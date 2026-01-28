"""
Pattern Detection Mixin for ContractVerifier.

Provides methods for detecting loop patterns (filter, map, nested, count, fold, find)
that enable automatic axiom generation for verification.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Set, Tuple, TYPE_CHECKING

from slop.parser import SList, Symbol, Number, is_form
from .z3_setup import z3

from .loop_patterns import (
    FilterPatternInfo, MapPatternInfo, NestedLoopPatternInfo, CountPatternInfo,
    FoldPatternInfo, FindPatternInfo, InnerLoopInfo, FieldSource,
)

if TYPE_CHECKING:
    from slop.parser import SExpr


class PatternDetectionMixin:
    """Mixin providing loop pattern detection methods."""

    def _is_mutable_binding(self, binding: SExpr) -> bool:
        """Check if a let binding is mutable: (mut var value)"""
        if isinstance(binding, SList) and len(binding) >= 2:
            first = binding[0]
            return isinstance(first, Symbol) and first.name == 'mut'
        return False

    def _is_empty_collection_init(self, expr: SExpr) -> bool:
        """Check if expression initializes an empty collection.

        Patterns:
        - (make-graph arena)
        - (make-list arena)
        - (list-new arena Type)
        - (record-new Type (field nil/empty) ...)
        """
        if isinstance(expr, SList) and len(expr) >= 1:
            head = expr[0]
            if isinstance(head, Symbol):
                # (make-X arena) pattern
                if head.name.startswith('make-'):
                    return True
                # (graph-empty arena) or similar
                if head.name.endswith('-empty'):
                    return True
                # (list-new arena Type) pattern
                if head.name == 'list-new':
                    return True
        return False

    def _is_conditional_set(self, expr: SExpr, result_var: str, loop_var: str) -> Optional[SExpr]:
        """Check if expr is (if predicate (set! result (add result item))) and return predicate.

        Also handles:
        - (when predicate (set! result ...))
        - (if predicate (set! result (add-X arena result item)))
        - (when predicate (list-push result item))
        """
        if is_form(expr, 'if') or is_form(expr, 'when'):
            if len(expr) >= 3:
                predicate = expr[1]
                then_branch = expr[2]

                # Check if then_branch is (set! result (add result item))
                if is_form(then_branch, 'set!') and len(then_branch) >= 3:
                    target = then_branch[1]
                    if isinstance(target, Symbol) and target.name == result_var:
                        return predicate

                # Check if then_branch is (list-push result item)
                if is_form(then_branch, 'list-push') and len(then_branch) >= 3:
                    target = then_branch[1]
                    if isinstance(target, Symbol) and target.name == result_var:
                        return predicate

        return None

    def _find_conditional_set_in_expr(self, expr: SExpr, result_var: str, loop_var: str) -> Optional[SExpr]:
        """Recursively search for conditional set pattern, traversing into let bindings.

        This handles patterns like:
        (let ((x ...))
          (let ((y ...))
            (if predicate (set! result ...))))
        """
        # First try direct match
        predicate = self._is_conditional_set(expr, result_var, loop_var)
        if predicate is not None:
            return predicate

        # Traverse into let bindings
        if is_form(expr, 'let') and len(expr) >= 3:
            # Check all body expressions in the let
            for body_expr in expr.items[2:]:
                predicate = self._find_conditional_set_in_expr(body_expr, result_var, loop_var)
                if predicate is not None:
                    return predicate

        # Traverse into do blocks
        if is_form(expr, 'do'):
            for body_expr in expr.items[1:]:
                predicate = self._find_conditional_set_in_expr(body_expr, result_var, loop_var)
                if predicate is not None:
                    return predicate

        return None

    def _detect_filter_pattern(self, body: SExpr) -> Optional[FilterPatternInfo]:
        """Detect filter loop pattern in function body.

        Pattern:
        (let ((mut result (make-X arena)))
          (for-each (item collection)
            (if predicate
              (set! result (add-X arena result item))))
          result)

        Returns FilterPatternInfo if detected, None otherwise.
        """
        # Must be a let expression
        if not is_form(body, 'let') or len(body) < 3:
            return None

        bindings = body[1]
        if not isinstance(bindings, SList):
            return None

        # Find mutable result binding
        result_var = None
        for binding in bindings.items:
            if self._is_mutable_binding(binding) and len(binding) >= 3:
                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                init_expr = binding[2]
                if var_name and self._is_empty_collection_init(init_expr):
                    result_var = var_name
                    break

        if not result_var:
            return None

        # Find for-each loop in body
        body_exprs = body.items[2:]
        for body_expr in body_exprs:
            if is_form(body_expr, 'for-each') and len(body_expr) >= 3:
                loop_binding = body_expr[1]
                if isinstance(loop_binding, SList) and len(loop_binding) >= 2:
                    loop_var = loop_binding[0].name if isinstance(loop_binding[0], Symbol) else None
                    collection = loop_binding[1]

                    if loop_var:
                        # Search loop body for (if predicate (set! result ...))
                        # Use recursive search to handle nested lets
                        loop_body = body_expr.items[2:]
                        for stmt in loop_body:
                            # Skip @loop-invariant
                            if is_form(stmt, '@loop-invariant'):
                                continue

                            # Use recursive search to find conditional set in nested lets
                            predicate = self._find_conditional_set_in_expr(stmt, result_var, loop_var)
                            if predicate is not None:
                                # Check if predicate is negated (exclusion filter)
                                is_negated = False
                                excluded_item = None

                                if is_form(predicate, 'not') and len(predicate) >= 2:
                                    inner = predicate[1]
                                    is_negated = True
                                    # Check for (not (eq item x)) pattern
                                    if isinstance(inner, SList) and len(inner) >= 3:
                                        inner_head = inner[0]
                                        if isinstance(inner_head, Symbol) and inner_head.name.endswith('-eq'):
                                            # Find which arg is the loop var
                                            arg1 = inner[1]
                                            arg2 = inner[2]
                                            if isinstance(arg1, Symbol) and arg1.name == loop_var:
                                                excluded_item = arg2
                                            elif isinstance(arg2, Symbol) and arg2.name == loop_var:
                                                excluded_item = arg1

                                return FilterPatternInfo(
                                    result_var=result_var,
                                    collection=collection,
                                    loop_var=loop_var,
                                    predicate=predicate,
                                    is_negated=is_negated,
                                    excluded_item=excluded_item
                                )

        return None

    def _detect_map_pattern(self, body: SExpr) -> Optional[MapPatternInfo]:
        """Detect map/transform loop pattern in function body.

        Map pattern (unconditional push with constructor):
        (let ((mut result (list-new arena Type)))
          (for-each (item collection)
            (list-push result (constructor-new arena ...)))
          result)

        Also detects conditional map patterns (filter-and-transform):
        (let ((mut result (list-new arena Type)))
          (for-each (item collection)
            (when condition
              (let ((x ...) (y ...))
                (list-push result (make-triple arena y pred x)))))
          result)

        Returns MapPatternInfo if detected, None otherwise.
        """
        # Must be a let expression
        if not is_form(body, 'let') or len(body) < 3:
            return None

        bindings = body[1]
        if not isinstance(bindings, SList):
            return None

        # Build initial bindings context from let bindings
        initial_bindings: Dict[str, SExpr] = {}
        for binding in bindings.items:
            if isinstance(binding, SList) and len(binding) >= 2:
                first = binding[0]
                if isinstance(first, Symbol):
                    if first.name == 'mut' and len(binding) >= 3:
                        # (mut var value)
                        var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                        var_value = binding[2]
                    else:
                        # (var value)
                        var_name = first.name
                        var_value = binding[1]
                    if var_name and var_value:
                        initial_bindings[var_name] = var_value

        # Find mutable result binding
        result_var = None
        for binding in bindings.items:
            if self._is_mutable_binding(binding) and len(binding) >= 3:
                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                init_expr = binding[2]
                if var_name and self._is_empty_collection_init(init_expr):
                    result_var = var_name
                    break

        if not result_var:
            return None

        # Find for-each loop in body
        body_exprs = body.items[2:]
        for body_expr in body_exprs:
            if is_form(body_expr, 'for-each') and len(body_expr) >= 3:
                loop_binding = body_expr[1]
                if isinstance(loop_binding, SList) and len(loop_binding) >= 2:
                    loop_var = loop_binding[0].name if isinstance(loop_binding[0], Symbol) else None
                    collection = loop_binding[1]

                    if loop_var:
                        loop_body = body_expr.items[2:]

                        # First try: UNCONDITIONAL push with constructor
                        push_info = self._find_unconditional_push_in_expr(
                            loop_body, result_var, loop_var
                        )
                        if push_info is not None:
                            constructor_expr, field_mappings = push_info
                            return MapPatternInfo(
                                result_var=result_var,
                                collection=collection,
                                loop_var=loop_var,
                                constructor_expr=constructor_expr,
                                field_mappings=field_mappings
                            )

                        # Second try: CONDITIONAL push with constructor (filter-and-transform)
                        cond_push_info = self._find_conditional_push_with_constructor(
                            loop_body, result_var, loop_var, initial_bindings
                        )
                        if cond_push_info is not None:
                            constructor_expr, field_mappings, predicate = cond_push_info
                            return MapPatternInfo(
                                result_var=result_var,
                                collection=collection,
                                loop_var=loop_var,
                                constructor_expr=constructor_expr,
                                field_mappings=field_mappings
                            )

        return None

    def _detect_nested_loop_pattern(self, body: SExpr) -> Optional[NestedLoopPatternInfo]:
        """Detect nested for-each loops with join semantics.

        Recognizes patterns where:
        1. Outer loop iterates over a collection
        2. Inner loop iterates over query result that depends on outer var
        3. Constructor in innermost body uses fields from both loops

        Example (eq-trans):
        (let ((same-as (make-iri arena OWL_SAME_AS))
              (mut result (list-new arena Triple)))
          (for-each (dt (. delta triples))
            (when (term-eq (triple-predicate dt) same-as)
              (let ((x (triple-subject dt))
                    (y (triple-object dt)))
                (let ((y-objects (indexed-graph-match arena g (some y) ...)))
                  (for-each (yo-triple y-objects)
                    (let ((z (triple-object yo-triple)))
                      (when inner-filter
                        (list-push result (make-triple arena x same-as z)))))))))
          result)

        Returns NestedLoopPatternInfo if detected, None otherwise.
        """
        # Must be a let expression
        if not is_form(body, 'let') or len(body) < 3:
            return None

        bindings = body[1]
        if not isinstance(bindings, SList):
            return None

        # Extract outer let bindings (constants and mutable result)
        outer_let_bindings: Dict[str, SExpr] = {}
        result_var = None

        for binding in bindings.items:
            if isinstance(binding, SList) and len(binding) >= 2:
                first = binding[0]
                if isinstance(first, Symbol):
                    if first.name == 'mut' and len(binding) >= 3:
                        # (mut var value)
                        var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                        var_value = binding[2]
                        if var_name and self._is_empty_collection_init(var_value):
                            result_var = var_name
                    else:
                        # (var value) - constant binding
                        var_name = first.name
                        var_value = binding[1]
                        if var_name and var_value:
                            outer_let_bindings[var_name] = var_value

        if not result_var:
            return None

        # Find outer for-each loop in body
        body_exprs = body.items[2:]
        for body_expr in body_exprs:
            if is_form(body_expr, 'for-each') and len(body_expr) >= 3:
                loop_binding = body_expr[1]
                if isinstance(loop_binding, SList) and len(loop_binding) >= 2:
                    outer_loop_var = loop_binding[0].name if isinstance(loop_binding[0], Symbol) else None
                    outer_collection = loop_binding[1]

                    if outer_loop_var:
                        # Process outer loop body to find nested structure
                        nested_result = self._process_nested_loop_body(
                            body_expr.items[2:],  # loop body
                            outer_loop_var,
                            outer_let_bindings.copy(),
                            result_var,
                            []  # no inner loops yet
                        )

                        if nested_result is not None:
                            (outer_filter, outer_bindings, inner_loops,
                             constructor_expr, field_mappings, all_bindings) = nested_result

                            # Classify field provenance
                            field_provenance = self._classify_field_provenance(
                                field_mappings,
                                outer_loop_var,
                                outer_bindings,
                                outer_let_bindings,
                                inner_loops
                            )

                            return NestedLoopPatternInfo(
                                result_var=result_var,
                                outer_collection=outer_collection,
                                outer_loop_var=outer_loop_var,
                                outer_filter=outer_filter,
                                outer_bindings=outer_bindings,
                                outer_let_bindings=outer_let_bindings,
                                inner_loops=inner_loops,
                                constructor_expr=constructor_expr,
                                field_mappings=field_mappings,
                                field_provenance=field_provenance
                            )

        return None

    def _process_nested_loop_body(
        self,
        stmts: List[SExpr],
        current_loop_var: str,
        bindings: Dict[str, SExpr],
        result_var: str,
        inner_loops: List[InnerLoopInfo],
        outer_filter: Optional[SExpr] = None
    ) -> Optional[Tuple[
        Optional[SExpr],        # outer_filter
        Dict[str, SExpr],       # outer_bindings (from let after outer filter)
        List[InnerLoopInfo],    # inner_loops
        SExpr,                  # constructor_expr
        Dict[str, SExpr],       # field_mappings
        Dict[str, SExpr]        # all_bindings (accumulated)
    ]]:
        """Recursively process loop body to find inner loops and push.

        Returns None if no nested pattern found, otherwise returns tuple of
        (outer_filter, outer_bindings, inner_loops, constructor, field_mappings, all_bindings).

        The outer_filter parameter accumulates filter conditions encountered BEFORE
        any inner for-each loop is found.
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Handle (when filter body) - this is a filter condition
            if is_form(stmt, 'when') and len(stmt) >= 3:
                filter_cond = stmt[1]
                then_body = stmt[2]

                # If we haven't found an inner loop yet, this is an outer filter
                # Pass it along to be returned when we find the final structure
                current_outer_filter = filter_cond if not inner_loops else outer_filter

                # Recurse into then_body
                result = self._process_nested_loop_body(
                    [then_body], current_loop_var, bindings.copy(), result_var,
                    inner_loops, current_outer_filter
                )
                if result is not None:
                    return result
                continue

            # Handle (let ((bindings)) body)
            if is_form(stmt, 'let') and len(stmt) >= 3:
                let_bindings = stmt[1]
                new_bindings = bindings.copy()

                # Extract bindings
                if isinstance(let_bindings, SList):
                    for binding in let_bindings.items:
                        if isinstance(binding, SList) and len(binding) >= 2:
                            var_name = None
                            var_value = None
                            if isinstance(binding[0], Symbol):
                                if binding[0].name == 'mut' and len(binding) >= 3:
                                    var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                                    var_value = binding[2]
                                else:
                                    var_name = binding[0].name
                                    var_value = binding[1]
                            if var_name and var_value:
                                new_bindings[var_name] = var_value

                # Recurse into let body with expanded bindings
                result = self._process_nested_loop_body(
                    stmt.items[2:], current_loop_var, new_bindings, result_var,
                    inner_loops, outer_filter
                )
                if result is not None:
                    return result
                continue

            # Handle nested (for-each (var collection) body) - THE KEY PART
            if is_form(stmt, 'for-each') and len(stmt) >= 3:
                inner_binding = stmt[1]
                if isinstance(inner_binding, SList) and len(inner_binding) >= 2:
                    inner_var = inner_binding[0].name if isinstance(inner_binding[0], Symbol) else None
                    inner_collection = inner_binding[1]

                    if inner_var:
                        # Check if inner collection references outer variables (join!)
                        # Resolve through bindings to find the actual referenced vars
                        join_vars = self._find_join_vars_deep(inner_collection, bindings)

                        inner_loop_info = InnerLoopInfo(
                            collection=inner_collection,
                            loop_var=inner_var,
                            filter=None,
                            bindings={},
                            join_vars=join_vars
                        )

                        # Recurse into inner loop body with new loop var
                        new_inner_loops = inner_loops + [inner_loop_info]
                        result = self._process_nested_loop_body(
                            stmt.items[2:], inner_var, bindings.copy(), result_var,
                            new_inner_loops, outer_filter
                        )
                        if result is not None:
                            # Return with the accumulated outer_filter
                            (_, found_bindings, final_inner_loops,
                             constructor, field_mappings, all_bindings) = result
                            return (outer_filter, bindings, final_inner_loops,
                                    constructor, field_mappings, all_bindings)
                continue

            # Handle (list-push result (constructor ...))
            if is_form(stmt, 'list-push') and len(stmt) >= 3:
                target = stmt[1]
                pushed_expr = stmt[2]
                if isinstance(target, Symbol) and target.name == result_var:
                    # Resolve constructor if it's a variable
                    resolved_constructor = pushed_expr
                    if isinstance(pushed_expr, Symbol) and pushed_expr.name in bindings:
                        resolved_constructor = bindings[pushed_expr.name]

                    if isinstance(resolved_constructor, SList) and len(resolved_constructor) >= 1:
                        field_mappings = self._extract_field_mappings_with_context(
                            resolved_constructor, current_loop_var, bindings
                        )
                        if field_mappings:
                            return (outer_filter, bindings, inner_loops, resolved_constructor,
                                    field_mappings, bindings)

        return None

    def _find_join_vars_deep(
        self, expr: SExpr, bindings: Dict[str, SExpr]
    ) -> Set[str]:
        """Find variables from bindings that are transitively referenced in expr.

        For inner collection expressions like:
        - 'matches' where matches = (query-by-subject g y) and y is in bindings
        - (graph-match g y) where y is in bindings

        Returns the set of binding names that are used (transitively) in the expression.
        """
        referenced: Set[str] = set()

        def collect_refs(e: SExpr, seen: Set[str]):
            if isinstance(e, Symbol):
                var_name = e.name
                if var_name in bindings and var_name not in seen:
                    referenced.add(var_name)
                    # Also check what this binding references
                    seen.add(var_name)
                    collect_refs(bindings[var_name], seen)
            elif isinstance(e, SList):
                for item in e.items:
                    collect_refs(item, seen)

        collect_refs(expr, set())
        return referenced

    def _find_referenced_vars_set(
        self, expr: SExpr, known_vars: Dict[str, SExpr]
    ) -> Set[str]:
        """Find which known variables are referenced in an expression.

        For detecting join patterns: which outer scope variables are used
        in an inner loop's collection expression.
        """
        referenced: Set[str] = set()

        def collect_refs(e: SExpr):
            if isinstance(e, Symbol):
                if e.name in known_vars:
                    referenced.add(e.name)
            elif isinstance(e, SList):
                for item in e.items:
                    collect_refs(item)

        collect_refs(expr)
        return referenced

    def _classify_field_provenance(
        self,
        field_mappings: Dict[str, SExpr],
        outer_loop_var: str,
        outer_bindings: Dict[str, SExpr],
        outer_let_bindings: Dict[str, SExpr],
        inner_loops: List[InnerLoopInfo]
    ) -> Dict[str, str]:
        """Classify the source of each constructor field.

        For (make-triple arena x same-as z):
        - x → resolves to (triple-subject dt) → OUTER
        - same-as → constant from outer let → CONSTANT
        - z → resolves to (triple-object yo-triple) → INNER

        Returns dict mapping field name to FieldSource value.
        """
        provenance: Dict[str, str] = {}

        # Collect all inner loop variables
        inner_loop_vars = {loop.loop_var for loop in inner_loops}

        for field_name, field_expr in field_mappings.items():
            source = self._determine_field_source(
                field_expr,
                outer_loop_var,
                outer_bindings,
                outer_let_bindings,
                inner_loop_vars
            )
            provenance[field_name] = source

        return provenance

    def _determine_field_source(
        self,
        expr: SExpr,
        outer_loop_var: str,
        outer_bindings: Dict[str, SExpr],
        outer_let_bindings: Dict[str, SExpr],
        inner_loop_vars: Set[str]
    ) -> str:
        """Determine the source classification for a single field expression."""
        # Check if it's a constant from outer let
        if isinstance(expr, Symbol):
            if expr.name in outer_let_bindings:
                return FieldSource.CONSTANT
            # Check if it's an outer binding that derives from outer loop var
            if expr.name in outer_bindings:
                resolved = outer_bindings[expr.name]
                return self._determine_field_source(
                    resolved, outer_loop_var, outer_bindings, outer_let_bindings, inner_loop_vars
                )

        # Check if expression references outer loop var directly
        refs_outer = self._references_var(expr, outer_loop_var)

        # Check if expression references any inner loop var
        refs_inner = any(
            self._references_var(expr, inner_var)
            for inner_var in inner_loop_vars
        )

        if refs_outer and refs_inner:
            return FieldSource.MIXED
        elif refs_inner:
            return FieldSource.INNER
        elif refs_outer:
            return FieldSource.OUTER
        else:
            # No loop var reference - likely a constant
            return FieldSource.CONSTANT

    def _find_unconditional_push_in_expr(
        self, stmts: List[SExpr], result_var: str, loop_var: str
    ) -> Optional[Tuple[SExpr, Dict[str, SExpr]]]:
        """Find unconditional list-push with constructor in loop body.

        Returns (constructor_expr, field_mappings) if found.

        Patterns recognized:
        - Direct: (list-push result (constructor ...))
        - In let: (let (...) ... (list-push result (constructor ...)))
        - In do: (do ... (list-push result (constructor ...)))

        Does NOT match conditional pushes (when/if), as those are filter patterns.
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Check for unconditional (list-push result (constructor ...))
            if is_form(stmt, 'list-push') and len(stmt) >= 3:
                target = stmt[1]
                pushed_expr = stmt[2]
                if isinstance(target, Symbol) and target.name == result_var:
                    # Check if pushed expr is a constructor call
                    if isinstance(pushed_expr, SList) and len(pushed_expr) >= 1:
                        field_mappings = self._extract_field_mappings(
                            pushed_expr, loop_var
                        )
                        if field_mappings:
                            return (pushed_expr, field_mappings)

            # Recurse into let bindings (but NOT conditionals)
            if is_form(stmt, 'let') and len(stmt) >= 3:
                nested_result = self._find_unconditional_push_in_expr(
                    stmt.items[2:], result_var, loop_var
                )
                if nested_result is not None:
                    return nested_result

            # Recurse into do blocks
            if is_form(stmt, 'do'):
                nested_result = self._find_unconditional_push_in_expr(
                    stmt.items[1:], result_var, loop_var
                )
                if nested_result is not None:
                    return nested_result

            # Skip conditionals - those are filter patterns, not map patterns
            # (if ...) and (when ...) are handled by _detect_filter_pattern

        return None

    def _find_conditional_push_with_constructor(
        self, stmts: List[SExpr], result_var: str, loop_var: str,
        bindings_context: Dict[str, SExpr]
    ) -> Optional[Tuple[SExpr, Dict[str, SExpr], SExpr]]:
        """Find conditional list-push with constructor (filter-and-transform pattern).

        Returns (constructor_expr, field_mappings, predicate) if found.

        This handles patterns like:
        (when condition
          (let ((x (accessor loop_var)) ...)
            (when condition2
              (list-push result (make-triple arena y same-as x)))))

        The bindings_context maps variable names to their definitions, allowing
        us to trace variables back to their source expressions.
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Handle (when condition body) or (if condition body)
            if (is_form(stmt, 'when') or is_form(stmt, 'if')) and len(stmt) >= 3:
                predicate = stmt[1]
                then_body = stmt[2]

                # Check if then_body directly contains list-push with constructor
                push_result = self._check_push_with_constructor(
                    then_body, result_var, loop_var, bindings_context
                )
                if push_result is not None:
                    constructor_expr, field_mappings = push_result
                    return (constructor_expr, field_mappings, predicate)

                # Recurse into then_body (may have nested let/when)
                nested_result = self._find_conditional_push_with_constructor(
                    [then_body], result_var, loop_var, bindings_context
                )
                if nested_result is not None:
                    # Combine predicates: outer AND inner
                    inner_constructor, inner_mappings, inner_pred = nested_result
                    return (inner_constructor, inner_mappings, predicate)

            # Handle let bindings - add to context and recurse
            if is_form(stmt, 'let') and len(stmt) >= 3:
                let_bindings = stmt[1]
                new_context = bindings_context.copy()

                # Extract bindings
                if isinstance(let_bindings, SList):
                    for binding in let_bindings.items:
                        if isinstance(binding, SList) and len(binding) >= 2:
                            var_name = None
                            var_value = None
                            # Handle (var value) or (mut var value)
                            if isinstance(binding[0], Symbol):
                                if binding[0].name == 'mut' and len(binding) >= 3:
                                    var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                                    var_value = binding[2]
                                else:
                                    var_name = binding[0].name
                                    var_value = binding[1]
                            if var_name and var_value:
                                new_context[var_name] = var_value

                # Recurse into let body with expanded context
                nested_result = self._find_conditional_push_with_constructor(
                    stmt.items[2:], result_var, loop_var, new_context
                )
                if nested_result is not None:
                    return nested_result

        return None

    def _check_push_with_constructor(
        self, expr: SExpr, result_var: str, loop_var: str,
        bindings_context: Dict[str, SExpr]
    ) -> Optional[Tuple[SExpr, Dict[str, SExpr]]]:
        """Check if expr is (list-push result (constructor ...)) and extract field mappings.

        Uses bindings_context to resolve variable references to their source expressions.
        Handles both direct constructor calls and variable references to constructors:
        - (list-push result (make-triple arena y pred x))
        - (list-push result inferred) where inferred = (make-triple ...)
        """
        if not is_form(expr, 'list-push') or len(expr) < 3:
            return None

        target = expr[1]
        pushed_expr = expr[2]

        if not isinstance(target, Symbol) or target.name != result_var:
            return None

        # Resolve pushed_expr if it's a variable reference
        resolved_pushed = pushed_expr
        if isinstance(pushed_expr, Symbol) and pushed_expr.name in bindings_context:
            resolved_pushed = bindings_context[pushed_expr.name]

        if not isinstance(resolved_pushed, SList) or len(resolved_pushed) < 1:
            return None

        # Extract field mappings, resolving variables through bindings_context
        field_mappings = self._extract_field_mappings_with_context(
            resolved_pushed, loop_var, bindings_context
        )
        if field_mappings:
            return (resolved_pushed, field_mappings)

        return None

    def _extract_field_mappings_with_context(
        self, constructor: SExpr, loop_var: str,
        bindings_context: Dict[str, SExpr]
    ) -> Dict[str, SExpr]:
        """Extract field mappings from constructor, resolving variables through context.

        For (make-triple arena y same-as x) where:
            x = (triple-subject dt)
            y = (triple-object dt)
            same-as = (make-iri arena OWL_SAME_AS)

        Returns: {
            'subject': (triple-object dt),   # resolved from y
            'predicate': same-as (or resolved expr),
            'object': (triple-subject dt)    # resolved from x
        }

        Note: make-triple uses RDF order (arena, subject, predicate, object)
        """
        if not isinstance(constructor, SList) or len(constructor) < 1:
            return {}

        head = constructor[0]
        if not isinstance(head, Symbol):
            return {}

        head_name = head.name
        mappings: Dict[str, SExpr] = {}

        # Handle make-triple: (make-triple arena subj pred obj)
        # Note: Different from triple-new! Uses RDF order.
        if head_name == 'make-triple' and len(constructor) >= 5:
            # Args: arena, subject, predicate, object
            subj_arg = constructor[2]
            pred_arg = constructor[3]
            obj_arg = constructor[4]

            # Resolve through bindings context
            mappings['subject'] = self._resolve_through_context(subj_arg, bindings_context)
            mappings['predicate'] = self._resolve_through_context(pred_arg, bindings_context)
            mappings['object'] = self._resolve_through_context(obj_arg, bindings_context)
            return mappings

        # Fall back to regular extraction if not make-triple
        return self._extract_field_mappings(constructor, loop_var)

    def _resolve_through_context(
        self, expr: SExpr, bindings_context: Dict[str, SExpr]
    ) -> SExpr:
        """Resolve a variable through the bindings context to its source expression.

        If expr is a Symbol that exists in bindings_context, return its definition.
        Otherwise return expr unchanged.
        """
        if isinstance(expr, Symbol) and expr.name in bindings_context:
            return bindings_context[expr.name]
        return expr

    def _extract_field_mappings(
        self, constructor: SExpr, loop_var: str
    ) -> Dict[str, SExpr]:
        """Extract field -> source_expr mappings from a constructor call.

        For (triple-new arena (triple-predicate dt) (triple-object dt) (triple-subject dt)):
        Returns: {
            'predicate': (triple-predicate dt),
            'subject': (triple-object dt),   # Note: swapped positions
            'object': (triple-subject dt)    # Note: swapped positions
        }

        For (record-new Type (field1 expr1) (field2 expr2) ...):
        Returns: {'field1': expr1, 'field2': expr2, ...}

        Returns empty dict if pattern is not recognized.
        """
        if not isinstance(constructor, SList) or len(constructor) < 1:
            return {}

        head = constructor[0]
        if not isinstance(head, Symbol):
            return {}

        head_name = head.name
        mappings: Dict[str, SExpr] = {}

        # Handle triple-new: (triple-new arena pred subj obj)
        # Known positional constructor for Triple type
        if head_name == 'triple-new' and len(constructor) >= 5:
            # Args: arena, predicate, subject, object
            mappings['predicate'] = constructor[2]
            mappings['subject'] = constructor[3]
            mappings['object'] = constructor[4]
            return mappings

        # Handle make-triple: (make-triple arena subj pred obj)
        # Note: Different argument order from triple-new!
        # make-triple follows RDF convention: (subject, predicate, object)
        if head_name == 'make-triple' and len(constructor) >= 5:
            # Args: arena, subject, predicate, object
            mappings['subject'] = constructor[2]
            mappings['predicate'] = constructor[3]
            mappings['object'] = constructor[4]
            return mappings

        # Handle record-new: (record-new Type (field1 val1) (field2 val2) ...)
        # Must be checked BEFORE generic -new suffix to avoid matching positional pattern
        if head_name == 'record-new' and len(constructor) >= 3:
            # Skip type name at position 1
            for i, field_binding in enumerate(constructor.items[2:]):
                if isinstance(field_binding, SList) and len(field_binding) >= 2:
                    field_name = field_binding[0]
                    field_value = field_binding[1]
                    if isinstance(field_name, Symbol):
                        mappings[field_name.name] = field_value
            if mappings:
                return mappings

        # Handle struct-new: (struct-new Type (field1 val1) ...)
        # Must be checked BEFORE generic -new suffix
        if head_name == 'struct-new' and len(constructor) >= 3:
            for field_binding in constructor.items[2:]:
                if isinstance(field_binding, SList) and len(field_binding) >= 2:
                    field_name = field_binding[0]
                    field_value = field_binding[1]
                    if isinstance(field_name, Symbol):
                        mappings[field_name.name] = field_value
            if mappings:
                return mappings

        # Handle Type-new: (Type-new arena field1 field2 ...)
        # Generic positional constructor pattern (after specific patterns)
        if head_name.endswith('-new'):
            type_name = head_name[:-4]  # Remove '-new' suffix
            # Return positional mappings with numeric keys
            for i, arg in enumerate(constructor.items[2:]):  # Skip constructor name and arena
                mappings[f'field_{i}'] = arg
            if mappings:
                return mappings

        # General fallback: any constructor-like call with arguments
        # Map positional arguments to field_0, field_1, etc.
        if len(constructor) >= 2:
            # Check if any argument references the loop variable
            has_loop_var_ref = False
            for arg in constructor.items[1:]:
                if self._references_var(arg, loop_var):
                    has_loop_var_ref = True
                    break

            if has_loop_var_ref:
                for i, arg in enumerate(constructor.items[1:]):
                    # Skip arena argument if it's the first
                    if i == 0 and isinstance(arg, Symbol) and arg.name == 'arena':
                        continue
                    mappings[f'arg_{i}'] = arg

        return mappings

    def _references_var(self, expr: SExpr, var_name: str) -> bool:
        """Check if expression references a variable."""
        if isinstance(expr, Symbol):
            return expr.name == var_name
        if isinstance(expr, SList):
            for item in expr.items:
                if self._references_var(item, var_name):
                    return True
        return False

    def _generate_filter_axioms(self, pattern: FilterPatternInfo,
                                translator: Z3Translator) -> List:
        """Generate Z3 axioms for detected filter pattern.

        Axioms:
        1. Size constraint: (size result) <= (size source) where source is the parent object
        2. Exclusion constraint: If predicate is (not (eq item x)), then (not (contains result x))
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # Translate the collection
        collection_z3 = translator.translate_expr(pattern.collection)
        if collection_z3 is None:
            return axioms

        # Axiom 1: Size constraint - result size <= source size
        # If collection is (. obj field), compare to obj's size, not field's size
        # This matches postconditions like (graph-size $result) <= (graph-size g)
        source_obj = None
        if is_form(pattern.collection, '.') and len(pattern.collection) >= 2:
            # Collection is (. obj field) - use obj as the source for size comparison
            source_obj = translator.translate_expr(pattern.collection[1])

        if source_obj is not None:
            # Use the source object for size comparison
            # Try common size accessor patterns
            size_func_name = "field_size"
            if size_func_name not in translator.variables:
                size_func = z3.Function(size_func_name, z3.IntSort(), z3.IntSort())
                translator.variables[size_func_name] = size_func
            else:
                size_func = translator.variables[size_func_name]

            result_size = size_func(result_var)
            source_size = size_func(source_obj)
            axioms.append(result_size <= source_size)
            axioms.append(result_size >= 0)
        else:
            # Fallback: compare to collection size directly
            size_func_name = "field_size"
            if size_func_name not in translator.variables:
                size_func = z3.Function(size_func_name, z3.IntSort(), z3.IntSort())
                translator.variables[size_func_name] = size_func
            else:
                size_func = translator.variables[size_func_name]

            result_size = size_func(result_var)
            collection_size = size_func(collection_z3)
            axioms.append(result_size <= collection_size)
            axioms.append(result_size >= 0)

        # Axiom 2: Exclusion constraint for (not (eq item x)) patterns
        if pattern.is_negated and pattern.excluded_item is not None:
            excluded_z3 = translator.translate_expr(pattern.excluded_item)
            if excluded_z3 is not None:
                # Get or create contains predicate function
                contains_func_name = "fn_graph-contains_2"  # 2-arity contains
                if contains_func_name not in translator.variables:
                    contains_func = z3.Function(contains_func_name, z3.IntSort(), z3.IntSort(), z3.BoolSort())
                    translator.variables[contains_func_name] = contains_func
                else:
                    contains_func = translator.variables[contains_func_name]

                # The excluded item is NOT in the result
                axioms.append(z3.Not(contains_func(result_var, excluded_z3)))

        return axioms

    def _detect_count_pattern(self, body: SExpr) -> Optional[CountPatternInfo]:
        """Detect count loop pattern in function body.

        Pattern:
        (let ((mut count 0))
          (for-each (item collection)
            (if predicate
              (set! count (+ count 1))))
          count)

        Returns CountPatternInfo if detected, None otherwise.
        """
        # Must be a let expression
        if not is_form(body, 'let') or len(body) < 3:
            return None

        bindings = body[1]
        if not isinstance(bindings, SList):
            return None

        # Find mutable count binding initialized to 0
        count_var = None
        for binding in bindings.items:
            if self._is_mutable_binding(binding) and len(binding) >= 3:
                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                init_expr = binding[2]
                # Check if initialized to 0
                if var_name and isinstance(init_expr, Number) and init_expr.value == 0:
                    count_var = var_name
                    break

        if not count_var:
            return None

        # Find for-each loop in body
        body_exprs = body.items[2:]
        for body_expr in body_exprs:
            if is_form(body_expr, 'for-each') and len(body_expr) >= 3:
                loop_binding = body_expr[1]
                if isinstance(loop_binding, SList) and len(loop_binding) >= 2:
                    loop_var = loop_binding[0].name if isinstance(loop_binding[0], Symbol) else None
                    collection = loop_binding[1]

                    if loop_var:
                        # Search loop body for (if predicate (set! count (+ count 1)))
                        loop_body = body_expr.items[2:]
                        predicate = self._find_count_increment_predicate(loop_body, count_var)
                        if predicate is not None:
                            return CountPatternInfo(
                                count_var=count_var,
                                collection=collection,
                                loop_var=loop_var,
                                predicate=predicate
                            )

        return None

    def _find_count_increment_predicate(self, stmts: List[SExpr], count_var: str) -> Optional[SExpr]:
        """Find the predicate in a count increment pattern.

        Looks for patterns like:
        - (if predicate (set! count (+ count 1)))
        - (when predicate (set! count (+ count 1)))
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Check for if/when with count increment
            if (is_form(stmt, 'if') or is_form(stmt, 'when')) and len(stmt) >= 3:
                predicate = stmt[1]
                then_branch = stmt[2]

                # Check if then branch is (set! count (+ count 1))
                if self._is_count_increment(then_branch, count_var):
                    return predicate

            # Recurse into nested let
            if is_form(stmt, 'let') and len(stmt) >= 3:
                nested_result = self._find_count_increment_predicate(stmt.items[2:], count_var)
                if nested_result is not None:
                    return nested_result

        return None

    def _is_count_increment(self, expr: SExpr, count_var: str) -> bool:
        """Check if expression is (set! count (+ count 1))."""
        if not is_form(expr, 'set!') or len(expr) < 3:
            return False

        target = expr[1]
        if not isinstance(target, Symbol) or target.name != count_var:
            return False

        value = expr[2]
        if not is_form(value, '+') or len(value) < 3:
            return False

        # Check for (+ count 1) or (+ 1 count)
        arg1 = value[1]
        arg2 = value[2]

        if isinstance(arg1, Symbol) and arg1.name == count_var:
            if isinstance(arg2, Number) and arg2.value == 1:
                return True
        if isinstance(arg2, Symbol) and arg2.name == count_var:
            if isinstance(arg1, Number) and arg1.value == 1:
                return True

        return False

    def _generate_count_axioms(self, pattern: CountPatternInfo,
                               translator: Z3Translator) -> List:
        """Generate Z3 axioms for detected count pattern.

        Axioms:
        1. Count is non-negative: $result >= 0
        2. Count is bounded by collection size: $result <= (list-len collection)
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # Only add numeric axioms if result is an integer type
        if result_var.sort() != z3.IntSort():
            return axioms

        # Axiom 1: Count is non-negative
        axioms.append(result_var >= 0)

        # Axiom 2: Count is bounded by collection size
        # Translate the collection to get its Z3 representation
        collection_z3 = translator.translate_expr(pattern.collection)
        if collection_z3 is not None:
            # Get or create list-len function
            list_len_func_name = "fn_list-len_1"
            if list_len_func_name not in translator.variables:
                list_len_func = z3.Function(list_len_func_name, z3.IntSort(), z3.IntSort())
                translator.variables[list_len_func_name] = list_len_func
            else:
                list_len_func = translator.variables[list_len_func_name]

            collection_len = list_len_func(collection_z3)
            axioms.append(result_var <= collection_len)

        return axioms

    def _detect_fold_pattern(self, body: SExpr) -> Optional[FoldPatternInfo]:
        """Detect fold/accumulation loop pattern in function body.

        Pattern:
        (let ((mut acc init))
          (for-each (item collection)
            (set! acc (op acc item)))
          acc)

        Returns FoldPatternInfo if detected, None otherwise.
        """
        # Must be a let expression
        if not is_form(body, 'let') or len(body) < 3:
            return None

        bindings = body[1]
        if not isinstance(bindings, SList):
            return None

        # Find mutable accumulator binding
        acc_var = None
        init_value = None
        for binding in bindings.items:
            if self._is_mutable_binding(binding) and len(binding) >= 3:
                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                init_expr = binding[2]
                # Accept numeric or simple initializers (not empty collection inits)
                if var_name and not self._is_empty_collection_init(init_expr):
                    acc_var = var_name
                    init_value = init_expr
                    break

        if not acc_var or init_value is None:
            return None

        # Find for-each loop in body
        body_exprs = body.items[2:]
        for body_expr in body_exprs:
            if is_form(body_expr, 'for-each') and len(body_expr) >= 3:
                loop_binding = body_expr[1]
                if isinstance(loop_binding, SList) and len(loop_binding) >= 2:
                    loop_var = loop_binding[0].name if isinstance(loop_binding[0], Symbol) else None
                    collection = loop_binding[1]

                    if loop_var:
                        # Search loop body for (set! acc (op acc item))
                        loop_body = body_expr.items[2:]
                        operator = self._find_accumulator_operator(loop_body, acc_var, loop_var)
                        if operator is not None:
                            return FoldPatternInfo(
                                acc_var=acc_var,
                                init_value=init_value,
                                collection=collection,
                                loop_var=loop_var,
                                operator=operator
                            )

        return None

    def _find_accumulator_operator(self, stmts: List[SExpr], acc_var: str, loop_var: str) -> Optional[str]:
        """Find the operator in a fold/accumulation pattern.

        Looks for patterns like:
        - (set! acc (+ acc item))
        - (set! acc (* acc item))
        - (set! acc (max acc item))
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Check for (set! acc (op acc item))
            if is_form(stmt, 'set!') and len(stmt) >= 3:
                target = stmt[1]
                if isinstance(target, Symbol) and target.name == acc_var:
                    value = stmt[2]
                    if isinstance(value, SList) and len(value) >= 3:
                        op = value[0]
                        if isinstance(op, Symbol):
                            # Check if it involves acc and loop_var
                            arg1 = value[1]
                            arg2 = value[2]
                            uses_acc = (isinstance(arg1, Symbol) and arg1.name == acc_var) or \
                                       (isinstance(arg2, Symbol) and arg2.name == acc_var)
                            uses_loop = (isinstance(arg1, Symbol) and arg1.name == loop_var) or \
                                        (isinstance(arg2, Symbol) and arg2.name == loop_var)
                            if uses_acc and uses_loop:
                                return op.name

            # Check for conditional accumulation (if pred (set! acc ...))
            if (is_form(stmt, 'if') or is_form(stmt, 'when')) and len(stmt) >= 3:
                then_branch = stmt[2]
                result = self._find_accumulator_operator([then_branch], acc_var, loop_var)
                if result is not None:
                    return result

            # Recurse into nested let
            if is_form(stmt, 'let') and len(stmt) >= 3:
                nested_result = self._find_accumulator_operator(stmt.items[2:], acc_var, loop_var)
                if nested_result is not None:
                    return nested_result

        return None

    def _generate_fold_axioms(self, pattern: FoldPatternInfo,
                              translator: Z3Translator) -> List:
        """Generate Z3 axioms for detected fold pattern.

        Axioms depend on the operator:
        - For '+': If init >= 0 and items non-negative, result >= init
        - For '*': Special handling for multiplication
        - For 'max'/'min': Result bounded by init and collection
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # Translate initial value
        init_z3 = translator.translate_expr(pattern.init_value)

        op = pattern.operator
        if op == '+':
            # For addition starting at 0, result is non-negative if items are
            if isinstance(pattern.init_value, Number) and pattern.init_value.value == 0:
                # Common case: sum starting at 0, items assumed non-negative
                # We can't prove this without knowing item signs, so just add non-negative constraint
                # if init is 0 (most common for sums)
                pass
            # For any + accumulator, result >= init if items are non-negative
            # This is a heuristic - we add it when init is a known value
            if init_z3 is not None:
                # Add axiom: result >= init (for non-negative items)
                # This is sound for counting/summing positive values
                pass

        elif op == 'max':
            # For max, result >= init
            if init_z3 is not None:
                axioms.append(result_var >= init_z3)

        elif op == 'min':
            # For min, result <= init
            if init_z3 is not None:
                axioms.append(result_var <= init_z3)

        return axioms

    def _detect_find_pattern(self, body: SExpr) -> Optional[FindPatternInfo]:
        """Detect find-first loop pattern in function body.

        Pattern:
        (let ((mut found nil))
          (for-each (item collection)
            (if (and (== found nil) predicate)
              (set! found item)))
          found)

        Returns FindPatternInfo if detected, None otherwise.
        """
        # Must be a let expression
        if not is_form(body, 'let') or len(body) < 3:
            return None

        bindings = body[1]
        if not isinstance(bindings, SList):
            return None

        # Find mutable result binding initialized to nil
        result_var = None
        for binding in bindings.items:
            if self._is_mutable_binding(binding) and len(binding) >= 3:
                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                init_expr = binding[2]
                # Check if initialized to nil
                if var_name and isinstance(init_expr, Symbol) and init_expr.name == 'nil':
                    result_var = var_name
                    break

        if not result_var:
            return None

        # Find for-each loop in body
        body_exprs = body.items[2:]
        for body_expr in body_exprs:
            if is_form(body_expr, 'for-each') and len(body_expr) >= 3:
                loop_binding = body_expr[1]
                if isinstance(loop_binding, SList) and len(loop_binding) >= 2:
                    loop_var = loop_binding[0].name if isinstance(loop_binding[0], Symbol) else None
                    collection = loop_binding[1]

                    if loop_var:
                        # Search loop body for find-first pattern
                        loop_body = body_expr.items[2:]
                        predicate = self._find_first_predicate(loop_body, result_var, loop_var)
                        if predicate is not None:
                            return FindPatternInfo(
                                result_var=result_var,
                                collection=collection,
                                loop_var=loop_var,
                                predicate=predicate
                            )

        return None

    def _find_first_predicate(self, stmts: List[SExpr], result_var: str, loop_var: str) -> Optional[SExpr]:
        """Find the predicate in a find-first pattern.

        Looks for patterns like:
        - (if (and (== found nil) predicate) (set! found item))
        - (when (and (== found nil) predicate) (set! found item))
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Check for if/when with find-first pattern
            if (is_form(stmt, 'if') or is_form(stmt, 'when')) and len(stmt) >= 3:
                condition = stmt[1]
                then_branch = stmt[2]

                # Check if condition is (and (== found nil) predicate)
                if is_form(condition, 'and') and len(condition) >= 3:
                    nil_check = condition[1]
                    predicate = condition[2]

                    # Check if nil_check is (== result_var nil)
                    is_nil_check = False
                    if is_form(nil_check, '==') and len(nil_check) >= 3:
                        arg1 = nil_check[1]
                        arg2 = nil_check[2]
                        if (isinstance(arg1, Symbol) and arg1.name == result_var and
                            isinstance(arg2, Symbol) and arg2.name == 'nil'):
                            is_nil_check = True
                        elif (isinstance(arg2, Symbol) and arg2.name == result_var and
                              isinstance(arg1, Symbol) and arg1.name == 'nil'):
                            is_nil_check = True

                    # Check if then_branch sets result to loop_var
                    if is_nil_check and is_form(then_branch, 'set!') and len(then_branch) >= 3:
                        target = then_branch[1]
                        value = then_branch[2]
                        if (isinstance(target, Symbol) and target.name == result_var and
                            isinstance(value, Symbol) and value.name == loop_var):
                            return predicate

            # Recurse into nested let
            if is_form(stmt, 'let') and len(stmt) >= 3:
                nested_result = self._find_first_predicate(stmt.items[2:], result_var, loop_var)
                if nested_result is not None:
                    return nested_result

        return None

    def _has_for_each(self, expr: SExpr) -> bool:
        """Check if expression contains a for-each loop"""
        if is_form(expr, 'for-each'):
            return True
        if isinstance(expr, SList):
            for item in expr.items:
                if self._has_for_each(item):
                    return True
        return False


__all__ = ['PatternDetectionMixin']
