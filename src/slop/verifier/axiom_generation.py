"""
Axiom Generation Mixin for ContractVerifier.

Provides methods for generating Z3 axioms from loop patterns, record constructors,
list operations, and other SLOP constructs to enable verification.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Set, Tuple, TYPE_CHECKING

from slop.parser import SList, Symbol, String, Number, is_form
from slop.types import RecordType, RangeType

from .z3_setup import Z3_AVAILABLE, z3
from .loop_patterns import (
    FilterPatternInfo, MapPatternInfo, NestedLoopPatternInfo, CountPatternInfo,
    FoldPatternInfo, InnerLoopInfo, FieldSource,
)

if TYPE_CHECKING:
    from slop.parser import SExpr
    from .translator import Z3Translator
    from .types import FunctionSignature


class AxiomGenerationMixin:
    """Mixin providing axiom generation methods."""

    def _extract_seq_push_axioms(self, fn_body: SExpr, postconditions: List[SExpr],
                                  translator: 'Z3Translator') -> List[z3.BoolRef]:
        """Generate axioms connecting pushed elements to their source.

        For filter patterns like:
            (let ((mut result (list-new ...)))
              (for-each (t items)
                (when (pred t)
                  (list-push result t)))
              result)

        Generates axiom:
            ForAll i: 0 <= i < Length($result) =>
                Exists j: 0 <= j < Length(items) &&
                          $result[i] == items[j] && pred(items[j])

        This enables proving postconditions like:
            (forall (t $result) (pred t))
        """
        axioms: List[z3.BoolRef] = []

        # Find filter patterns
        filter_pattern = self._detect_filter_pattern(fn_body)
        if filter_pattern is None:
            return axioms

        # Need Seq for $result
        if '$result' not in translator.list_seqs:
            return axioms

        result_seq = translator.list_seqs['$result']

        # Get or create Seq for source collection
        if isinstance(filter_pattern.collection, Symbol):
            source_name = filter_pattern.collection.name
            if source_name not in translator.list_seqs:
                # Create Seq for the source collection
                translator._create_list_seq(source_name)
            source_seq = translator.list_seqs.get(source_name)
        else:
            return axioms

        if source_seq is None:
            return axioms

        # Create index variables for the quantified formula
        result_idx = z3.Int('_push_res_i')
        source_idx = z3.Int('_push_src_j')

        # Translate the predicate with loop variable bound to source element
        old_binding = translator.variables.get(filter_pattern.loop_var)
        try:
            # Bind loop var to source element at j
            translator.variables[filter_pattern.loop_var] = source_seq[source_idx]

            pred_z3 = translator.translate_expr(filter_pattern.predicate)
            if pred_z3 is None:
                return axioms

            # Handle negated predicates (exclusion filters)
            if filter_pattern.is_negated:
                # For (not (eq item excluded)), all result elements satisfy (not (eq elem excluded))
                # This is a simpler axiom: just propagate the predicate
                pass

            # Build the axiom:
            # ForAll i in result: Exists j in source: result[i] == source[j] && pred(source[j])
            #
            # This says: every element in result came from source and satisfies the predicate
            source_constraint = z3.Exists([source_idx],
                z3.And(
                    source_idx >= 0,
                    source_idx < z3.Length(source_seq),
                    result_seq[result_idx] == source_seq[source_idx],
                    pred_z3
                )
            )

            axiom = z3.ForAll([result_idx],
                z3.Implies(
                    z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                    source_constraint
                )
            )
            axioms.append(axiom)

            # Also add a simpler axiom that directly states the postcondition property
            # For filter (pred t), every element in result satisfies pred
            # ForAll i: 0 <= i < Length(result) => pred(result[i])
            translator.variables[filter_pattern.loop_var] = result_seq[result_idx]
            pred_on_result = translator.translate_expr(filter_pattern.predicate)
            if pred_on_result is not None:
                direct_axiom = z3.ForAll([result_idx],
                    z3.Implies(
                        z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                        pred_on_result
                    )
                )
                axioms.append(direct_axiom)

        finally:
            # Restore binding
            if old_binding is not None:
                translator.variables[filter_pattern.loop_var] = old_binding
            elif filter_pattern.loop_var in translator.variables:
                del translator.variables[filter_pattern.loop_var]

        return axioms

    def _extract_map_push_axioms(self, fn_body: SExpr, postconditions: List[SExpr],
                                  translator: 'Z3Translator') -> List[z3.BoolRef]:
        """Generate axioms connecting result fields to source fields for map patterns.

        For map patterns like:
            (let ((mut result (list-new ...)))
              (for-each (dt (. delta triples))
                (list-push result
                  (triple-new arena
                    (triple-predicate dt)  ; predicate preserved
                    (triple-object dt)     ; subject <- object (swapped)
                    (triple-subject dt)))) ; object <- subject (swapped)
              result)

        Generates axiom:
            ForAll i: 0 <= i < Length($result) =>
                Exists j: 0 <= j < Length(source) &&
                    field_predicate($result[i]) == field_predicate(source[j]) &&
                    field_subject($result[i]) == field_object(source[j]) &&
                    field_object($result[i]) == field_subject(source[j])

        This enables proving postconditions like:
            (forall (t $result)
              (exists (dt (. delta triples))
                (and (term-eq (triple-predicate dt) (triple-predicate t))
                     (term-eq (triple-subject t) (triple-object dt))
                     (term-eq (triple-object t) (triple-subject dt)))))

        Also handles nested loop patterns (joins) like eq-trans where inner loops
        iterate over query results derived from outer loop variables.
        """
        axioms: List[z3.BoolRef] = []

        # First try: single-loop map pattern
        map_pattern = self._detect_map_pattern(fn_body)
        if map_pattern is None:
            # Second try: nested loop pattern (joins)
            nested_pattern = self._detect_nested_loop_pattern(fn_body)
            if nested_pattern is not None:
                return self._generate_nested_loop_axioms(
                    nested_pattern, postconditions, translator
                )
            return axioms

        # Need Seq for $result
        if '$result' not in translator.list_seqs:
            return axioms

        result_seq = translator.list_seqs['$result']

        # Get or create Seq for source collection
        source_seq = None
        source_name = None

        if isinstance(map_pattern.collection, Symbol):
            source_name = map_pattern.collection.name
            if source_name not in translator.list_seqs:
                translator._create_list_seq(source_name)
            source_seq = translator.list_seqs.get(source_name)
        elif is_form(map_pattern.collection, '.') and len(map_pattern.collection) >= 3:
            # Field access: (. obj field) - use same naming as property translator
            obj = map_pattern.collection[1]
            field = map_pattern.collection[2]
            if isinstance(obj, Symbol) and isinstance(field, Symbol):
                # Must match naming convention in _get_or_create_collection_seq:
                # "_field_{obj_name}_{field_name}"
                source_name = f"_field_{obj.name}_{field.name}"
                if source_name not in translator.list_seqs:
                    translator._create_list_seq(source_name)
                source_seq = translator.list_seqs.get(source_name)

        if source_seq is None:
            return axioms

        # Create index variables for the quantified formula
        result_idx = z3.Int('_map_res_i')
        source_idx = z3.Int('_map_src_j')

        # Build field correspondence constraints
        # For each (result_field, source_expr) in field_mappings,
        # generate: field_{result_field}($result[i]) == translate(source_expr)[loop_var/source[j]]

        old_binding = translator.variables.get(map_pattern.loop_var)
        try:
            # Bind loop var to source element at j for translating source expressions
            translator.variables[map_pattern.loop_var] = source_seq[source_idx]

            field_constraints = []

            # Determine the type prefix from the collection being iterated
            # For (. delta triples) iterating Triple elements, prefix is "triple"
            type_prefix = self._infer_element_type_prefix(map_pattern.collection)

            for result_field, source_expr in map_pattern.field_mappings.items():
                # Determine result accessor name
                if type_prefix:
                    result_accessor_name = f"{type_prefix}-{result_field}"
                else:
                    result_accessor_name = result_field

                # Create the result field function
                result_field_func_name = f"fn_{result_accessor_name}_1"
                if result_field_func_name not in translator.variables:
                    result_field_func = z3.Function(
                        result_field_func_name,
                        z3.IntSort(),
                        z3.IntSort()
                    )
                    translator.variables[result_field_func_name] = result_field_func
                else:
                    result_field_func = translator.variables[result_field_func_name]

                result_field_z3 = result_field_func(result_seq[result_idx])

                # Find appropriate equality function for the field type
                eq_func = self._get_type_equality_function(
                    result_accessor_name, translator
                )

                # Check if source_expr references the loop variable
                # If not, it's a constant field - use source field == result field
                if not self._references_var(source_expr, map_pattern.loop_var):
                    # Constant field: add constraint that source field equals result field
                    # This is valid because filter conditions ensure matching values
                    source_field_z3 = result_field_func(source_seq[source_idx])
                    if eq_func is not None:
                        field_constraints.append(eq_func(result_field_z3, source_field_z3))
                    else:
                        field_constraints.append(result_field_z3 == source_field_z3)
                    continue

                # Translate the source expression with loop var bound to source[j]
                source_z3 = translator.translate_expr(source_expr)
                if source_z3 is None:
                    continue

                # For map pattern: result.subject = source.object
                # We need: term-eq(triple-subject(result[i]), triple-object(source[j]))

                if eq_func is not None:
                    # Use type-specific equality: eq_func(result_field, source_field)
                    field_constraints.append(eq_func(result_field_z3, source_z3))
                else:
                    # Fallback to native equality
                    field_constraints.append(result_field_z3 == source_z3)

            if not field_constraints:
                return axioms

            # Build the axiom:
            # ForAll i in result: Exists j in source: AND(field_constraints...)
            source_constraint = z3.Exists([source_idx],
                z3.And(
                    source_idx >= 0,
                    source_idx < z3.Length(source_seq),
                    *field_constraints
                )
            )

            axiom = z3.ForAll([result_idx],
                z3.Implies(
                    z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                    source_constraint
                )
            )
            axioms.append(axiom)

            # Size relationship: result size <= source size
            # For unfiltered maps they're equal; for filtered maps result may be smaller
            size_axiom = z3.Length(result_seq) <= z3.Length(source_seq)
            axioms.append(size_axiom)

            # Completeness axiom (inverse direction):
            # ForAll j in source: filter_conditions(source[j]) =>
            #     Exists i in result: field_constraints(result[i], source[j])
            #
            # This enables proving "for every filtered source, there's a matching result"
            filter_conditions, filter_bindings = self._extract_filter_conditions_from_loop(fn_body)
            if filter_conditions:
                # Resolve variables in filter conditions through bindings
                resolved_conditions = [
                    self._resolve_filter_condition(cond, filter_bindings)
                    for cond in filter_conditions
                ]

                # Translate filter conditions with loop var bound to source[j]
                filter_z3 = []
                for cond in resolved_conditions:
                    cond_z3 = translator.translate_expr(cond)
                    if cond_z3 is not None:
                        filter_z3.append(cond_z3)

                if filter_z3:
                    # Build: filter1 AND filter2 AND ... => Exists result matching
                    result_constraint = z3.Exists([result_idx],
                        z3.And(
                            result_idx >= 0,
                            result_idx < z3.Length(result_seq),
                            *field_constraints
                        )
                    )

                    completeness_axiom = z3.ForAll([source_idx],
                        z3.Implies(
                            z3.And(
                                source_idx >= 0,
                                source_idx < z3.Length(source_seq),
                                *filter_z3
                            ),
                            result_constraint
                        )
                    )
                    axioms.append(completeness_axiom)

        finally:
            # Restore binding
            if old_binding is not None:
                translator.variables[map_pattern.loop_var] = old_binding
            elif map_pattern.loop_var in translator.variables:
                del translator.variables[map_pattern.loop_var]

        return axioms

    def _generate_nested_loop_axioms(
        self,
        pattern: NestedLoopPatternInfo,
        postconditions: List[SExpr],
        translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Generate axioms for nested loop join patterns.

        For nested patterns like eq-trans:
        (let ((same-as (make-iri arena OWL_SAME_AS))
              (mut result (list-new arena Triple)))
          (for-each (dt (. delta triples))
            (when (term-eq (triple-predicate dt) same-as)
              (let ((x (triple-subject dt))
                    (y (triple-object dt)))
                (let ((y-objects (indexed-graph-match ...)))
                  (for-each (yo-triple y-objects)
                    (let ((z (triple-object yo-triple)))
                      (when inner-filter
                        (list-push result (make-triple arena x same-as z)))))))))
          result)

        Generates axioms that connect result elements to outer collection elements
        based on field provenance analysis:

        For fields with OUTER provenance (e.g., subject from x = triple-subject(dt)):
            ForAll i in result: Exists j in outer_collection:
                outer_filter(outer_collection[j]) AND
                result_field(result[i]) = outer_field(outer_collection[j])

        For fields with CONSTANT provenance (e.g., predicate = same-as):
            ForAll i in result: Exists j in outer_collection:
                outer_filter(outer_collection[j]) AND
                result_field(result[i]) = constant_field(outer_collection[j])

        This enables proving properties like:
            (forall (t $result)
              (exists (dt (. delta triples))
                (term-eq (triple-predicate dt) (triple-predicate t))))
        """
        axioms: List[z3.BoolRef] = []

        # Need Seq for $result
        if '$result' not in translator.list_seqs:
            return axioms

        result_seq = translator.list_seqs['$result']

        # Get or create Seq for outer source collection
        outer_seq = None
        outer_name = None

        if isinstance(pattern.outer_collection, Symbol):
            outer_name = pattern.outer_collection.name
            if outer_name not in translator.list_seqs:
                translator._create_list_seq(outer_name)
            outer_seq = translator.list_seqs.get(outer_name)
        elif is_form(pattern.outer_collection, '.') and len(pattern.outer_collection) >= 3:
            # Field access: (. obj field)
            obj = pattern.outer_collection[1]
            field = pattern.outer_collection[2]
            if isinstance(obj, Symbol) and isinstance(field, Symbol):
                outer_name = f"_field_{obj.name}_{field.name}"
                if outer_name not in translator.list_seqs:
                    translator._create_list_seq(outer_name)
                outer_seq = translator.list_seqs.get(outer_name)

        if outer_seq is None:
            return axioms

        # Create index variables
        result_idx = z3.Int('_nested_res_i')
        outer_idx = z3.Int('_nested_outer_j')

        # Save and set up variable bindings
        old_outer_binding = translator.variables.get(pattern.outer_loop_var)

        try:
            # Bind outer loop var to outer element at j
            translator.variables[pattern.outer_loop_var] = outer_seq[outer_idx]

            # Also bind outer_bindings variables through resolution
            old_bindings = {}
            for var_name, var_expr in pattern.outer_bindings.items():
                old_bindings[var_name] = translator.variables.get(var_name)
                # Translate the binding expression with outer_loop_var bound
                var_z3 = translator.translate_expr(var_expr)
                if var_z3 is not None:
                    translator.variables[var_name] = var_z3

            # Determine type prefix from collection
            type_prefix = self._infer_element_type_prefix(pattern.outer_collection)

            # Build outer filter constraint (if any)
            outer_filter_z3 = None
            if pattern.outer_filter is not None:
                # Resolve filter condition through outer_let_bindings
                resolved_filter = self._resolve_filter_condition(
                    pattern.outer_filter, pattern.outer_let_bindings
                )
                outer_filter_z3 = translator.translate_expr(resolved_filter)

            # Build field constraints based on provenance
            field_constraints = []

            for result_field, source_expr in pattern.field_mappings.items():
                provenance = pattern.field_provenance.get(result_field, FieldSource.OUTER)

                # Determine result accessor name
                if type_prefix:
                    result_accessor_name = f"{type_prefix}-{result_field}"
                else:
                    result_accessor_name = result_field

                # Create the result field function
                result_field_func_name = f"fn_{result_accessor_name}_1"
                if result_field_func_name not in translator.variables:
                    result_field_func = z3.Function(
                        result_field_func_name,
                        z3.IntSort(),
                        z3.IntSort()
                    )
                    translator.variables[result_field_func_name] = result_field_func
                else:
                    result_field_func = translator.variables[result_field_func_name]

                result_field_z3 = result_field_func(result_seq[result_idx])

                # Get equality function
                eq_func = self._get_type_equality_function(result_accessor_name, translator)

                if provenance == FieldSource.CONSTANT:
                    # Constant field: result field equals constant from outer source
                    # For same-as predicate: triple-predicate(result[i]) = triple-predicate(outer[j])
                    # (since both are filtered to have same-as predicate)
                    outer_field_z3 = result_field_func(outer_seq[outer_idx])
                    if eq_func is not None:
                        field_constraints.append(eq_func(result_field_z3, outer_field_z3))
                    else:
                        field_constraints.append(result_field_z3 == outer_field_z3)

                elif provenance == FieldSource.OUTER:
                    # Outer field: result field equals expression derived from outer var
                    # Resolve through bindings
                    resolved_expr = self._resolve_through_context(
                        source_expr, pattern.outer_bindings
                    )
                    source_z3 = translator.translate_expr(resolved_expr)
                    if source_z3 is not None:
                        if eq_func is not None:
                            field_constraints.append(eq_func(result_field_z3, source_z3))
                        else:
                            field_constraints.append(result_field_z3 == source_z3)

                elif provenance == FieldSource.INNER:
                    # Inner field: derived from inner loop - harder to axiomatize simply
                    # For now, just add that the field type matches outer collection type
                    # This is a weaker axiom but still useful
                    outer_field_z3 = result_field_func(outer_seq[outer_idx])
                    # We can't prove direct equality, but we know the types match
                    # Skip adding constraint for INNER provenance in the outer existence axiom
                    pass

                # MIXED provenance - skip, too complex

            if not field_constraints:
                return axioms

            # Build the outer existence axiom:
            # ForAll i in result: Exists j in outer:
            #     outer_filter(outer[j]) AND field_constraints
            outer_constraint_parts = [
                outer_idx >= 0,
                outer_idx < z3.Length(outer_seq)
            ]
            if outer_filter_z3 is not None:
                outer_constraint_parts.append(outer_filter_z3)
            outer_constraint_parts.extend(field_constraints)

            outer_existence = z3.Exists([outer_idx], z3.And(*outer_constraint_parts))

            axiom = z3.ForAll([result_idx],
                z3.Implies(
                    z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                    outer_existence
                )
            )
            axioms.append(axiom)

            # Size relationship: result size <= outer size
            # (may be much smaller due to filtering and join)
            size_axiom = z3.Length(result_seq) <= z3.Length(outer_seq)
            axioms.append(size_axiom)

        finally:
            # Restore bindings
            if old_outer_binding is not None:
                translator.variables[pattern.outer_loop_var] = old_outer_binding
            elif pattern.outer_loop_var in translator.variables:
                del translator.variables[pattern.outer_loop_var]

            for var_name, old_val in old_bindings.items():
                if old_val is not None:
                    translator.variables[var_name] = old_val
                elif var_name in translator.variables:
                    del translator.variables[var_name]

        return axioms

    def _extract_filter_conditions_from_loop(
        self, fn_body: SExpr
    ) -> Tuple[List[SExpr], Dict[str, SExpr]]:
        """Extract filter conditions from (when ...) clauses leading to list-push.

        For patterns like:
            (let ((mut result (list-new arena Type)))
              (for-each (dt source)
                (when cond1
                  (let ((x expr1))
                    (when cond2
                      (list-push result ...)))))
              result)

        Returns:
            - List of filter condition expressions [cond1, cond2]
            - Bindings context for variable resolution {'x': expr1}

        This is used to generate completeness axioms for filtered map patterns.
        """
        # Must be a let expression
        if not is_form(fn_body, 'let') or len(fn_body) < 3:
            return [], {}

        bindings = fn_body[1]
        if not isinstance(bindings, SList):
            return [], {}

        # Build initial bindings context from outer let
        initial_bindings: Dict[str, SExpr] = {}
        for binding in bindings.items:
            if isinstance(binding, SList) and len(binding) >= 2:
                first = binding[0]
                if isinstance(first, Symbol):
                    if first.name == 'mut' and len(binding) >= 3:
                        var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                        var_value = binding[2]
                    else:
                        var_name = first.name
                        var_value = binding[1]
                    if var_name and var_value:
                        initial_bindings[var_name] = var_value

        # Find for-each loop in body
        body_exprs = fn_body.items[2:]
        for body_expr in body_exprs:
            if is_form(body_expr, 'for-each') and len(body_expr) >= 3:
                loop_body = body_expr.items[2:]
                # Extract conditions from the loop body
                conditions, bindings_ctx = self._collect_filter_conditions(
                    loop_body, initial_bindings.copy()
                )
                return conditions, bindings_ctx

        return [], initial_bindings

    def _collect_filter_conditions(
        self, stmts: List[SExpr], bindings: Dict[str, SExpr]
    ) -> Tuple[List[SExpr], Dict[str, SExpr]]:
        """Recursively collect filter conditions from when clauses on path to list-push.

        Traverses into when, let, and do forms, collecting:
        - Conditions from (when cond ...) clauses
        - Variable bindings from (let ((x val)) ...)

        Returns (conditions, bindings) when list-push is found, or ([], bindings) otherwise.
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Handle (when condition body)
            if is_form(stmt, 'when') and len(stmt) >= 3:
                condition = stmt[1]
                then_body = stmt[2]

                # Check if then_body contains list-push (possibly nested)
                if self._contains_list_push([then_body]):
                    # Recursively collect conditions from then_body
                    inner_conditions, inner_bindings = self._collect_filter_conditions(
                        [then_body], bindings.copy()
                    )
                    # Prepend this condition
                    return [condition] + inner_conditions, inner_bindings

            # Handle (let ((x val) ...) body...)
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

                # Recurse into let body
                inner_conditions, inner_bindings = self._collect_filter_conditions(
                    stmt.items[2:], new_bindings
                )
                if inner_conditions or self._contains_list_push(stmt.items[2:]):
                    return inner_conditions, inner_bindings

            # Handle (do body...)
            if is_form(stmt, 'do') and len(stmt) >= 2:
                inner_conditions, inner_bindings = self._collect_filter_conditions(
                    stmt.items[1:], bindings.copy()
                )
                if inner_conditions or self._contains_list_push(stmt.items[1:]):
                    return inner_conditions, inner_bindings

            # Found list-push - return empty conditions (base case)
            if is_form(stmt, 'list-push'):
                return [], bindings

        return [], bindings

    def _contains_list_push(self, stmts: List[SExpr]) -> bool:
        """Check if any statement contains a list-push call."""
        for stmt in stmts:
            if is_form(stmt, 'list-push'):
                return True
            if isinstance(stmt, SList):
                # Recurse into nested forms
                if is_form(stmt, 'when') and len(stmt) >= 3:
                    if self._contains_list_push([stmt[2]]):
                        return True
                elif is_form(stmt, 'let') and len(stmt) >= 3:
                    if self._contains_list_push(stmt.items[2:]):
                        return True
                elif is_form(stmt, 'do') and len(stmt) >= 2:
                    if self._contains_list_push(stmt.items[1:]):
                        return True
        return False

    def _resolve_filter_condition(
        self, condition: SExpr, bindings: Dict[str, SExpr]
    ) -> SExpr:
        """Resolve variables in filter condition through let bindings.

        For condition: (not (indexed-graph-contains g inferred))
        With bindings: {'inferred': (make-triple arena y same-as x),
                        'same-as': (make-iri arena OWL_SAME_AS)}

        Recursively substitutes variable references with their bound values.
        Also simplifies constructor calls like (make-iri arena X) to X for
        verification purposes, since these wrappers don't affect equality semantics.

        Returns fully resolved condition.
        """
        if isinstance(condition, Symbol):
            var_name = condition.name
            if var_name in bindings:
                # Recursively resolve the bound value
                return self._resolve_filter_condition(bindings[var_name], bindings)
            return condition

        if isinstance(condition, SList) and len(condition) >= 1:
            head = condition[0]

            # Simplify (make-iri arena X) -> X
            # make-iri is a constructor that wraps a string to create an IRI Term
            # For verification, we treat it as identity since term-eq on make-iri(X)
            # is equivalent to checking the underlying value X
            if isinstance(head, Symbol) and head.name == 'make-iri' and len(condition) >= 3:
                # (make-iri arena value) -> value
                value = condition[2]
                return self._resolve_filter_condition(value, bindings)

            # Recursively resolve each element
            resolved_items = [
                self._resolve_filter_condition(item, bindings)
                for item in condition.items
            ]
            return SList(resolved_items, condition.line, condition.col)

        return condition

    def _infer_element_type_prefix(self, collection: SExpr) -> Optional[str]:
        """Infer the element type prefix from a collection expression.

        For (. delta triples) where triples is a list of Triple, returns "triple".
        For a variable 'triples' that is (List Triple), returns "triple".

        This is used to construct field accessor names like triple-subject.
        """
        # Check for field access: (. obj field)
        if is_form(collection, '.') and len(collection) >= 3:
            field = collection[2]
            if isinstance(field, Symbol):
                field_name = field.name
                # Common patterns: "triples" -> "triple", "terms" -> "term"
                if field_name.endswith('s'):
                    return field_name[:-1]  # Remove trailing 's'
                return field_name

        # Check for simple variable name
        if isinstance(collection, Symbol):
            var_name = collection.name
            if var_name.endswith('s'):
                return var_name[:-1]
            return var_name

        return None

    def _get_type_equality_function(
        self, accessor_name: str, translator: 'Z3Translator'
    ) -> Optional[z3.FuncDeclRef]:
        """Get the appropriate equality function for a field type.

        For field accessors like triple-predicate, triple-subject, triple-object,
        the field type is Term, so we check for imported term-eq function.

        IMPORTANT: Only returns an equality function if:
        1. The function is imported with a postcondition defining its semantics, OR
        2. The function already exists in the translator's variables

        If no imported equality function is found, returns None to use native ==.
        This ensures axioms align with what Z3 can actually reason about.

        Returns Z3 function or None if no specific equality function found.
        """
        # Known mappings: accessor pattern -> equality function name
        # Triple fields (predicate, subject, object) are Term type
        triple_field_accessors = {'triple-predicate', 'triple-subject', 'triple-object'}

        if accessor_name in triple_field_accessors:
            eq_func_name = "fn_term-eq_2"
            # Only use if already exists (imported and set up)
            if eq_func_name in translator.variables:
                return translator.variables[eq_func_name]
            # Check if term-eq is imported with semantics
            if self._has_imported_equality_semantics('term-eq'):
                eq_func = z3.Function(
                    eq_func_name,
                    z3.IntSort(), z3.IntSort(), z3.BoolSort()
                )
                translator.variables[eq_func_name] = eq_func
                return eq_func
            # No imported term-eq with semantics - use native ==
            return None

        # Try to infer from accessor pattern: {type}-{field} -> {type}-eq
        if '-' in accessor_name:
            type_prefix = accessor_name.rsplit('-', 1)[0]
            eq_func_name = f"fn_{type_prefix}-eq_2"
            if eq_func_name in translator.variables:
                return translator.variables[eq_func_name]
            # Check if type-eq is imported with semantics
            if self._has_imported_equality_semantics(f'{type_prefix}-eq'):
                eq_func = z3.Function(
                    eq_func_name,
                    z3.IntSort(), z3.IntSort(), z3.BoolSort()
                )
                translator.variables[eq_func_name] = eq_func
                return eq_func
            # No imported equality function with semantics - use native ==
            return None

        return None

    def _has_imported_equality_semantics(self, eq_func_name: str) -> bool:
        """Check if an equality function is imported with postcondition semantics.

        Returns True if the function is imported with (@post (== $result (== a b))).
        """
        sig = self.imported_defs.functions.get(eq_func_name)
        if sig is None or len(sig.params) != 2:
            return False

        # Check postconditions for pattern: (== $result (== a b))
        for post in sig.postconditions:
            if is_form(post, '==') and len(post) == 3:
                lhs, rhs = post[1], post[2]
                # Check for (== $result (== ...)) or (== (== ...) $result)
                if isinstance(lhs, Symbol) and lhs.name == '$result':
                    if is_form(rhs, '==') and len(rhs) == 3:
                        return True
                elif isinstance(rhs, Symbol) and rhs.name == '$result':
                    if is_form(lhs, '==') and len(lhs) == 3:
                        return True
        return False

    def _extract_imported_equality_axioms(
        self, translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Extract axioms from imported equality functions.

        For imported functions like term-eq with postcondition:
            (@post (== $result (== a b)))

        Generate a Z3 axiom that tells Z3 what the equality function means:
            ForAll a, b: fn_term-eq_2(a, b) == (a == b)

        This allows Z3 to reason about equality in properties.
        """
        axioms: List[z3.BoolRef] = []

        for fn_name, sig in self.imported_defs.functions.items():
            # Check if this looks like an equality function
            if not (fn_name.endswith('-eq') or fn_name.endswith('?')):
                continue

            # Must have exactly 2 parameters
            if len(sig.params) != 2:
                continue

            # Check postconditions for pattern: (== $result (== a b))
            for post in sig.postconditions:
                eq_axiom = self._parse_equality_postcondition(
                    fn_name, sig.params, post, translator
                )
                if eq_axiom is not None:
                    axioms.append(eq_axiom)

        return axioms

    def _parse_equality_postcondition(
        self,
        fn_name: str,
        params: List[str],
        post: SExpr,
        translator: 'Z3Translator'
    ) -> Optional[z3.BoolRef]:
        """Parse an equality postcondition and generate a Z3 axiom.

        Pattern: (== $result (== a b)) or (== $result (== b a))
        where a, b are the function's parameters.

        Returns: ForAll a, b: fn_name(a, b) == (a == b)
        """
        if not is_form(post, '==') or len(post) != 3:
            return None

        lhs, rhs = post[1], post[2]

        # Check for (== $result (== ...))
        if not (isinstance(lhs, Symbol) and lhs.name == '$result'):
            # Try swapped: (== (== ...) $result)
            if isinstance(rhs, Symbol) and rhs.name == '$result':
                lhs, rhs = rhs, lhs
            else:
                return None

        # rhs should be (== a b) where a, b are the params
        if not is_form(rhs, '==') or len(rhs) != 3:
            return None

        inner_lhs, inner_rhs = rhs[1], rhs[2]
        if not (isinstance(inner_lhs, Symbol) and isinstance(inner_rhs, Symbol)):
            return None

        # Check that these are the function's parameters
        param_names = {inner_lhs.name, inner_rhs.name}
        if param_names != set(params):
            return None

        # Create or get the Z3 function
        func_key = f"fn_{fn_name}_2"
        if func_key not in translator.variables:
            func = z3.Function(func_key, z3.IntSort(), z3.IntSort(), z3.BoolSort())
            translator.variables[func_key] = func
        else:
            func = translator.variables[func_key]

        # Create quantified variables
        a = z3.Int(f'{fn_name}_a')
        b = z3.Int(f'{fn_name}_b')

        # Generate axiom: ForAll a, b: fn(a, b) == (a == b)
        axiom = z3.ForAll([a, b], func(a, b) == (a == b))
        return axiom

    def _extract_imported_postcondition_axioms(
        self, translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Extract universal axioms from imported function postconditions.

        For imported functions with postconditions, generate universally quantified
        axioms that enable reasoning about relational properties involving multiple
        calls to the same function.

        For example, for a function like indexed-graph-match with postcondition:
            (@post (forall (t $result) (indexed-graph-contains g t)))

        We generate an axiom that universally quantifies over the function's parameters:
            ForAll arena, g, s, p, o:
                ForAll t in (indexed-graph-match arena g s p o):
                    indexed-graph-contains(g, t)

        This enables verifying properties like completeness-forward that involve
        both filtered and unfiltered calls to the same function.
        """
        axioms: List[z3.BoolRef] = []

        for fn_name, sig in self.imported_defs.functions.items():
            if not sig.postconditions:
                continue

            # Skip equality functions - handled by _extract_imported_equality_axioms
            if fn_name.endswith('-eq') and len(sig.params) == 2:
                continue

            for post in sig.postconditions:
                axiom = self._translate_postcondition_as_universal_axiom(
                    fn_name, sig, post, translator
                )
                if axiom is not None:
                    axioms.append(axiom)

        return axioms

    def _translate_postcondition_as_universal_axiom(
        self,
        fn_name: str,
        sig: 'FunctionSignature',
        post: SExpr,
        translator: 'Z3Translator'
    ) -> Optional[z3.BoolRef]:
        """Translate a single postcondition as a universal axiom.

        The postcondition is universally quantified over the function's parameters.
        $result is replaced with a call to the function with the quantified params.

        For example:
            fn: indexed-graph-match(arena, g, s, p, o)
            @post: (forall (t $result) (pred t))

        Becomes:
            ForAll arena, g, s, p, o:
                ForAll t in (indexed-graph-match arena g s p o):
                    pred(t)
        """
        from .types import FunctionSignature

        if not sig.params:
            return None

        # Create quantified variables for each parameter
        param_vars: List[z3.ArithRef] = []
        param_map: Dict[str, z3.ArithRef] = {}

        for i, param_name in enumerate(sig.params):
            # Create a unique Z3 variable for this parameter
            var = z3.Int(f'_ax_{fn_name}_{param_name}')
            param_vars.append(var)
            param_map[param_name] = var

        # Create or get the Z3 function for the function call
        func_key = f"fn_{fn_name}_{len(sig.params)}"
        if func_key not in translator.variables:
            # Determine return sort based on postcondition patterns
            # If postcondition uses forall/exists with $result, it's a collection
            if self._postcondition_treats_result_as_collection(post):
                # For collections, we model the function result as an Int (id)
                # and create a corresponding Seq if needed
                return_sort = z3.IntSort()
            else:
                return_sort = z3.IntSort()

            arg_sorts = [z3.IntSort()] * len(sig.params)
            func = z3.Function(func_key, *arg_sorts, return_sort)
            translator.variables[func_key] = func
        else:
            func = translator.variables[func_key]

        # Create the function call with quantified parameters
        fn_result = func(*param_vars)

        # Save current variable bindings
        saved_vars: Dict[str, z3.ExprRef] = {}
        for param_name, param_var in param_map.items():
            saved_vars[param_name] = translator.variables.get(param_name)
            translator.variables[param_name] = param_var

        # For collection-returning functions, set up a Seq for $result
        # that represents the function's result with these specific parameters
        saved_result = translator.variables.get('$result')
        saved_result_seq = translator.list_seqs.get('$result')

        try:
            # If postcondition uses $result as a collection, create a Seq for it
            if self._postcondition_treats_result_as_collection(post):
                # Create a unique Seq name for this function call
                seq_name = f'_ax_{fn_name}_result'
                if seq_name not in translator.list_seqs:
                    translator._create_list_seq(seq_name)
                result_seq = translator.list_seqs.get(seq_name)
                if result_seq is not None:
                    translator.list_seqs['$result'] = result_seq
                    # Also bind $result to the function result (id)
                    translator.variables['$result'] = fn_result
            else:
                translator.variables['$result'] = fn_result

            # Translate the postcondition body
            post_z3 = translator.translate_expr(post)
            if post_z3 is None or not z3.is_bool(post_z3):
                return None

            # Wrap in universal quantifier over all parameters
            if param_vars:
                return z3.ForAll(param_vars, post_z3)
            else:
                return post_z3

        finally:
            # Restore variable bindings
            for param_name, saved_val in saved_vars.items():
                if saved_val is None:
                    if param_name in translator.variables:
                        del translator.variables[param_name]
                else:
                    translator.variables[param_name] = saved_val

            if saved_result is None:
                if '$result' in translator.variables:
                    del translator.variables['$result']
            else:
                translator.variables['$result'] = saved_result

            if saved_result_seq is None:
                if '$result' in translator.list_seqs:
                    del translator.list_seqs['$result']
            else:
                translator.list_seqs['$result'] = saved_result_seq

    def _postcondition_treats_result_as_collection(self, post: SExpr) -> bool:
        """Check if a postcondition treats $result as a collection.

        Returns True if the postcondition contains patterns like:
        - (forall (t $result) ...)
        - (exists (t $result) ...)
        - (list-len $result)
        """
        if isinstance(post, SList) and len(post) >= 1:
            head = post[0]
            if isinstance(head, Symbol):
                # Check for (forall (t $result) ...) or (exists (t $result) ...)
                if head.name in ('forall', 'exists') and len(post) >= 3:
                    binding = post[1]
                    if isinstance(binding, SList) and len(binding) == 2:
                        coll = binding[1]
                        if isinstance(coll, Symbol) and coll.name == '$result':
                            return True

                # Check for (list-len $result)
                if head.name == 'list-len' and len(post) >= 2:
                    arg = post[1]
                    if isinstance(arg, Symbol) and arg.name == '$result':
                        return True

            # Recursively check subexpressions
            for item in post.items:
                if self._postcondition_treats_result_as_collection(item):
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


__all__ = ['AxiomGenerationMixin']
