"""
Union Type Handling Mixin for ContractVerifier.

Provides methods for handling union types, detecting union equality functions,
and generating axioms for union constructors and pattern matching.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Tuple, TYPE_CHECKING

from slop.parser import SList, Symbol, String, is_form
from slop.types import UnionType

from .z3_setup import Z3_AVAILABLE, z3

if TYPE_CHECKING:
    from slop.parser import SExpr
    from .translator import Z3Translator


class UnionHandlingMixin:
    """Mixin providing union type handling methods."""

    def _is_union_new(self, expr: SExpr) -> bool:
        """Check if expression is a union-new form (handles do blocks)"""
        return_expr = self._get_return_expr(expr)
        return is_form(return_expr, 'union-new')

    def _is_union_constructor(self, expr: SExpr) -> bool:
        """Check if expression is a union constructor like (ok value) or (error e).

        Handles do blocks by checking the return expression.
        """
        return_expr = self._get_return_expr(expr)
        if not isinstance(return_expr, SList) or len(return_expr) < 2:
            return False

        head = return_expr[0]
        if not isinstance(head, Symbol):
            return False

        # Common Result/Option constructors
        constructors = {'ok', 'error', 'some', 'none'}
        return head.name in constructors

    def _extract_union_constructor_axioms(self, body: SExpr, translator: Z3Translator) -> List:
        """Extract axioms for union constructors like (ok result) or (error e).

        For (ok result), adds:
        1. union_tag($result) == ok_index
        2. union_payload_ok($result) == result

        This enables proving match postconditions like:
        (match $result ((ok d) (== (. d field) x)) ((error _) true))
        """
        axioms = []
        return_expr = self._get_return_expr(body)

        if not isinstance(return_expr, SList) or len(return_expr) < 1:
            return axioms

        head = return_expr[0]
        if not isinstance(head, Symbol):
            return axioms

        constructor_name = head.name
        constructors = {'ok', 'error', 'some', 'none'}

        if constructor_name not in constructors:
            return axioms

        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # Use the same tag index calculation as _translate_match
        # Check enum_values first, fall back to hash
        tag_idx = translator.enum_values.get(
            constructor_name,
            translator.enum_values.get(f"'{constructor_name}", hash(constructor_name) % 256)
        )

        # Get or create union_tag function
        tag_func_name = "union_tag"
        if tag_func_name not in translator.variables:
            tag_func = z3.Function(tag_func_name, z3.IntSort(), z3.IntSort())
            translator.variables[tag_func_name] = tag_func
        else:
            tag_func = translator.variables[tag_func_name]

        # Axiom 1: union_tag($result) == constructor_index
        axioms.append(tag_func(result_var) == z3.IntVal(tag_idx))

        # Axiom 2: union_payload_<constructor>($result) == payload
        if len(return_expr) >= 2:
            payload_expr = return_expr[1]
            payload_z3 = translator.translate_expr(payload_expr)

            if payload_z3 is not None:
                payload_func_name = f"union_payload_{constructor_name}"
                if payload_func_name not in translator.variables:
                    # Create function with appropriate return sort
                    if z3.is_bool(payload_z3):
                        payload_func = z3.Function(payload_func_name, z3.IntSort(), z3.BoolSort())
                    elif z3.is_real(payload_z3):
                        payload_func = z3.Function(payload_func_name, z3.IntSort(), z3.RealSort())
                    else:
                        payload_func = z3.Function(payload_func_name, z3.IntSort(), z3.IntSort())
                    translator.variables[payload_func_name] = payload_func
                else:
                    payload_func = translator.variables[payload_func_name]

                axioms.append(payload_func(result_var) == payload_z3)

                # Axiom 3: If payload is a record-new, propagate field axioms
                # For (some (record-new Type (field1 val1) ...)), add:
                #   field_field1(union_payload_some($result)) == val1
                #   string_len(field_field1(union_payload_some($result))) == len if val1 is string
                if is_form(payload_expr, 'record-new') and len(payload_expr) >= 3:
                    payload_var = payload_func(result_var)  # This is union_payload_some($result)
                    for item in payload_expr.items[2:]:  # Skip 'record-new' and Type
                        if isinstance(item, SList) and len(item) >= 2:
                            field_name = item[0].name if isinstance(item[0], Symbol) else None
                            if field_name:
                                field_func = translator._translate_field_for_obj(payload_var, field_name)
                                field_value = translator.translate_expr(item[1])
                                if field_value is not None:
                                    axioms.append(field_func == field_value)

                                # If field value is a string literal, add string_len axiom
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

    def _extract_union_constructor_axioms_for_expr(
        self, return_expr: SExpr, translator: Z3Translator
    ) -> List:
        """Extract CONDITIONAL axioms for a union constructor return expression.

        For functions with multiple return paths (e.g., early return (some ...) and
        final (none)), we add conditional axioms:
            union_tag($result) == some_tag => field_X(payload($result)) == value

        This allows Z3 to use these axioms when exploring the 'some' case in a
        match postcondition, without conflicting with the 'none' return path.
        """
        axioms = []

        if not isinstance(return_expr, SList) or len(return_expr) < 1:
            return axioms

        head = return_expr[0]
        if not isinstance(head, Symbol):
            return axioms

        constructor_name = head.name
        constructors = {'ok', 'error', 'some', 'none'}

        if constructor_name not in constructors:
            return axioms

        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # Get tag index using same calculation as _translate_match
        tag_idx = translator.enum_values.get(
            constructor_name,
            translator.enum_values.get(f"'{constructor_name}", hash(constructor_name) % 256)
        )

        # Get or create union_tag function
        tag_func_name = "union_tag"
        if tag_func_name not in translator.variables:
            tag_func = z3.Function(tag_func_name, z3.IntSort(), z3.IntSort())
            translator.variables[tag_func_name] = tag_func
        else:
            tag_func = translator.variables[tag_func_name]

        # Condition: this return path was taken (i.e., tag matches this constructor)
        tag_condition = tag_func(result_var) == z3.IntVal(tag_idx)

        # For constructors with payload (some, ok, error), add conditional field axioms
        if len(return_expr) >= 2 and constructor_name != 'none':
            payload_expr = return_expr[1]

            # Get or create payload function
            payload_func_name = f"union_payload_{constructor_name}"
            if payload_func_name not in translator.variables:
                payload_func = z3.Function(payload_func_name, z3.IntSort(), z3.IntSort())
                translator.variables[payload_func_name] = payload_func
            else:
                payload_func = translator.variables[payload_func_name]

            payload_var = payload_func(result_var)

            # If payload is a record-new, add conditional field axioms
            if is_form(payload_expr, 'record-new') and len(payload_expr) >= 3:
                for item in payload_expr.items[2:]:  # Skip 'record-new' and Type
                    if isinstance(item, SList) and len(item) >= 2:
                        field_name = item[0].name if isinstance(item[0], Symbol) else None
                        if field_name:
                            field_func = translator._translate_field_for_obj(payload_var, field_name)
                            field_value = translator.translate_expr(item[1])

                            if field_value is not None:
                                # Conditional: tag == X => field == value
                                axioms.append(z3.Implies(tag_condition, field_func == field_value))

                            # If field is string literal, add conditional string_len axiom
                            if isinstance(item[1], String):
                                str_len_func_name = "string_len"
                                if str_len_func_name not in translator.variables:
                                    str_len_func = z3.Function(str_len_func_name, z3.IntSort(), z3.IntSort())
                                    translator.variables[str_len_func_name] = str_len_func
                                else:
                                    str_len_func = translator.variables[str_len_func_name]
                                actual_len = len(item[1].value)
                                # Conditional: tag == X => string_len(field) == actual_len
                                axioms.append(z3.Implies(
                                    tag_condition,
                                    str_len_func(field_func) == z3.IntVal(actual_len)
                                ))

        return axioms

    def _extract_union_tag_axiom(self, union_new: SList, translator: Z3Translator) -> Optional:
        """Extract axiom: union_tag($result) == tag_index for union-new body.

        When the function body is (union-new Type tag payload), we can prove
        that match expressions checking the tag will succeed for that tag.
        """
        # union-new Type tag payload
        if len(union_new) < 3:
            return None

        result_var = translator.variables.get('$result')
        if result_var is None:
            return None

        # Get tag (can be symbol or quoted symbol)
        tag_expr = union_new[2]
        if isinstance(tag_expr, Symbol):
            tag_name = tag_expr.name.lstrip("'")
        elif is_form(tag_expr, 'quote') and len(tag_expr) >= 2:
            inner = tag_expr[1]
            tag_name = inner.name if isinstance(inner, Symbol) else None
        else:
            tag_name = None

        if tag_name is None:
            return None

        # Get tag index from enum_values or hash
        tag_idx = translator.enum_values.get(tag_name,
                  translator.enum_values.get(f"'{tag_name}",
                  hash(tag_name) % 256))

        # Get or create union_tag function
        tag_func_name = "union_tag"
        if tag_func_name not in translator.variables:
            tag_func = z3.Function(tag_func_name, z3.IntSort(), z3.IntSort())
            translator.variables[tag_func_name] = tag_func
        else:
            tag_func = translator.variables[tag_func_name]

        return tag_func(result_var) == z3.IntVal(tag_idx)

    def _extract_union_new_field_axioms(self, union_new: SList, translator: Z3Translator) -> List:
        """Extract field axioms for union-new with record-new payload.

        For (union-new ReasonerResult reason-success (record-new ReasonerSuccess ... (iterations x) ...)),
        adds axioms like:
            field_iterations(union_payload_reason_success($result)) == x
        """
        axioms = []

        # union-new Type tag payload
        if len(union_new) < 4:
            return axioms

        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # Get tag name
        tag_expr = union_new[2]
        if isinstance(tag_expr, Symbol):
            tag_name = tag_expr.name.lstrip("'")
        elif is_form(tag_expr, 'quote') and len(tag_expr) >= 2:
            inner = tag_expr[1]
            tag_name = inner.name if isinstance(inner, Symbol) else None
        else:
            tag_name = None

        if tag_name is None:
            return axioms

        # Get payload
        payload_expr = union_new[3]

        # Check if payload is record-new
        if not is_form(payload_expr, 'record-new') or len(payload_expr) < 3:
            return axioms

        # Get or create union_payload function for this tag
        payload_func_name = f"union_payload_{tag_name}"
        if payload_func_name not in translator.variables:
            payload_func = z3.Function(payload_func_name, z3.IntSort(), z3.IntSort())
            translator.variables[payload_func_name] = payload_func
        else:
            payload_func = translator.variables[payload_func_name]

        # payload_var represents union_payload_tag($result)
        payload_var = payload_func(result_var)

        # Extract field values from record-new
        # (record-new Type (field1 val1) (field2 val2) ...)
        for item in payload_expr.items[2:]:  # Skip 'record-new' and Type
            if isinstance(item, SList) and len(item) >= 2:
                field_name = item[0].name if isinstance(item[0], Symbol) else None
                if field_name:
                    field_func = translator._translate_field_for_obj(payload_var, field_name)
                    field_value = translator.translate_expr(item[1])
                    if field_value is not None:
                        axioms.append(field_func == field_value)

        return axioms

    def _detect_union_equality_function(self, fn_form: SList) -> Optional[Tuple[str, str, str]]:
        """Detect union equality function pattern.

        Returns (param1_name, param2_name, union_type_name) if detected, None otherwise.

        Pattern:
        - Function name ends in -eq
        - Two parameters of same union type
        - Postcondition contains (== $result (== a b))
        """
        # Check function name ends in -eq
        if len(fn_form) < 3:
            return None
        fn_name = fn_form[1].name if isinstance(fn_form[1], Symbol) else None
        if not fn_name or not fn_name.endswith('-eq'):
            return None

        # Check for two parameters of same type
        params = fn_form[2]
        if not isinstance(params, SList) or len(params) < 2:
            return None

        param1_name = None
        param1_type = None
        param2_name = None
        param2_type = None

        for i, param in enumerate(params.items[:2]):
            if isinstance(param, SList) and len(param) >= 2:
                first = param[0]
                if isinstance(first, Symbol) and first.name in ('in', 'out', 'mut'):
                    pname = param[1].name if isinstance(param[1], Symbol) else None
                    ptype = param[2] if len(param) > 2 else None
                else:
                    pname = first.name if isinstance(first, Symbol) else None
                    ptype = param[1]

                if i == 0:
                    param1_name = pname
                    param1_type = ptype
                else:
                    param2_name = pname
                    param2_type = ptype

        if not param1_name or not param2_name:
            return None

        # Get type names
        type1_name = param1_type.name if isinstance(param1_type, Symbol) else None
        type2_name = param2_type.name if isinstance(param2_type, Symbol) else None

        if not type1_name or type1_name != type2_name:
            return None

        # Check if it's a union type
        if type1_name not in self.type_env.type_registry:
            return None
        typ = self.type_env.type_registry[type1_name]
        if not isinstance(typ, UnionType):
            return None

        # Check for postcondition (== $result (== a b))
        has_equality_post = False
        for item in fn_form.items[3:]:
            if is_form(item, '@post') and len(item) >= 2:
                post = item[1]
                # Look for (== $result (== a b)) pattern
                if is_form(post, '==') and len(post) >= 3:
                    left = post[1]
                    right = post[2]
                    if isinstance(left, Symbol) and left.name == '$result':
                        if is_form(right, '==') and len(right) >= 3:
                            has_equality_post = True
                            break

        if not has_equality_post:
            return None

        return (param1_name, param2_name, type1_name)

    def _extract_helper_eq_calls_from_match(self, body: SExpr) -> Dict[str, str]:
        """Extract helper equality function calls from nested match body.

        Returns dict mapping variant name to helper-eq function name.
        E.g., {'iri': 'iri-eq', 'blank': 'blank-eq', 'literal': 'literal-eq'}
        """
        result: Dict[str, str] = {}
        self._collect_eq_from_match(body, result, None)
        return result

    def _collect_eq_from_match(self, expr: SExpr, result: Dict[str, str], current_variant: Optional[str]):
        """Recursively collect helper-eq calls from match expressions."""
        if is_form(expr, 'match') and len(expr) >= 3:
            # Process each clause
            for clause in expr.items[2:]:
                if isinstance(clause, SList) and len(clause) >= 2:
                    pattern = clause[0]
                    body = clause[1]

                    # Extract variant name from pattern
                    variant_name = None
                    if isinstance(pattern, SList) and len(pattern) >= 1:
                        tag = pattern[0]
                        if isinstance(tag, Symbol):
                            variant_name = tag.name.lstrip("'")
                        elif is_form(tag, 'quote') and len(tag) >= 2:
                            inner = tag[1]
                            variant_name = inner.name if isinstance(inner, Symbol) else None

                    if variant_name and variant_name != '_':
                        # Check if body contains a -eq call
                        eq_func = self._find_eq_call_in_expr(body)
                        if eq_func:
                            result[variant_name] = eq_func
                        else:
                            # Recurse into nested match
                            self._collect_eq_from_match(body, result, variant_name)

    def _find_eq_call_in_expr(self, expr: SExpr) -> Optional[str]:
        """Find the first -eq function call or == operator in an expression.

        Returns:
        - Function name ending in -eq (e.g., 'iri-eq', 'string-eq')
        - '==' if the expression uses native equality OR if a -eq function
          would inline to native equality
        - None if no equality comparison found

        Note: If a -eq function is simple inlinable, we return what it INLINES TO
        rather than the function name itself. This ensures union equality axioms
        match the actual Z3 expressions generated during body translation.

        Examples:
        - (num-eq a b) where num-eq body is (== a b) → returns '=='
        - (str-eq a b) where str-eq body is (string-eq a b) → returns 'string-eq'
        - (iri-eq a b) where iri-eq body is (string-eq (. a value) ...) → returns 'iri-eq'
          (not inlined because body isn't simple param comparison)
        """
        if isinstance(expr, SList) and len(expr) >= 1:
            head = expr[0]
            if isinstance(head, Symbol):
                # Check for -eq function call
                if head.name.endswith('-eq'):
                    # Check if this function inlines to native equality
                    if (self.function_registry and
                        self.function_registry.inlines_to_native_equality(head.name)):
                        return '=='

                    # Check if this function inlines to another -eq function
                    if self.function_registry:
                        inlined_eq = self._get_inlined_equality_func(head.name)
                        if inlined_eq:
                            return inlined_eq

                    return head.name
                # Check for == operator (native equality)
                if head.name == '==':
                    return '=='
            # Recurse
            for item in expr.items:
                result = self._find_eq_call_in_expr(item)
                if result:
                    return result
        return None

    def _get_inlined_equality_func(self, name: str) -> Optional[str]:
        """If function inlines to a simple equality call, return that function name.

        For example, if str-eq has body (string-eq a b), returns 'string-eq'.
        Returns None if the function doesn't inline to a simple equality.
        """
        if not self.function_registry:
            return None

        fn = self.function_registry.functions.get(name)
        if not fn or not fn.body or not fn.is_pure:
            return None

        if not self.function_registry.is_simple_inlinable(name):
            return None

        # Check if body is (some-eq-func param1 param2)
        body = fn.body
        if not isinstance(body, SList) or len(body) < 3:
            return None

        head = body[0]
        if not isinstance(head, Symbol):
            return None

        # Check if it's an equality-like function call on parameters
        if head.name == '==' or head.name.endswith('-eq'):
            arg1, arg2 = body[1], body[2]
            if isinstance(arg1, Symbol) and isinstance(arg2, Symbol):
                if arg1.name in fn.params and arg2.name in fn.params:
                    return head.name

        return None

    def _extract_union_equality_axioms(self, fn_form: SList, fn_body: SExpr,
                                        translator: Z3Translator) -> List:
        """Extract structural equality axioms for union equality functions.

        For term-eq with Term = (union (iri IRI) (blank BlankNode) (literal Literal)):

        Instead of a universally quantified axiom (which Z3 struggles with),
        we add ground axioms for the specific parameters a and b:

        1. If tags are different, a != b
        2. For each variant: if tags match variant i and helper-eq returns true/false,
           then a == b / a != b

        These ground axioms help Z3 prove (== $result (== a b)) without quantifiers.
        """
        axioms = []

        # Detect union equality function pattern
        detection = self._detect_union_equality_function(fn_form)
        if detection is None:
            return axioms

        param1_name, param2_name, union_type_name = detection

        # Get union type
        union_type = self.type_env.type_registry.get(union_type_name)
        if not isinstance(union_type, UnionType):
            return axioms

        # Extract helper-eq calls from the body
        helper_eqs = self._extract_helper_eq_calls_from_match(fn_body)

        # Get parameter variables
        a_var = translator.variables.get(param1_name)
        b_var = translator.variables.get(param2_name)
        if a_var is None or b_var is None:
            return axioms

        # Get or create union_tag function
        tag_func_name = "union_tag"
        if tag_func_name not in translator.variables:
            tag_func = z3.Function(tag_func_name, z3.IntSort(), z3.IntSort())
            translator.variables[tag_func_name] = tag_func
        else:
            tag_func = translator.variables[tag_func_name]

        # Constraint: union_tag must return valid variant indices
        # For a union with N variants, tag values must be in [0, N-1]
        num_variants = len(union_type.variants)
        axioms.append(tag_func(a_var) >= 0)
        axioms.append(tag_func(a_var) < num_variants)
        axioms.append(tag_func(b_var) >= 0)
        axioms.append(tag_func(b_var) < num_variants)

        # Axiom 1: Different tags <=> a != b (for same-type union values)
        # (union_tag(a) != union_tag(b)) <=> (a != b)
        # Forward: different tags means not equal
        axioms.append(z3.Implies(tag_func(a_var) != tag_func(b_var), a_var != b_var))
        # Reverse: if equal, must have same tags
        axioms.append(z3.Implies(a_var == b_var, tag_func(a_var) == tag_func(b_var)))

        # For each variant, add ground axioms connecting helper-eq to native equality
        for i, (variant_name, variant_type) in enumerate(union_type.variants.items()):
            tag_idx = translator.enum_values.get(variant_name,
                       translator.enum_values.get(f"'{variant_name}", i))

            # Get or create payload extraction function
            payload_func_name = f"union_payload_{variant_name}"
            if payload_func_name not in translator.variables:
                payload_func = z3.Function(payload_func_name, z3.IntSort(), z3.IntSort())
                translator.variables[payload_func_name] = payload_func
            else:
                payload_func = translator.variables[payload_func_name]

            # Find helper equality function for this variant
            helper_eq_name = helper_eqs.get(variant_name)
            if helper_eq_name:
                # Get payloads for a and b
                a_payload = payload_func(a_var)
                b_payload = payload_func(b_var)

                # Ground axiom: tags match variant i AND helper_eq(payloads) <=> a == b (when tags are i)
                tags_match_i = z3.And(tag_func(a_var) == tag_idx, tag_func(b_var) == tag_idx)

                # Determine helper_eq_result based on whether it's native == or a function call
                if helper_eq_name == '==':
                    # Native equality on payloads
                    helper_eq_result = (a_payload == b_payload)
                else:
                    # Get or create the helper-eq function
                    helper_func_key = f"fn_{helper_eq_name}_2"
                    if helper_func_key not in translator.variables:
                        helper_func = z3.Function(helper_func_key, z3.IntSort(), z3.IntSort(), z3.BoolSort())
                        translator.variables[helper_func_key] = helper_func
                    else:
                        helper_func = translator.variables[helper_func_key]
                    helper_eq_result = helper_func(a_payload, b_payload)

                # Forward: If both tags are variant i and helper-eq is true, then a == b
                axioms.append(z3.Implies(z3.And(tags_match_i, helper_eq_result), a_var == b_var))

                # Forward: If both tags are variant i and helper-eq is false, then a != b
                axioms.append(z3.Implies(z3.And(tags_match_i, z3.Not(helper_eq_result)), a_var != b_var))

                # Reverse: If a == b and tags are variant i, then helper-eq must be true
                axioms.append(z3.Implies(z3.And(a_var == b_var, tag_func(a_var) == tag_idx),
                                         helper_eq_result))

                # Reverse: If a != b and tags are variant i (and b has same tag), then helper-eq must be false
                axioms.append(z3.Implies(z3.And(a_var != b_var, tags_match_i),
                                         z3.Not(helper_eq_result)))

        return axioms


__all__ = ['UnionHandlingMixin']
