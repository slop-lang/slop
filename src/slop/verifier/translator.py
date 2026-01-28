"""
Z3 Translator - Converts SLOP AST expressions to Z3 constraints.

This module provides the Z3Translator class that transforms SLOP expressions
into Z3 SMT solver constraints for verification purposes.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Tuple, Any, TYPE_CHECKING

from slop.parser import SList, Symbol, String, Number, is_form
from slop.types import (
    Type, PrimitiveType, RangeType, RangeBounds, RecordType, EnumType,
    OptionType, ResultType, PtrType, FnType, UNKNOWN, ListType, ArrayType,
    UnionType,
)

from .z3_setup import Z3_AVAILABLE, z3
from .types import MinimalTypeEnv, ImportedDefinitions

if TYPE_CHECKING:
    from slop.parser import SExpr
    from .registry import FunctionRegistry


class Z3Translator:
    """Translates SLOP AST expressions to Z3 constraints"""

    def __init__(self, type_env: MinimalTypeEnv, filename: str = "<unknown>",
                 function_registry: Optional[FunctionRegistry] = None,
                 imported_defs: Optional[ImportedDefinitions] = None,
                 use_array_encoding: bool = False,
                 use_seq_encoding: bool = False):
        if not Z3_AVAILABLE:
            raise RuntimeError("Z3 is not available")
        self.type_env = type_env
        self.filename = filename
        self.function_registry = function_registry
        self.imported_defs = imported_defs or ImportedDefinitions()
        self.variables: Dict[str, z3.ExprRef] = {}
        self.constraints: List[z3.BoolRef] = []
        self.enum_values: Dict[str, int] = {}  # 'Fizz' -> 0, etc.
        # Array encoding for lists: maps list variable name to (array, length) pair
        self.use_array_encoding = use_array_encoding
        self.list_arrays: Dict[str, Tuple[z3.ArrayRef, z3.ArithRef]] = {}
        self._array_counter = 0  # Counter for unique array names
        # Sequence encoding for lists: maps list variable name to Seq variable
        # Seq encoding enables proper reasoning about list contents via Z3's native Sequence theory
        self.use_seq_encoding = use_seq_encoding
        self.list_seqs: Dict[str, z3.SeqRef] = {}
        self._seq_counter = 0  # Counter for unique seq names
        self._build_enum_map()

    def _build_enum_map(self):
        """Build mapping from enum/union variant names to integer values"""
        # Build from local type registry
        for typ in self.type_env.type_registry.values():
            if isinstance(typ, EnumType):
                for i, variant in enumerate(typ.variants):
                    self.enum_values[variant] = i
                    self.enum_values[f"'{variant}"] = i
            elif isinstance(typ, UnionType):
                # Union variants also need indices for match expressions
                for i, variant in enumerate(typ.variants.keys()):
                    self.enum_values[variant] = i
                    self.enum_values[f"'{variant}"] = i

        # Also build from imported types
        for typ in self.imported_defs.types.values():
            if isinstance(typ, EnumType):
                for i, variant in enumerate(typ.variants):
                    if variant not in self.enum_values:
                        self.enum_values[variant] = i
                        self.enum_values[f"'{variant}"] = i
            elif isinstance(typ, UnionType):
                for i, variant in enumerate(typ.variants.keys()):
                    if variant not in self.enum_values:
                        self.enum_values[variant] = i
                        self.enum_values[f"'{variant}"] = i

    # ========================================================================
    # Array Encoding for Lists
    # ========================================================================

    def _create_list_array(self, name: str) -> Tuple[z3.ArrayRef, z3.ArithRef]:
        """Create a Z3 array and length variable for a list.

        Lists are modeled as a pair: (Array(Int -> Int), Int length).
        The array stores elements as integers (pointers/ids), and the
        length tracks how many elements are valid.

        Returns:
            Tuple of (array variable, length variable)
        """
        # Return existing array if already created
        if name in self.list_arrays:
            return self.list_arrays[name]

        self._array_counter += 1
        arr_name = f"_arr_{name}_{self._array_counter}"
        len_name = f"_len_{name}_{self._array_counter}"

        # Create array from Int to Int (indices to element pointers)
        arr = z3.Array(arr_name, z3.IntSort(), z3.IntSort())
        length = z3.Int(len_name)

        # Length is always non-negative
        self.constraints.append(length >= 0)

        self.list_arrays[name] = (arr, length)
        return arr, length

    def _get_list_array(self, name: str) -> Optional[Tuple[z3.ArrayRef, z3.ArithRef]]:
        """Get the array and length for a list variable."""
        return self.list_arrays.get(name)

    # ========================================================================
    # Sequence Encoding for Lists (Z3 Seq Theory)
    # ========================================================================

    def _create_list_seq(self, name: str, elem_sort: Optional[z3.SortRef] = None) -> z3.SeqRef:
        """Create a Z3 Seq variable for a list.

        Sequences provide native support for list operations:
        - z3.Length(seq) - length of sequence
        - z3.At(seq, i) - element at index i (returns Unit sequence)
        - z3.Concat(seq1, seq2) - concatenation
        - z3.Unit(elem) - singleton sequence
        - z3.Empty(sort) - empty sequence

        Args:
            name: Variable name for the sequence
            elem_sort: Element sort (defaults to IntSort for pointer/id representation)

        Returns:
            Z3 Seq variable
        """
        if name in self.list_seqs:
            return self.list_seqs[name]

        self._seq_counter += 1
        seq_name = f"_seq_{name}_{self._seq_counter}"

        # Default to Int elements (representing pointers/ids)
        if elem_sort is None:
            elem_sort = z3.IntSort()

        seq_sort = z3.SeqSort(elem_sort)
        seq = z3.Const(seq_name, seq_sort)

        self.list_seqs[name] = seq
        return seq

    def _get_list_seq(self, name: str) -> Optional[z3.SeqRef]:
        """Get the Seq variable for a list."""
        return self.list_seqs.get(name)

    def _translate_list_len_seq(self, lst_expr: SExpr) -> Optional[z3.ArithRef]:
        """Translate (list-len lst) using Seq encoding.

        Returns z3.Length(seq) for the sequence.
        """
        if isinstance(lst_expr, Symbol):
            lst_name = lst_expr.name
            if lst_name in self.list_seqs:
                return z3.Length(self.list_seqs[lst_name])
        return None

    def _translate_list_ref_seq(self, expr: SList) -> Optional[z3.ExprRef]:
        """Translate (list-ref lst i) using Seq encoding.

        Returns the element at index i. Note that z3.At returns a unit sequence,
        so we extract the actual element for integer sequences.
        """
        if len(expr) < 3:
            return None

        lst_expr = expr[1]
        idx_expr = expr[2]

        # Check for Seq encoding first
        if isinstance(lst_expr, Symbol):
            lst_name = lst_expr.name
            if lst_name in self.list_seqs:
                seq = self.list_seqs[lst_name]
                idx = self.translate_expr(idx_expr)
                if idx is None:
                    return None
                # z3.At returns a unit sequence; extract the element
                # For IntSort elements, use SubSeq then IndexOf trick
                # Actually, z3.At on SeqSort<Int> returns Seq<Int>, need z3.Nth
                # z3.Nth(seq, i) extracts the i-th element directly
                return seq[idx]  # seq[i] is syntactic sugar for z3.Nth(seq, i)

        return None

    def _seq_push(self, seq: z3.SeqRef, elem: z3.ExprRef) -> z3.SeqRef:
        """Model list-push as sequence concatenation.

        (list-push lst elem) becomes Concat(lst, Unit(elem))
        """
        return z3.Concat(seq, z3.Unit(elem))

    def _seq_empty(self, elem_sort: Optional[z3.SortRef] = None) -> z3.SeqRef:
        """Create an empty sequence.

        Models (list-new arena Type).
        """
        if elem_sort is None:
            elem_sort = z3.IntSort()
        return z3.Empty(z3.SeqSort(elem_sort))

    def _get_or_create_collection_seq(self, coll_expr: SExpr) -> Optional[z3.SeqRef]:
        """Get or create a Seq for a collection expression.

        Handles:
        - Simple symbols: $result, items, etc.
        - Field access: (. delta triples), (. obj field)

        For field access, creates a Seq with a name like "_field_delta_triples".
        """
        if isinstance(coll_expr, Symbol):
            coll_name = coll_expr.name
            if coll_name == '$result':
                return self.list_seqs.get('$result')
            elif coll_name in self.list_seqs:
                return self.list_seqs[coll_name]
            else:
                # Create a new Seq for this collection
                return self._create_list_seq(coll_name)

        # Handle field access: (. obj field)
        if isinstance(coll_expr, SList) and is_form(coll_expr, '.') and len(coll_expr) >= 3:
            obj_expr = coll_expr[1]
            field_expr = coll_expr[2]

            # Build a unique name for this field access
            obj_name = obj_expr.name if isinstance(obj_expr, Symbol) else "_obj"
            field_name = field_expr.name if isinstance(field_expr, Symbol) else "_field"
            seq_name = f"_field_{obj_name}_{field_name}"

            if seq_name in self.list_seqs:
                return self.list_seqs[seq_name]
            else:
                return self._create_list_seq(seq_name)

        # Handle function calls: (fn-name args...)
        # These are modeled as uninterpreted functions returning collections
        if isinstance(coll_expr, SList) and len(coll_expr) >= 1:
            head = coll_expr[0]
            if isinstance(head, Symbol) and self._is_function_call(coll_expr):
                # Build unique name from function and args
                fn_name = head.name
                args_str = "_".join(
                    arg.name if isinstance(arg, Symbol) else str(id(arg))
                    for arg in coll_expr.items[1:]
                )
                seq_name = f"_fn_{fn_name}_{args_str}" if args_str else f"_fn_{fn_name}"

                if seq_name in self.list_seqs:
                    return self.list_seqs[seq_name]
                else:
                    return self._create_list_seq(seq_name)

        return None

    def _is_function_call(self, expr: SExpr) -> bool:
        """Check if expression is a function call that could return a collection.

        This excludes special forms and operators that are handled elsewhere.
        """
        if not isinstance(expr, SList) or len(expr) < 1:
            return False
        head = expr[0]
        if not isinstance(head, Symbol):
            return False
        # Exclude special forms and operators
        special_forms = {
            'if', 'let', 'match', 'and', 'or', 'not', '.',
            'forall', 'exists', 'implies', 'quote',
            '+', '-', '*', '/', '%',
            '==', '!=', '>', '<', '>=', '<=',
        }
        if head.name.startswith('@') or head.name in special_forms:
            return False
        return True

    def _translate_forall_collection(self, expr: SList) -> Optional[z3.BoolRef]:
        """Translate (forall (elem coll) body) to a quantified formula.

        This is the collection-bound forall syntax:
            (forall (t $result) (is-valid t))
            (forall (dt (. delta triples)) (pred dt))

        Expansion:
            ForAll i: 0 <= i < Length(seq) => body[t/seq[i]]

        Args:
            expr: The forall expression (forall (elem coll) body)

        Returns:
            Z3 ForAll expression or None if not a collection-bound pattern
        """
        if len(expr) < 3:
            return None

        binding = expr[1]
        body = expr[2]

        # Check for collection-bound pattern: (elem collection)
        if not isinstance(binding, SList) or len(binding) != 2:
            return None

        # First element must be a symbol (the element variable)
        if not isinstance(binding[0], Symbol):
            return None

        elem_var = binding[0].name
        coll_expr = binding[1]

        # Check if this is a collection reference (not a type annotation)
        if isinstance(coll_expr, Symbol):
            coll_name = coll_expr.name
            # Skip if it looks like a type (uppercase first letter, not $result)
            if coll_name != '$result' and coll_name[0].isupper():
                return None
        elif isinstance(coll_expr, SList):
            # Allow field access (. obj field) or function calls (fn args...)
            if not (is_form(coll_expr, '.') or self._is_function_call(coll_expr)):
                return None
        else:
            return None

        # Get the sequence for the collection
        seq = self._get_or_create_collection_seq(coll_expr)
        if seq is None:
            return None

        # Create index variable
        idx_var = z3.Int(f'_idx_{elem_var}')

        # Get the element at index
        elem_at_idx = seq[idx_var]  # z3.Nth(seq, idx_var)

        # Save old binding if any
        old_binding = self.variables.get(elem_var)

        try:
            # Bind elem_var to the element expression
            self.variables[elem_var] = elem_at_idx

            # Translate the body with elem_var bound
            body_z3 = self.translate_expr(body)
            if body_z3 is None or not z3.is_bool(body_z3):
                return None

            # ForAll i: 0 <= i < Length(seq) => body
            return z3.ForAll([idx_var],
                z3.Implies(
                    z3.And(idx_var >= 0, idx_var < z3.Length(seq)),
                    body_z3
                )
            )
        finally:
            # Restore old binding
            if old_binding is not None:
                self.variables[elem_var] = old_binding
            elif elem_var in self.variables:
                del self.variables[elem_var]

    def _translate_exists_collection(self, expr: SList) -> Optional[z3.BoolRef]:
        """Translate (exists (elem coll) body) to existential quantifier.

        Similar to forall but uses existential:
            Exists i: 0 <= i < Length(seq) && body[elem/seq[i]]

        Handles both simple symbols and field access collections.
        """
        if len(expr) < 3:
            return None

        binding = expr[1]
        body = expr[2]

        # Check for collection-bound pattern
        if not isinstance(binding, SList) or len(binding) != 2:
            return None

        if not isinstance(binding[0], Symbol):
            return None

        elem_var = binding[0].name
        coll_expr = binding[1]

        # Check if this is a collection reference (not a type annotation)
        if isinstance(coll_expr, Symbol):
            coll_name = coll_expr.name
            if coll_name != '$result' and coll_name[0].isupper():
                return None
        elif isinstance(coll_expr, SList):
            # Allow field access (. obj field) or function calls (fn args...)
            if not (is_form(coll_expr, '.') or self._is_function_call(coll_expr)):
                return None
        else:
            return None

        # Get the sequence
        seq = self._get_or_create_collection_seq(coll_expr)
        if seq is None:
            return None

        idx_var = z3.Int(f'_idx_{elem_var}')
        elem_at_idx = seq[idx_var]

        old_binding = self.variables.get(elem_var)

        try:
            self.variables[elem_var] = elem_at_idx

            body_z3 = self.translate_expr(body)
            if body_z3 is None or not z3.is_bool(body_z3):
                return None

            # Exists i: 0 <= i < Length(seq) && body
            return z3.Exists([idx_var],
                z3.And(
                    idx_var >= 0,
                    idx_var < z3.Length(seq),
                    body_z3
                )
            )
        finally:
            if old_binding is not None:
                self.variables[elem_var] = old_binding
            elif elem_var in self.variables:
                del self.variables[elem_var]

    def _translate_list_ref(self, expr: SList) -> Optional[z3.ExprRef]:
        """Translate (list-ref lst i) to z3.Select(arr, i).

        Pattern: (list-ref list index)
        Returns the element at the given index in the list.
        """
        if len(expr) < 3:
            return None

        lst_expr = expr[1]
        idx_expr = expr[2]

        # Translate the index
        idx = self.translate_expr(idx_expr)
        if idx is None:
            return None

        # Get the list - check if it's a known list variable with array encoding
        if isinstance(lst_expr, Symbol):
            lst_name = lst_expr.name
            if lst_name in self.list_arrays:
                arr, _ = self.list_arrays[lst_name]
                return z3.Select(arr, idx)

        # Fall back to translating the list expression
        lst = self.translate_expr(lst_expr)
        if lst is None:
            return None

        # If we have array encoding, lst might be an array
        if z3.is_array(lst):
            return z3.Select(lst, idx)

        # Fall back to uninterpreted function for element access
        func_name = "list_ref"
        if func_name not in self.variables:
            func = z3.Function(func_name, z3.IntSort(), z3.IntSort(), z3.IntSort())
            self.variables[func_name] = func
        else:
            func = self.variables[func_name]
        return func(lst, idx)

    def _translate_forall(self, expr: SList) -> Optional[z3.BoolRef]:
        """Translate (forall (var Type) body) to z3.ForAll.

        Patterns:
        - (forall (i Int) body) - explicit type annotation
        - (forall i body) - inferred type (defaults to Int)

        The body is translated with the bound variable in scope.
        """
        if len(expr) < 3:
            return None

        binding = expr[1]
        body = expr[2]

        # Extract variable name
        var_name: Optional[str] = None
        if isinstance(binding, SList) and len(binding) >= 1:
            # Pattern: (forall (i Int) body)
            if isinstance(binding[0], Symbol):
                var_name = binding[0].name
        elif isinstance(binding, Symbol):
            # Pattern: (forall i body)
            var_name = binding.name

        if var_name is None:
            return None

        # Create bound variable (always Int for now)
        bound_var = z3.Int(var_name)

        # Save old binding if any
        old_binding = self.variables.get(var_name)

        try:
            # Bind the variable for body translation
            self.variables[var_name] = bound_var

            # Translate the body
            body_z3 = self.translate_expr(body)
            if body_z3 is None or not z3.is_bool(body_z3):
                return None

            return z3.ForAll([bound_var], body_z3)
        finally:
            # Restore old binding
            if old_binding is not None:
                self.variables[var_name] = old_binding
            elif var_name in self.variables:
                del self.variables[var_name]

    def _translate_exists(self, expr: SList) -> Optional[z3.BoolRef]:
        """Translate (exists (var Type) body) to z3.Exists.

        Similar to forall but uses existential quantifier.
        """
        if len(expr) < 3:
            return None

        binding = expr[1]
        body = expr[2]

        # Extract variable name
        var_name: Optional[str] = None
        if isinstance(binding, SList) and len(binding) >= 1:
            if isinstance(binding[0], Symbol):
                var_name = binding[0].name
        elif isinstance(binding, Symbol):
            var_name = binding.name

        if var_name is None:
            return None

        # Create bound variable
        bound_var = z3.Int(var_name)

        # Save old binding if any
        old_binding = self.variables.get(var_name)

        try:
            # Bind the variable for body translation
            self.variables[var_name] = bound_var

            # Translate the body
            body_z3 = self.translate_expr(body)
            if body_z3 is None or not z3.is_bool(body_z3):
                return None

            return z3.Exists([bound_var], body_z3)
        finally:
            # Restore old binding
            if old_binding is not None:
                self.variables[var_name] = old_binding
            elif var_name in self.variables:
                del self.variables[var_name]

    def _translate_implies(self, expr: SList) -> Optional[z3.BoolRef]:
        """Translate (implies antecedent consequent) to z3.Implies."""
        if len(expr) < 3:
            return None

        antecedent = self.translate_expr(expr[1])
        consequent = self.translate_expr(expr[2])

        if antecedent is None or consequent is None:
            return None

        if not z3.is_bool(antecedent) or not z3.is_bool(consequent):
            return None

        return z3.Implies(antecedent, consequent)

    def _expand_all_triples_have_predicate(self, expr: SList) -> Optional[z3.BoolRef]:
        """Expand (all-triples-have-predicate lst pred) to a quantified formula.

        Expansion:
        (forall (i Int)
          (implies (and (>= i 0) (< i (list-len lst)))
            (== (field_predicate (list-ref lst i)) pred_hash)))

        For array encoding, this becomes:
        (forall (i Int)
          (implies (and (>= i 0) (< i length))
            (== (field_predicate (Select arr i)) pred_hash)))
        """
        if len(expr) < 3:
            return None

        lst_expr = expr[1]
        pred_expr = expr[2]

        # Create bound variable for index
        i = z3.Int("_i_athp")

        # Get list length
        if isinstance(lst_expr, Symbol):
            lst_name = lst_expr.name
            if lst_name in self.list_arrays:
                # Array encoding: use stored length
                arr, length = self.list_arrays[lst_name]

                # Get predicate hash for comparison
                pred_hash: Optional[z3.ExprRef] = None
                if isinstance(pred_expr, Symbol):
                    # Look up constant value
                    if pred_expr.name in self.imported_defs.constants:
                        const = self.imported_defs.constants[pred_expr.name]
                        if isinstance(const.value, str):
                            pred_hash = z3.IntVal(hash(const.value) % (2**31))
                    elif pred_expr.name in self.variables:
                        pred_hash = self.variables[pred_expr.name]
                elif isinstance(pred_expr, String):
                    pred_hash = z3.IntVal(hash(pred_expr.value) % (2**31))

                if pred_hash is None:
                    pred_hash = self.translate_expr(pred_expr)
                    if pred_hash is None:
                        return None

                # Get or create predicate accessor function
                func_name = "field_predicate"
                if func_name not in self.variables:
                    func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                    self.variables[func_name] = func
                else:
                    func = self.variables[func_name]

                # Build the quantified formula
                element = z3.Select(arr, i)
                element_pred = func(element)

                # The condition: 0 <= i < length implies element has predicate
                condition = z3.And(i >= 0, i < length)
                body = z3.Implies(condition, element_pred == pred_hash)

                return z3.ForAll([i], body)

        # Fall back to uninterpreted function for non-array case
        # This returns Bool since all-triples-have-predicate returns Bool
        lst = self.translate_expr(lst_expr)
        pred = self.translate_expr(pred_expr)
        if lst is None or pred is None:
            return None

        func_key = "fn_all-triples-have-predicate_2"
        if func_key not in self.variables:
            func = z3.Function(func_key, z3.IntSort(), z3.IntSort(), z3.BoolSort())
            self.variables[func_key] = func
        else:
            func = self.variables[func_key]
        return func(lst, pred)

    def declare_variable(self, name: str, typ: Type) -> z3.ExprRef:
        """Create Z3 variable with appropriate sort and add range constraints"""
        if name in self.variables:
            return self.variables[name]

        var: z3.ExprRef

        if isinstance(typ, PrimitiveType):
            if typ.name == 'Bool':
                var = z3.Bool(name)
            elif typ.name in ('Int', 'I8', 'I16', 'I32', 'I64', 'U8', 'U16', 'U32', 'U64'):
                var = z3.Int(name)
                # Add unsigned constraints for unsigned types
                if typ.name.startswith('U'):
                    self.constraints.append(var >= 0)
            elif typ.name in ('Float', 'F32'):
                var = z3.Real(name)
            else:
                # Default to Int for other primitives
                var = z3.Int(name)

        elif isinstance(typ, RangeType):
            var = z3.Int(name)
            self._add_range_constraints(var, typ.bounds)

        elif isinstance(typ, PtrType):
            # Model pointers as integers (addresses)
            var = z3.Int(name)
            # Pointers are non-negative
            self.constraints.append(var >= 0)

        else:
            # For complex types, use Int as placeholder
            var = z3.Int(name)

        self.variables[name] = var
        return var

    def _add_range_constraints(self, var: z3.ArithRef, bounds: RangeBounds):
        """Add constraints for range type bounds"""
        if bounds.min_val is not None:
            self.constraints.append(var >= bounds.min_val)
        if bounds.max_val is not None:
            self.constraints.append(var <= bounds.max_val)

    def translate_expr(self, expr: SExpr) -> Optional[z3.ExprRef]:
        """Translate SLOP expression to Z3 expression"""
        # Normalize native parser infix-in-parens pattern: ((a) op (b)) -> (op (a) (b))
        # Native parser can produce ((list-len ...) == 0) instead of (== (list-len ...) 0)
        if isinstance(expr, SList) and len(expr) == 3:
            mid = expr[1]
            if isinstance(mid, Symbol) and mid.name in ('==', '!=', '>', '<', '>=', '<=', 'and', 'or'):
                # Convert infix to prefix
                expr = SList([mid, expr[0], expr[2]])

        if isinstance(expr, Number):
            if isinstance(expr.value, float):
                return z3.RealVal(expr.value)
            return z3.IntVal(int(expr.value))

        if isinstance(expr, String):
            # Model string as unique integer ID with known length
            # Use a hash to create a unique identifier
            str_id = hash(expr.value) % (2**31)
            str_var = z3.IntVal(str_id)
            # Track string length for this specific string value
            func_name = "string_len"
            if func_name not in self.variables:
                func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                self.variables[func_name] = func
            else:
                func = self.variables[func_name]
            # Add axiom: string_len(this_string_id) == actual_length
            self.constraints.append(func(str_var) == z3.IntVal(len(expr.value)))
            return str_var

        if isinstance(expr, Symbol):
            return self._translate_symbol(expr)

        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                op = head.name

                # Boolean literals
                if op == 'true':
                    return z3.BoolVal(True)
                if op == 'false':
                    return z3.BoolVal(False)

                # Comparison operators
                if op in ('>', '<', '>=', '<=', '==', '!='):
                    return self._translate_comparison(expr)

                # Arithmetic operators
                if op in ('+', '-', '*', '/', '%'):
                    return self._translate_arithmetic(expr)

                # Boolean operators
                if op in ('and', 'or', 'not'):
                    return self._translate_boolean(expr)

                # Field access
                if op == '.':
                    return self._translate_field_access(expr)

                # List length - equivalent to (. list len)
                if op == 'list-len':
                    if len(expr) >= 2:
                        lst_expr = expr[1]
                        # Check for Seq encoding first (preferred)
                        if self.use_seq_encoding:
                            seq_result = self._translate_list_len_seq(lst_expr)
                            if seq_result is not None:
                                return seq_result
                        # Check for array encoding
                        if self.use_array_encoding and isinstance(lst_expr, Symbol):
                            lst_name = lst_expr.name
                            if lst_name in self.list_arrays:
                                _, length = self.list_arrays[lst_name]
                                return length
                        lst = self.translate_expr(lst_expr)
                        if lst is None:
                            return None
                        # Use the same field accessor pattern as _translate_field_access
                        func_name = "field_len"
                        if func_name not in self.variables:
                            func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                            self.variables[func_name] = func
                        else:
                            func = self.variables[func_name]
                        result = func(lst)
                        # List length is always non-negative
                        self.constraints.append(result >= 0)
                        return result
                    return None

                # List element access (array/seq encoding)
                if op == 'list-ref':
                    # Try Seq encoding first
                    if self.use_seq_encoding:
                        seq_result = self._translate_list_ref_seq(expr)
                        if seq_result is not None:
                            return seq_result
                    return self._translate_list_ref(expr)

                # Quantifiers
                if op == 'forall':
                    # Try collection-bound pattern first with Seq encoding
                    if self.use_seq_encoding:
                        coll_result = self._translate_forall_collection(expr)
                        if coll_result is not None:
                            return coll_result
                    return self._translate_forall(expr)

                if op == 'exists':
                    # Try collection-bound pattern first with Seq encoding
                    if self.use_seq_encoding:
                        coll_result = self._translate_exists_collection(expr)
                        if coll_result is not None:
                            return coll_result
                    return self._translate_exists(expr)

                # Implication
                if op == 'implies':
                    return self._translate_implies(expr)

                # all-triples-have-predicate expansion
                if op == 'all-triples-have-predicate':
                    if self.use_array_encoding:
                        return self._expand_all_triples_have_predicate(expr)
                    # Fall through to function call handling

                # String length
                if op == 'string-len':
                    if len(expr) >= 2:
                        arg = expr[1]
                        # Handle string literals directly - return actual length
                        if isinstance(arg, String):
                            return z3.IntVal(len(arg.value))

                        s = self.translate_expr(arg)
                        if s is None:
                            return None
                        func_name = "string_len"
                        if func_name not in self.variables:
                            func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                            self.variables[func_name] = func
                        else:
                            func = self.variables[func_name]
                        result = func(s)
                        # String length is always non-negative
                        self.constraints.append(result >= 0)
                        return result
                    return None

                # is-form - check if SExpr is a specific form type
                if op == 'is-form':
                    if len(expr) >= 3:
                        form_expr = self.translate_expr(expr[1])
                        # The second arg is a string literal for the form name
                        # Model as uninterpreted function: form_type(expr) == form_name_hash
                        if form_expr is None:
                            return None
                        func_name = "form_type"
                        if func_name not in self.variables:
                            func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                            self.variables[func_name] = func
                        else:
                            func = self.variables[func_name]
                        # Get form name and hash it for comparison
                        form_name = expr[2]
                        if isinstance(form_name, String):
                            name_hash = hash(form_name.value) % (2**31)
                        else:
                            name_hash = 0
                        return func(form_expr) == z3.IntVal(name_hash)
                    return None

                # Pointer dereference - pass through to inner expression
                if op == 'deref':
                    if len(expr) >= 2:
                        return self.translate_expr(expr[1])
                    return None

                # nil constant
                if op == 'nil':
                    return z3.IntVal(0)  # nil is address 0

                # Quote form - (quote x) is equivalent to 'x
                if op == 'quote' and len(expr) >= 2:
                    inner = expr[1]
                    if isinstance(inner, Symbol):
                        # Treat as quoted enum variant
                        name = inner.name
                        if name in self.enum_values:
                            return z3.IntVal(self.enum_values[name])
                        # Try with quote prefix
                        quoted_name = f"'{name}"
                        if quoted_name in self.enum_values:
                            return z3.IntVal(self.enum_values[quoted_name])
                    # If not found in enums, return the translated inner expression
                    return self.translate_expr(inner)

                # Control flow - path sensitive analysis
                if op == 'if':
                    return self._translate_if(expr)

                if op == 'cond':
                    return self._translate_cond(expr)

                if op == 'match':
                    return self._translate_match(expr)

                # Cast is a type-level operation - just translate the inner expression
                if op == 'cast' and len(expr) >= 3:
                    return self.translate_expr(expr[2])

                # do block - value is the last expression
                if op == 'do' and len(expr) >= 2:
                    # The value of a do block is its last expression
                    return self.translate_expr(expr.items[-1])

                # let binding - declare variables and translate body
                if op == 'let' and len(expr) >= 3:
                    return self._translate_let(expr)

                # Handle potential user-defined function calls
                # This is a fallback for functions not handled above
                return self._translate_function_call(expr)

        return None

    def _translate_symbol(self, sym: Symbol) -> Optional[z3.ExprRef]:
        """Translate a symbol reference"""
        name = sym.name

        # Quoted enum variant: 'Fizz -> IntVal(0)
        if name.startswith("'"):
            if name in self.enum_values:
                return z3.IntVal(self.enum_values[name])
            # Try without quote prefix
            variant = name[1:]
            if variant in self.enum_values:
                return z3.IntVal(self.enum_values[variant])

        # Special variable for postconditions
        if name == '$result':
            return self.variables.get('$result')

        # Boolean literals
        if name == 'true':
            return z3.BoolVal(True)
        if name == 'false':
            return z3.BoolVal(False)
        if name == 'nil':
            return z3.IntVal(0)

        # Check imported constants
        if name in self.imported_defs.constants:
            const = self.imported_defs.constants[name]
            if isinstance(const.value, (int, float)):
                if isinstance(const.value, float):
                    return z3.RealVal(const.value)
                return z3.IntVal(int(const.value))
            elif isinstance(const.value, str):
                # For string constants, use a hash as a unique identifier
                return z3.IntVal(hash(const.value) % (2**31))
            # If value is a symbol name, try to look it up
            elif const.value is not None:
                return z3.IntVal(hash(str(const.value)) % (2**31))

        # Shorthand dot notation: t.field -> (. t field)
        if '.' in name and not name.startswith('.'):
            parts = name.split('.', 1)
            obj_name, field_name = parts
            # Get the object variable
            obj = self._translate_symbol(Symbol(obj_name))
            if obj is None:
                return None
            # Translate as field access using the same logic as _translate_field_access
            return self._translate_field_for_obj(obj, field_name)

        # Look up in variables
        if name in self.variables:
            return self.variables[name]

        # Try to look up type and create variable
        typ = self.type_env.lookup_var(name)
        if typ:
            return self.declare_variable(name, typ)

        return None

    def _translate_comparison(self, expr: SList) -> Optional[z3.BoolRef]:
        """Translate comparison expression"""
        if len(expr) < 3:
            return None

        op = expr[0].name if isinstance(expr[0], Symbol) else None
        left = self.translate_expr(expr[1])
        right = self.translate_expr(expr[2])

        if left is None or right is None:
            return None

        # For equality/inequality, handle sort mismatches gracefully
        if op in ('==', '!='):
            left_is_bool = z3.is_bool(left)
            right_is_bool = z3.is_bool(right)

            # If sorts match, direct comparison works
            if left_is_bool == right_is_bool:
                return left == right if op == '==' else left != right

            # Sort mismatch: coerce Int to Bool (non-zero = true)
            if left_is_bool and not right_is_bool:
                right = right != 0
            elif right_is_bool and not left_is_bool:
                left = left != 0

            return left == right if op == '==' else left != right

        # Arithmetic comparisons require matching numeric sorts
        if op == '>':
            return left > right
        if op == '<':
            return left < right
        if op == '>=':
            return left >= right
        if op == '<=':
            return left <= right

        return None

    def _translate_arithmetic(self, expr: SList) -> Optional[z3.ArithRef]:
        """Translate arithmetic expression"""
        if len(expr) < 3:
            return None

        op = expr[0].name if isinstance(expr[0], Symbol) else None
        left = self.translate_expr(expr[1])
        right = self.translate_expr(expr[2])

        if left is None or right is None:
            return None

        if op == '+':
            return left + right
        if op == '-':
            return left - right
        if op == '*':
            return left * right
        if op == '/':
            # Add constraint that divisor is non-zero
            if isinstance(right, z3.ArithRef):
                self.constraints.append(right != 0)
            return left / right
        if op == '%':
            # Add constraint that divisor is non-zero
            if isinstance(right, z3.ArithRef):
                self.constraints.append(right != 0)
            return left % right

        return None

    def _translate_boolean(self, expr: SList) -> Optional[z3.BoolRef]:
        """Translate boolean expression"""
        op = expr[0].name if isinstance(expr[0], Symbol) else None

        if op == 'not' and len(expr) >= 2:
            arg = self.translate_expr(expr[1])
            if arg is not None and z3.is_bool(arg):
                return z3.Not(arg)
            return None

        if op == 'and' and len(expr) >= 3:
            args = [self.translate_expr(e) for e in expr.items[1:]]
            # Filter out None and non-bool args
            bool_args = [a for a in args if a is not None and z3.is_bool(a)]
            if len(bool_args) == len(args):  # All args translated to bool
                return z3.And(*bool_args)
            return None

        if op == 'or' and len(expr) >= 3:
            args = [self.translate_expr(e) for e in expr.items[1:]]
            # Filter out None and non-bool args
            bool_args = [a for a in args if a is not None and z3.is_bool(a)]
            if len(bool_args) == len(args):  # All args translated to bool
                return z3.Or(*bool_args)
            return None

        return None

    def _translate_field_access(self, expr: SList) -> Optional[z3.ExprRef]:
        """Translate field access (. obj field)"""
        if len(expr) < 3:
            return None

        # Model as uninterpreted function: field(obj)
        obj = self.translate_expr(expr[1])
        field_name = expr[2].name if isinstance(expr[2], Symbol) else None

        if obj is None or field_name is None:
            return None

        return self._translate_field_for_obj(obj, field_name)

    def _translate_field_for_obj(self, obj: z3.ExprRef, field_name: str) -> z3.ExprRef:
        """Translate field access given an already-translated object and field name"""
        # Create or get the field accessor function
        # Use Bool for fields that look boolean, Int otherwise
        func_name = f"field_{field_name}"
        is_bool_field = field_name.startswith('is-') or field_name.startswith('has-') or field_name in ('open', 'closed', 'valid', 'enabled', 'active')
        return_sort = z3.BoolSort() if is_bool_field else z3.IntSort()

        if func_name not in self.variables:
            func = z3.Function(func_name, z3.IntSort(), return_sort)
            self.variables[func_name] = func
        else:
            func = self.variables[func_name]

        return func(obj)

    def _translate_if(self, expr: SList) -> Optional[z3.ExprRef]:
        """Translate if expression to Z3 If()"""
        # (if cond then else)
        if len(expr) < 3:
            return None

        cond = self.translate_expr(expr[1])
        then_expr = self.translate_expr(expr[2])

        if cond is None or then_expr is None:
            return None

        # else is optional, defaults to 0
        if len(expr) > 3:
            else_expr = self.translate_expr(expr[3])
            if else_expr is None:
                return None
        else:
            # Default else to 0 (Unit)
            else_expr = z3.IntVal(0)

        return z3.If(cond, then_expr, else_expr)

    def _translate_cond(self, expr: SList) -> Optional[z3.ExprRef]:
        """Translate cond expression to nested Z3 If()"""
        # (cond (test1 e1) (test2 e2) (else default))
        # -> If(test1, e1, If(test2, e2, default))
        if len(expr) < 2:
            return None

        result: Optional[z3.ExprRef] = None

        # Process clauses in reverse order to build nested If
        for clause in reversed(expr.items[1:]):
            if not isinstance(clause, SList) or len(clause) < 2:
                continue

            first = clause[0]

            # Check for (else body) clause
            if isinstance(first, Symbol) and first.name == 'else':
                result = self.translate_expr(clause[1])
            else:
                # Regular clause: (test body)
                test = self.translate_expr(first)
                body = self.translate_expr(clause[1])

                if test is None or body is None:
                    return None

                if result is None:
                    # Last clause without else - use body as default
                    result = body
                else:
                    result = z3.If(test, body, result)

        return result

    def _translate_let(self, expr: SList) -> Optional[z3.ExprRef]:
        """Translate let binding: (let ((var1 val1) (var2 val2)...) body...)
        or (let (((mut var1) val1)...) body...) or (let ((mut var1 val1)...) body...)

        Declares bound variables and translates the body.
        The value of a let is the last expression in the body.
        """
        if len(expr) < 3:
            return None

        bindings = expr[1]
        if not isinstance(bindings, SList):
            return None

        # Process bindings - declare each variable
        for binding in bindings.items:
            if isinstance(binding, SList) and len(binding) >= 2:
                var_name = None
                init_value = None

                first = binding[0]
                if isinstance(first, Symbol):
                    if first.name == 'mut' and len(binding) >= 3:
                        # Pattern: (mut var value) - the SLOP pattern for mutable bindings
                        var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                        init_value = binding[2]
                    else:
                        # Pattern: (var value) - immutable binding
                        var_name = first.name
                        init_value = binding[1]
                elif isinstance(first, SList) and len(first) >= 2:
                    # Pattern: ((mut var) value) - alternative mutable pattern
                    if isinstance(first[0], Symbol) and first[0].name == 'mut':
                        var_name = first[1].name if isinstance(first[1], Symbol) else None
                    init_value = binding[1]

                if var_name and init_value is not None:
                    # Translate initial value
                    init_z3 = self.translate_expr(init_value)
                    if init_z3 is not None:
                        # Declare variable with same sort as initial value
                        if z3.is_bool(init_z3):
                            var = z3.Bool(var_name)
                        elif z3.is_real(init_z3):
                            var = z3.Real(var_name)
                        else:
                            var = z3.Int(var_name)
                        self.variables[var_name] = var
                        # Add constraint that variable equals initial value
                        self.constraints.append(var == init_z3)
                    else:
                        # Can't translate init value - just declare as Int
                        self.variables[var_name] = z3.Int(var_name)

        # Translate body expressions - value is the last one
        body_exprs = expr.items[2:]
        if not body_exprs:
            return None

        result = None
        for body_expr in body_exprs:
            result = self.translate_expr(body_expr)

        return result

    def _translate_match(self, expr: SList) -> Optional[z3.ExprRef]:
        """Translate match expression for union types.

        Pattern: (match expr ((tag1 var) body1) ((tag2 var) body2) ...)

        Translation strategy:
        - Track union discriminator with uninterpreted function union_tag(expr) -> Int
        - Each pattern (tag var) maps to tag index
        - Build nested z3.If() based on tag equality
        """
        if len(expr) < 3:
            return None

        scrutinee = self.translate_expr(expr[1])
        if scrutinee is None:
            return None

        # Get or create tag discriminator function
        tag_func_name = "union_tag"
        if tag_func_name not in self.variables:
            tag_func = z3.Function(tag_func_name, z3.IntSort(), z3.IntSort())
            self.variables[tag_func_name] = tag_func
        else:
            tag_func = self.variables[tag_func_name]

        tag_value = tag_func(scrutinee)

        # Process clauses in reverse to build nested If
        result: Optional[z3.ExprRef] = None
        for clause in reversed(expr.items[2:]):
            if not isinstance(clause, SList) or len(clause) < 2:
                continue

            pattern = clause[0]
            body = clause[1]

            if isinstance(pattern, Symbol) and pattern.name == '_':
                # Wildcard - default case
                result = self.translate_expr(body)
            elif isinstance(pattern, SList) and len(pattern) >= 1:
                # Handle pattern like (tag var) or ((quote tag) var)
                tag: Optional[str] = None
                tag_elem = pattern[0]
                if isinstance(tag_elem, Symbol):
                    tag = tag_elem.name.lstrip("'")
                elif is_form(tag_elem, 'quote') and len(tag_elem) >= 2:
                    # Handle quoted pattern: ((quote ok) _)
                    inner = tag_elem[1]
                    tag = inner.name if isinstance(inner, Symbol) else None

                if tag:
                    # Look up tag index from enum_values or hash it
                    tag_idx = self.enum_values.get(tag, self.enum_values.get(f"'{tag}", hash(tag) % 256))

                    # If the pattern has a variable binding, declare it
                    if len(pattern) >= 2 and isinstance(pattern[1], Symbol):
                        var_name = pattern[1].name
                        # Create uninterpreted function to extract the payload
                        payload_func_name = f"union_payload_{tag}"
                        if payload_func_name not in self.variables:
                            payload_func = z3.Function(payload_func_name, z3.IntSort(), z3.IntSort())
                            self.variables[payload_func_name] = payload_func
                        else:
                            payload_func = self.variables[payload_func_name]
                        # Bind the variable to the payload extraction
                        self.variables[var_name] = payload_func(scrutinee)

                    body_z3 = self.translate_expr(body)
                    if body_z3 is None:
                        return None

                    if result is None:
                        result = body_z3
                    else:
                        result = z3.If(tag_value == tag_idx, body_z3, result)
            elif isinstance(pattern, Symbol):
                # Simple tag pattern without variable binding
                tag = pattern.name
                tag_idx = self.enum_values.get(tag, self.enum_values.get(f"'{tag}", hash(tag) % 256))

                body_z3 = self.translate_expr(body)
                if body_z3 is None:
                    return None

                if result is None:
                    result = body_z3
                else:
                    result = z3.If(tag_value == tag_idx, body_z3, result)

        return result

    def _translate_with_substitution(self, expr: SExpr, param_map: Dict[str, 'z3.ExprRef']) -> Optional[z3.ExprRef]:
        """Translate expression with parameter substitution for function inlining.

        Args:
            expr: The expression to translate (function body)
            param_map: Map from parameter names to Z3 expressions

        This temporarily binds parameters to their argument values, translates
        the expression, then restores the original variable state.
        """
        # Save current variable bindings for parameters
        saved_vars: Dict[str, Optional[z3.ExprRef]] = {}
        for param, z3_val in param_map.items():
            saved_vars[param] = self.variables.get(param)
            self.variables[param] = z3_val

        try:
            # Translate the expression with substituted parameters
            result = self.translate_expr(expr)
            return result
        finally:
            # Restore original variable bindings
            for param, saved_val in saved_vars.items():
                if saved_val is None:
                    if param in self.variables:
                        del self.variables[param]
                else:
                    self.variables[param] = saved_val

    def _translate_function_call(self, expr: SList) -> Optional[z3.ExprRef]:
        """Translate user-defined function calls as uninterpreted functions.

        Strategy: model user-defined functions as uninterpreted functions.
        This allows Z3 to reason about their properties without knowing
        the implementation.

        For simple accessor functions (that just access a field), we inline
        the field access directly. This allows postconditions like
        (term-eq (triple-subject $result) subject) to be proven.
        """
        if len(expr) < 1:
            return None

        fn_name = expr[0].name if isinstance(expr[0], Symbol) else None
        if fn_name is None:
            return None

        # Try to inline simple accessor functions
        if self.function_registry and self.function_registry.is_simple_accessor(fn_name):
            accessor_info = self.function_registry.get_accessor_info(fn_name)
            if accessor_info and len(expr) >= 2:
                param_name, field_name = accessor_info
                # Translate the argument
                arg = self.translate_expr(expr[1])
                if arg is not None:
                    # Return field access on the argument
                    return self._translate_field_for_obj(arg, field_name)

        # Try to inline simple pure functions (e.g., iri-eq, blank-eq)
        if self.function_registry and self.function_registry.is_simple_inlinable(fn_name):
            fn_def = self.function_registry.functions[fn_name]
            if fn_def.body and len(fn_def.params) == len(expr.items) - 1:
                # Build parameter -> argument mapping
                param_map: Dict[str, z3.ExprRef] = {}
                all_args_translated = True
                for i, param in enumerate(fn_def.params):
                    arg_z3 = self.translate_expr(expr[i + 1])
                    if arg_z3 is None:
                        all_args_translated = False
                        break
                    param_map[param] = arg_z3

                if all_args_translated:
                    # Inline the function body with substituted parameters
                    result = self._translate_with_substitution(fn_def.body, param_map)
                    if result is not None:
                        return result
                    # Fall through to uninterpreted function if inlining fails

        # Translate arguments
        args = []
        for arg in expr.items[1:]:
            arg_z3 = self.translate_expr(arg)
            if arg_z3 is None:
                return None
            args.append(arg_z3)

        # Create uninterpreted function with unique key based on name and arity
        func_key = f"fn_{fn_name}_{len(args)}"

        # Check if we have imported signature with type info
        imported_sig = self.imported_defs.functions.get(fn_name)

        if func_key not in self.variables:
            # Determine return type based on imported signature or naming conventions
            return_sort = z3.IntSort()  # Default
            return_type: Optional[Type] = None

            if imported_sig:
                return_type = imported_sig.return_type
                if isinstance(return_type, PrimitiveType) and return_type.name == 'Bool':
                    return_sort = z3.BoolSort()
                elif isinstance(return_type, RangeType):
                    return_sort = z3.IntSort()  # Range types are integers
                # Other types default to IntSort
            else:
                # Use naming conventions for functions without imported signature
                is_predicate = (fn_name.endswith('-eq') or fn_name.endswith('?') or
                              fn_name.startswith('is-') or fn_name.endswith('-contains') or
                              fn_name == 'graph-contains' or fn_name == 'contains' or
                              fn_name.startswith('has-'))
                if is_predicate:
                    return_sort = z3.BoolSort()

            # Build argument sorts (default to Int for all args)
            if args:
                arg_sorts = [z3.IntSort()] * len(args)
                func = z3.Function(func_key, *arg_sorts, return_sort)
            else:
                # Zero-argument function
                func = z3.Function(func_key, return_sort)
            self.variables[func_key] = func
        else:
            func = self.variables[func_key]
            # Get return type from imported signature if available
            return_type = imported_sig.return_type if imported_sig else None

        # Apply the function to arguments
        if args:
            result = func(*args)
        else:
            result = func()

        # Add range constraints for imported functions with range return types
        if imported_sig and isinstance(imported_sig.return_type, RangeType):
            bounds = imported_sig.return_type.bounds
            if bounds.min_val is not None:
                self.constraints.append(result >= bounds.min_val)
            if bounds.max_val is not None:
                self.constraints.append(result <= bounds.max_val)

        return result




__all__ = [
    'Z3Translator',
]
