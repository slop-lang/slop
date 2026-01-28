"""
Loop analysis pattern dataclasses.

These represent various patterns detected in loops for verification and optimization.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, TYPE_CHECKING

if TYPE_CHECKING:
    from slop.parser import SExpr


# ============================================================================
# Type Invariants
# ============================================================================

@dataclass
class TypeInvariant:
    """Type invariant: a condition that must hold for all values of the type"""
    type_name: str
    condition: 'SExpr'  # The invariant expression


# ============================================================================
# Loop Pattern Detection
# ============================================================================

@dataclass
class FilterPatternInfo:
    """Information about a detected filter loop pattern.

    Filter pattern:
    (let ((mut result (make-X arena)))
      (for-each (item collection)
        (if predicate
          (set! result (add-X arena result item))))
      result)
    """
    result_var: str  # The mutable result variable name
    collection: 'SExpr'  # The collection being iterated
    loop_var: str  # The loop variable name
    predicate: 'SExpr'  # The filter predicate
    is_negated: bool = False  # Whether predicate is (not ...), indicating exclusion
    excluded_item: Optional['SExpr'] = None  # If negated equality, the excluded item


@dataclass
class MapPatternInfo:
    """Information about a detected map/transform loop pattern.

    Map pattern:
    (let ((mut result (list-new arena Type)))
      (for-each (item collection)
        (list-push result (constructor-new arena (field1 item) (field2 item) ...)))
      result)

    Unlike filter patterns which have a conditional push, map patterns have
    unconditional push of a transformed/constructed element.
    """
    result_var: str  # The mutable result variable name
    collection: 'SExpr'  # The collection being iterated (may be field access)
    loop_var: str  # The loop variable name
    constructor_expr: 'SExpr'  # The transformation/constructor expression
    field_mappings: Dict[str, 'SExpr']  # result_field -> source_expression
                                         # e.g., {'subject': (triple-object dt)}


class FieldSource:
    """Source classification for constructor fields in nested loops."""
    CONSTANT = "constant"    # Same value for all results (e.g., same-as from outer let)
    OUTER = "outer"          # Derived from outer loop variable
    INNER = "inner"          # Derived from inner loop variable
    MIXED = "mixed"          # Combines multiple sources


@dataclass
class InnerLoopInfo:
    """Information about an inner loop in a nested loop pattern."""
    collection: 'SExpr'                 # The collection being iterated (may be a query result)
    loop_var: str                       # The loop variable name
    filter: Optional['SExpr']           # Filter condition from (when ...) if any
    bindings: Dict[str, 'SExpr']        # Variable bindings from let expressions
    join_vars: Set[str]                 # Variables from outer scope used in collection query


@dataclass
class NestedLoopPatternInfo:
    """Information about a nested loop pattern with join semantics.

    Nested loop join pattern (e.g., eq-trans):
    (let ((mut result (list-new arena Type))
          (same-as (make-iri arena OWL_SAME_AS)))  ; outer constants
      (for-each (dt (. delta triples))             ; OUTER loop
        (when outer-filter                          ; outer filter
          (let ((x (triple-subject dt))
                (y (triple-object dt)))             ; outer bindings
            (let ((y-objects (indexed-graph-match arena g (some y) ...)))  ; join query
              (for-each (yo-triple y-objects)      ; INNER loop
                (let ((z (triple-object yo-triple)))  ; inner bindings
                  (when inner-filter                  ; inner filter
                    (list-push result (make-triple arena x same-as z)))))))))
      result)

    This pattern represents a join between delta.triples and the result of
    indexed-graph-match, similar to a SQL join.
    """
    result_var: str                   # The mutable result variable name

    # Outer loop info
    outer_collection: 'SExpr'           # e.g., (. delta triples)
    outer_loop_var: str               # e.g., dt
    outer_filter: Optional['SExpr']     # e.g., (term-eq (triple-predicate dt) same-as)
    outer_bindings: Dict[str, 'SExpr']  # e.g., {x: (triple-subject dt), y: (triple-object dt)}
    outer_let_bindings: Dict[str, 'SExpr']  # Constants from outer let (e.g., same-as)

    # Inner loop(s) - list supports multiple nesting levels
    inner_loops: List[InnerLoopInfo]

    # Constructor info
    constructor_expr: 'SExpr'           # e.g., (make-triple arena x same-as z)
    field_mappings: Dict[str, 'SExpr']  # e.g., {subject: x, predicate: same-as, object: z}

    # Field provenance: which source each field comes from
    field_provenance: Dict[str, str]  # e.g., {subject: OUTER, predicate: CONSTANT, object: INNER}


@dataclass
class CountPatternInfo:
    """Information about a detected count loop pattern.

    Count pattern:
    (let ((mut count 0))
      (for-each (item collection)
        (if predicate
          (set! count (+ count 1))))
      count)
    """
    count_var: str  # The mutable count variable name
    collection: 'SExpr'  # The collection being iterated
    loop_var: str  # The loop variable name
    predicate: 'SExpr'  # The condition for incrementing count


@dataclass
class FoldPatternInfo:
    """Information about a detected fold/accumulation loop pattern.

    Fold pattern:
    (let ((mut acc init))
      (for-each (item collection)
        (set! acc (op acc item)))
      acc)
    """
    acc_var: str  # The mutable accumulator variable name
    init_value: 'SExpr'  # The initial accumulator value
    collection: 'SExpr'  # The collection being iterated
    loop_var: str  # The loop variable name
    operator: str  # The accumulation operator (e.g., '+', '*', 'max', 'min')


@dataclass
class FindPatternInfo:
    """Information about a detected find-first loop pattern.

    Find pattern:
    (let ((mut found nil))
      (for-each (item collection)
        (if (and (== found nil) predicate)
          (set! found item)))
      found)
    """
    result_var: str  # The mutable result variable name
    collection: 'SExpr'  # The collection being iterated
    loop_var: str  # The loop variable name
    predicate: 'SExpr'  # The condition for selecting an item


# ============================================================================
# Loop Context for SSA Analysis
# ============================================================================

@dataclass
class SetBinding:
    """Information about a set! statement within a loop.

    Tracks which variable is being set, what function is called,
    and whether it's self-referential (variable passed as argument).
    """
    var_name: str  # Variable being set
    call_expr: 'SExpr'  # The function call expression
    fn_name: str  # Name of function being called
    is_self_ref: bool  # Whether var_name is passed as an argument
    self_ref_params: Dict[str, str]  # Maps param names to var names for self-refs


@dataclass
class LoopContext:
    """Information about a for-each loop for SSA analysis.

    Captures the structure of a loop including:
    - The iteration variable and collection
    - All variables modified within the loop (via set!)
    - Function calls in those set! statements with their postconditions
    """
    loop_var: str  # The iteration variable (e.g., 't' in (for-each (t triples) ...))
    collection: 'SExpr'  # The collection being iterated
    loop_expr: 'SExpr'  # The full for-each expression
    modified_vars: Set[str]  # Variables modified by set! within the loop
    set_bindings: List[SetBinding]  # All set! statements in the loop
    loop_invariants: List['SExpr']  # Explicit @loop-invariant annotations


@dataclass
class WhileLoopContext:
    """Information about a while loop for verification.

    Captures the structure of a while loop including:
    - The loop condition
    - The full while expression
    - All variables modified within the loop (via set!)
    - Explicit @loop-invariant annotations
    """
    condition: 'SExpr'  # The loop condition
    loop_expr: 'SExpr'  # The full (while ...) expression
    modified_vars: Set[str]  # Variables modified by set! within the loop
    loop_invariants: List['SExpr']  # Explicit @loop-invariant annotations


__all__ = [
    'TypeInvariant',
    'FilterPatternInfo',
    'MapPatternInfo',
    'FieldSource',
    'InnerLoopInfo',
    'NestedLoopPatternInfo',
    'CountPatternInfo',
    'FoldPatternInfo',
    'FindPatternInfo',
    'SetBinding',
    'LoopContext',
    'WhileLoopContext',
]
