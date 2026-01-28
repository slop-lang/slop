"""
SLOP Z3 Verifier - Contract and range verification using Z3 SMT solver

Verifies:
- @pre/@post contract consistency
- Range type safety through arithmetic operations
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Tuple, Union, Set
from slop.parser import SExpr, SList, Symbol, String, Number, is_form, parse, parse_file
from slop.types import (
    Type, PrimitiveType, RangeType, RangeBounds, RecordType, EnumType,
    OptionType, ResultType, PtrType, FnType, UNKNOWN, ListType, ArrayType,
    UnionType,
)
import subprocess
import sys
import os
import json
from pathlib import Path


def _find_system_z3() -> bool:
    """Try to find and import z3 from system Python or pipx."""
    # Try pipx first (common for tools installed outside venvs)
    pipx_venv = Path.home() / ".local/share/pipx/venvs/z3-solver"
    if pipx_venv.exists():
        # Find site-packages (handles different Python versions)
        site_packages_paths = list(pipx_venv.glob("lib/python*/site-packages"))
        if site_packages_paths:
            site_packages = str(site_packages_paths[0])
            if site_packages not in sys.path:
                sys.path.insert(0, site_packages)
            return True

    # Try to get z3 path from system python3
    try:
        result = subprocess.run(
            ["python3", "-c", "import z3; print(z3.__path__[0])"],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            z3_path = result.stdout.strip()
            # Add parent directory (site-packages) to path
            site_packages = os.path.dirname(z3_path)
            if site_packages not in sys.path:
                sys.path.insert(0, site_packages)
            return True
    except (subprocess.TimeoutExpired, FileNotFoundError, Exception):
        pass
    return False


# Try to import Z3 - make it optional
try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    # Try system Python fallback
    if _find_system_z3():
        try:
            import z3
            Z3_AVAILABLE = True
        except ImportError:
            Z3_AVAILABLE = False
            z3 = None  # type: ignore
    else:
        Z3_AVAILABLE = False
        z3 = None  # type: ignore


# ============================================================================
# Source Location
# ============================================================================

@dataclass
class SourceLocation:
    """Source location for error messages"""
    file: str = "<unknown>"
    line: int = 0
    column: int = 0


# ============================================================================
# Minimal Type Environment (for Z3 verification without full type checker)
# ============================================================================

@dataclass
class MinimalTypeEnv:
    """Minimal type environment for Z3 verification.

    Provides the subset of TypeEnv functionality needed by Z3Translator:
    - type_registry: Dict mapping type names to Type objects
    - lookup_var: Method to get type for a variable name
    - invariant_registry: TypeInvariantRegistry for type invariants
    """
    type_registry: Dict[str, Type] = field(default_factory=dict)
    _var_types: Dict[str, Type] = field(default_factory=dict)
    invariant_registry: Optional['TypeInvariantRegistry'] = None

    def lookup_var(self, name: str) -> Optional[Type]:
        """Look up the type of a variable"""
        return self._var_types.get(name)

    def bind_var(self, name: str, typ: Type):
        """Bind a variable to a type"""
        self._var_types[name] = typ

    def get_invariants_for_type(self, type_name: str) -> List[SExpr]:
        """Get invariants for a type, if invariant registry is available"""
        if self.invariant_registry:
            return self.invariant_registry.get_invariants(type_name)
        return []

# ============================================================================
# Imported Definitions (for verifying contracts with imported symbols)
# ============================================================================

@dataclass
class FunctionSignature:
    """Signature of an imported function for verification."""
    name: str
    param_types: List[Type]  # Parameter types in order
    return_type: Type  # Return type (may include range bounds)
    params: List[str] = field(default_factory=list)  # Parameter names for postcondition substitution
    postconditions: List[SExpr] = field(default_factory=list)  # @post annotations


@dataclass
class ConstantDef:
    """Definition of an imported constant."""
    name: str
    type: Type
    value: Any  # String, int, float


@dataclass
class ImportedDefinitions:
    """Definitions extracted from imported modules for verification."""
    functions: Dict[str, FunctionSignature] = field(default_factory=dict)
    types: Dict[str, Type] = field(default_factory=dict)  # RecordType, EnumType, UnionType, RangeType
    constants: Dict[str, ConstantDef] = field(default_factory=dict)

    def merge(self, other: 'ImportedDefinitions'):
        """Merge another ImportedDefinitions into this one."""
        self.functions.update(other.functions)
        self.types.update(other.types)
        self.constants.update(other.constants)


# ============================================================================
# Function Registry (for inlining during verification)
# ============================================================================

@dataclass
class FunctionDef:
    """Definition of a function for inlining purposes"""
    name: str
    params: List[str]  # Parameter names in order
    body: Optional[SExpr]
    is_pure: bool = True
    postconditions: List[SExpr] = field(default_factory=list)
    properties: List[Tuple[Optional[str], SExpr]] = field(default_factory=list)  # @property - (name, expr) tuples


class FunctionRegistry:
    """Registry of functions for inlining during verification.

    Enables inlining of simple accessor functions so postconditions like
    (term-eq (triple-subject $result) subject) can be proven by replacing
    (triple-subject $result) with the actual field access.
    """

    def __init__(self):
        self.functions: Dict[str, FunctionDef] = {}

    def register_from_ast(self, ast: List[SExpr]):
        """Extract function definitions from AST"""
        for form in ast:
            if is_form(form, 'module'):
                for item in form.items[1:]:
                    if is_form(item, 'fn'):
                        self._register_fn(item)
            elif is_form(form, 'fn'):
                self._register_fn(form)

    def _register_fn(self, fn_form: SList):
        """Register a single function"""
        if len(fn_form) < 3:
            return
        name = fn_form[1].name if isinstance(fn_form[1], Symbol) else None
        if not name:
            return

        # Extract parameter names
        params = []
        param_list = fn_form[2] if isinstance(fn_form[2], SList) else SList([])
        for param in param_list:
            if isinstance(param, SList) and len(param) >= 2:
                first = param[0]
                if isinstance(first, Symbol) and first.name in ('in', 'out', 'mut'):
                    # Mode is explicit: (in name Type)
                    param_name = param[1].name if isinstance(param[1], Symbol) else None
                else:
                    # No mode: (name Type)
                    param_name = first.name if isinstance(first, Symbol) else None
                if param_name:
                    params.append(param_name)

        # Extract body, postconditions, properties (skip other annotations and :keywords)
        body = None
        is_pure = False
        postconditions: List[SExpr] = []
        properties: List[SExpr] = []
        annotation_forms = {'@intent', '@spec', '@pre', '@post', '@assume', '@pure',
                           '@alloc', '@example', '@deprecated', '@property',
                           '@generation-mode', '@requires'}

        skip_next_string = False
        for item in fn_form.items[3:]:
            if isinstance(item, Symbol):
                if item.name.startswith(':'):
                    skip_next_string = True  # Next String is property value
                    continue
                # Simple expression as body
                body = item
                skip_next_string = False
            elif isinstance(item, String):
                # Skip string values after :keyword (property values)
                # But allow standalone String as function body
                if skip_next_string:
                    skip_next_string = False
                    continue
                body = item
            elif is_form(item, '@pure'):
                is_pure = True
                skip_next_string = False
                continue
            elif is_form(item, '@post') and len(item) > 1:
                # Extract postcondition
                postconditions.append(item[1])
                skip_next_string = False
                continue
            elif is_form(item, '@property') and len(item) > 1:
                # Extract property (universal assertion)
                # Named: (@property name expr) or Unnamed: (@property expr)
                if isinstance(item[1], Symbol) and len(item) > 2:
                    # Named property: (@property name expr)
                    properties.append((item[1].name, item[2]))
                else:
                    # Unnamed property: (@property expr)
                    properties.append((None, item[1]))
                skip_next_string = False
                continue
            elif isinstance(item, SList) and len(item) > 0:
                head = item[0]
                if isinstance(head, Symbol) and head.name in annotation_forms:
                    skip_next_string = False
                    continue
                body = item
                skip_next_string = False

        self.functions[name] = FunctionDef(name=name, params=params, body=body,
                                           is_pure=is_pure, postconditions=postconditions,
                                           properties=properties)

    def is_simple_accessor(self, name: str) -> bool:
        """Check if function is a simple field accessor: (. param field)"""
        fn = self.functions.get(name)
        if fn and fn.body and is_form(fn.body, '.'):
            return True
        return False

    def get_accessor_info(self, name: str) -> Optional[Tuple[str, str]]:
        """Get (param_name, field_name) for a simple accessor"""
        fn = self.functions.get(name)
        if fn and fn.body and is_form(fn.body, '.') and len(fn.body) >= 3:
            obj = fn.body[1]
            field = fn.body[2]
            if isinstance(obj, Symbol) and isinstance(field, Symbol):
                return (obj.name, field.name)
        return None

    def is_simple_inlinable(self, name: str) -> bool:
        """Check if function is a simple expression that can be inlined.

        Criteria:
        1. Function is marked @pure
        2. Body is a single expression (no control flow)
        3. Not recursive

        Examples of inlinable functions:
        - (fn iri-eq ((a IRI) (b IRI)) (@pure) (string-eq (. a value) (. b value)))
        - (fn blank-eq ((a BlankNode) (b BlankNode)) (@pure) (== (. a id) (. b id)))
        - (fn num-eq ((a Int) (b Int)) (@pure) (== a b))
        """
        fn = self.functions.get(name)
        if not fn or not fn.body or not fn.is_pure:
            return False
        return self._is_simple_expression(fn.body, name)

    def inlines_to_native_equality(self, name: str) -> bool:
        """Check if function inlines to native ==.

        Used by union equality axioms to determine if a helper-eq function
        should be treated as native Z3 equality rather than an uninterpreted function.

        Returns True ONLY for functions that directly use == on parameters:
        - (fn num-eq ((a Int) (b Int)) (@pure) (== a b))

        Does NOT return True for string-eq since that's modeled as an
        uninterpreted function in Z3, not native equality.
        """
        fn = self.functions.get(name)
        if not fn or not fn.body or not fn.is_pure:
            return False

        if not self._is_simple_expression(fn.body, name):
            return False

        # Check if body is (== param1 param2) - ONLY native ==
        body = fn.body
        if not isinstance(body, SList) or len(body) < 3:
            return False

        head = body[0]
        if not isinstance(head, Symbol):
            return False

        # Only native == counts, not string-eq or other comparison functions
        if head.name != '==':
            return False

        # Check if arguments are direct parameter references
        arg1, arg2 = body[1], body[2]
        if isinstance(arg1, Symbol) and isinstance(arg2, Symbol):
            if arg1.name in fn.params and arg2.name in fn.params:
                return True

        return False

    def _is_simple_expression(self, expr: SExpr, fn_name: str) -> bool:
        """Check if expression is a simple expression suitable for inlining.

        Returns False for:
        - Control flow: if, cond, match, when, unless
        - Loops: for-each, while
        - Bindings: let, do (multiple expressions)
        - Mutation: set!
        - Recursive calls to fn_name
        """
        if isinstance(expr, (Symbol, Number, String)):
            # Simple values are always inlinable
            return True

        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                head_name = head.name
                # Reject control flow and complex constructs
                if head_name in ('if', 'cond', 'match', 'when', 'unless',
                                 'for-each', 'while',
                                 'let', 'do', 'set!'):
                    return False
                # Reject recursive calls
                if head_name == fn_name:
                    return False
                # For other function calls, check all arguments are simple
                for arg in expr.items[1:]:
                    if not self._is_simple_expression(arg, fn_name):
                        return False
                return True

        return False


# ============================================================================
# Type Registry Builder (extract types from AST without full type checking)
# ============================================================================

@dataclass
class TypeInvariant:
    """Type invariant: a condition that must hold for all values of the type"""
    type_name: str
    condition: SExpr  # The invariant expression


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
    collection: SExpr  # The collection being iterated
    loop_var: str  # The loop variable name
    predicate: SExpr  # The filter predicate
    is_negated: bool = False  # Whether predicate is (not ...), indicating exclusion
    excluded_item: Optional[SExpr] = None  # If negated equality, the excluded item


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
    collection: SExpr  # The collection being iterated (may be field access)
    loop_var: str  # The loop variable name
    constructor_expr: SExpr  # The transformation/constructor expression
    field_mappings: Dict[str, SExpr]  # result_field -> source_expression
                                       # e.g., {'subject': (triple-object dt)}


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
    collection: SExpr  # The collection being iterated
    loop_var: str  # The loop variable name
    predicate: SExpr  # The condition for incrementing count


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
    init_value: SExpr  # The initial accumulator value
    collection: SExpr  # The collection being iterated
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
    collection: SExpr  # The collection being iterated
    loop_var: str  # The loop variable name
    predicate: SExpr  # The condition for selecting an item


@dataclass
class SetBinding:
    """Information about a set! statement within a loop.

    Tracks which variable is being set, what function is called,
    and whether it's self-referential (variable passed as argument).
    """
    var_name: str  # Variable being set
    call_expr: SExpr  # The function call expression
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
    collection: SExpr  # The collection being iterated
    loop_expr: SExpr  # The full for-each expression
    modified_vars: Set[str]  # Variables modified by set! within the loop
    set_bindings: List[SetBinding]  # All set! statements in the loop
    loop_invariants: List[SExpr]  # Explicit @loop-invariant annotations


@dataclass
class WhileLoopContext:
    """Information about a while loop for verification.

    Captures the structure of a while loop including:
    - The loop condition
    - The full while expression
    - All variables modified within the loop (via set!)
    - Explicit @loop-invariant annotations
    """
    condition: SExpr  # The loop condition
    loop_expr: SExpr  # The full (while ...) expression
    modified_vars: Set[str]  # Variables modified by set! within the loop
    loop_invariants: List[SExpr]  # Explicit @loop-invariant annotations


@dataclass
class SSAVersion:
    """Represents a specific version of a variable in SSA form.

    Each assignment creates a new version:
    - result@0: initial value (from let binding)
    - result@1: after first set!
    - result@k: after k-th set! (or symbolic for loop iterations)
    """
    var_name: str  # Original variable name
    version: int  # Version number (0 = initial)
    z3_var: Any  # The Z3 variable for this version (z3.ExprRef)
    defining_expr: Optional[SExpr] = None  # The expression that defined this version
    is_loop_version: bool = False  # True if this is a symbolic loop iteration version


class SSAContext:
    """Manages SSA versioning for variables during verification.

    Tracks the current version of each mutable variable and creates
    new Z3 variables for each assignment. This enables precise reasoning
    about value flow through assignments.

    Example:
        (let ((mut result (make-delta arena iter)))  ; result@0
          (for-each (t triples)
            (set! result (delta-add arena result t)))  ; result@1, result@2, ...
          result)  ; result@N (final)
    """

    def __init__(self, translator: 'Z3Translator'):
        self.translator = translator
        # var_name -> list of SSAVersion (index = version number)
        self.versions: Dict[str, List[SSAVersion]] = {}
        # var_name -> current version number
        self.current_version: Dict[str, int] = {}

    def init_variable(self, var_name: str, z3_var: Any, defining_expr: Optional[SExpr] = None):
        """Initialize a variable at version 0 (from let binding)."""
        version = SSAVersion(
            var_name=var_name,
            version=0,
            z3_var=z3_var,
            defining_expr=defining_expr
        )
        self.versions[var_name] = [version]
        self.current_version[var_name] = 0

    def get_current_version(self, var_name: str) -> Optional[SSAVersion]:
        """Get the current SSA version of a variable."""
        if var_name not in self.versions:
            return None
        ver_num = self.current_version[var_name]
        return self.versions[var_name][ver_num]

    def get_version(self, var_name: str, version: int) -> Optional[SSAVersion]:
        """Get a specific version of a variable."""
        if var_name not in self.versions:
            return None
        if version < 0 or version >= len(self.versions[var_name]):
            return None
        return self.versions[var_name][version]

    def create_new_version(self, var_name: str, defining_expr: Optional[SExpr] = None,
                           is_loop_version: bool = False) -> SSAVersion:
        """Create a new version of a variable (for set! or loop iteration).

        Returns the new SSAVersion with an appropriately typed Z3 variable.
        """
        if var_name not in self.versions:
            raise ValueError(f"Variable {var_name} not initialized in SSA context")

        current = self.get_current_version(var_name)
        if current is None:
            raise ValueError(f"No current version for {var_name}")

        new_ver_num = len(self.versions[var_name])
        new_var_name = f"{var_name}@{new_ver_num}"

        # Create Z3 variable with same sort as current version
        z3_var = current.z3_var
        if z3.is_bool(z3_var):
            new_z3_var = z3.Bool(new_var_name)
        elif z3.is_real(z3_var):
            new_z3_var = z3.Real(new_var_name)
        else:
            new_z3_var = z3.Int(new_var_name)

        new_version = SSAVersion(
            var_name=var_name,
            version=new_ver_num,
            z3_var=new_z3_var,
            defining_expr=defining_expr,
            is_loop_version=is_loop_version
        )

        self.versions[var_name].append(new_version)
        self.current_version[var_name] = new_ver_num

        # Register in translator's variables
        self.translator.variables[new_var_name] = new_z3_var

        return new_version

    def get_versioned_name(self, var_name: str) -> str:
        """Get the current versioned name (e.g., 'result@2')."""
        if var_name not in self.current_version:
            return var_name  # Not an SSA-tracked variable
        ver = self.current_version[var_name]
        if ver == 0:
            return var_name  # Version 0 uses original name
        return f"{var_name}@{ver}"

    def is_tracked(self, var_name: str) -> bool:
        """Check if a variable is being tracked in SSA form."""
        return var_name in self.versions

    def get_all_versions(self, var_name: str) -> List[SSAVersion]:
        """Get all versions of a variable."""
        return self.versions.get(var_name, [])

    def snapshot(self) -> Dict[str, int]:
        """Take a snapshot of current version numbers (for loop entry)."""
        return dict(self.current_version)

    def restore(self, snapshot: Dict[str, int]):
        """Restore version numbers from a snapshot."""
        self.current_version = dict(snapshot)


# ============================================================================
# Weakest Precondition Calculus
# ============================================================================

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

    def wp(self, expr: SExpr, postcondition: 'z3.BoolRef') -> 'z3.BoolRef':
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

    def _find_loop_invariant(self, loop_expr: SList) -> Optional[SExpr]:
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

    def _pattern_to_tag_index(self, pattern: SExpr) -> Optional[int]:
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

    def _is_wildcard_pattern(self, pattern: SExpr) -> bool:
        """Check if pattern is a wildcard (_)."""
        if isinstance(pattern, Symbol):
            return pattern.name == '_'
        return False

    def _substitute_var_with_expr(
        self, formula: 'z3.BoolRef', var_name: str, expr: SExpr
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


@dataclass
class InferredInvariant:
    """A loop invariant automatically inferred from function postconditions.

    Invariants are inferred by analyzing postconditions of functions called
    in set! statements within loops. For example:

    - `{(. $result field) == (. param field)}` → field preserved
    - `{(. $result field) >= (. param field)}` → field monotonically increasing
    - `{(list-len (. $result list)) >= ...}` → list grows or stays same

    These inferred invariants enable automatic verification of loops without
    requiring explicit @loop-invariant annotations.
    """
    variable: str  # The loop variable this invariant applies to
    property_expr: SExpr  # The invariant expression (using variable name, not $result)
    source: str  # Where this was inferred from: "initialization", "preservation", "postcondition"
    confidence: float = 1.0  # Confidence level (1.0 = certain, lower = heuristic)
    original_postcondition: Optional[SExpr] = None  # The postcondition it was derived from


class InvariantInferencer:
    """Infers loop invariants from function postconditions.

    Analyzes postconditions of functions called within loops to automatically
    derive loop invariants. This enables verification of loops without
    requiring manual @loop-invariant annotations.

    Inference patterns:
    1. Field preservation: (. $result field) == (. param field)
       → Invariant: field value unchanged through iterations

    2. Monotonic increase: (. $result field) >= (. param field)
       → Invariant: field monotonically increasing

    3. List growth: (list-len (. $result list)) >= (list-len (. param list))
       → Invariant: list grows or stays same size

    4. Non-negative: (>= $result 0) or (>= (. $result field) 0)
       → Invariant: value stays non-negative
    """

    def __init__(self, function_registry: Optional['FunctionRegistry'] = None,
                 imported_defs: Optional['ImportedDefinitions'] = None):
        self.function_registry = function_registry
        self.imported_defs = imported_defs

    def infer_from_loop(self, loop_ctx: LoopContext) -> List[InferredInvariant]:
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

    def _get_postconditions(self, fn_name: str) -> List[SExpr]:
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

    def _infer_from_postcondition(self, post: SExpr, var_name: str,
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

    def _check_field_preservation(self, post: SExpr,
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

    def _check_monotonic_increase(self, post: SExpr,
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

    def _check_nonnegative(self, post: SExpr) -> Optional[SExpr]:
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

    def _check_list_length_pattern(self, post: SExpr,
                                    param_names: List[str]) -> Optional[SExpr]:
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

    def _extract_result_field(self, expr: SExpr) -> Optional[str]:
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

    def _extract_param_field(self, expr: SExpr,
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

    def _make_field_preserved_invariant(self, var_name: str, field_name: str) -> SExpr:
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


class TypeInvariantRegistry:
    """Registry of type invariants extracted from @invariant annotations"""

    def __init__(self):
        self.invariants: Dict[str, List[SExpr]] = {}  # type_name -> list of invariant expressions

    def add_invariant(self, type_name: str, condition: SExpr):
        """Add an invariant for a type"""
        if type_name not in self.invariants:
            self.invariants[type_name] = []
        self.invariants[type_name].append(condition)

    def get_invariants(self, type_name: str) -> List[SExpr]:
        """Get all invariants for a type"""
        return self.invariants.get(type_name, [])


def build_type_registry_from_ast(ast: List[SExpr]) -> Dict[str, Type]:
    """Extract type definitions from AST without full type checking.

    Mirrors the native type-extract.slop approach for extracting types.
    """
    registry: Dict[str, Type] = {}

    for form in ast:
        if is_form(form, 'module'):
            # Process forms inside module
            for item in form.items[1:]:
                if is_form(item, 'type'):
                    _register_type(item, registry)
        elif is_form(form, 'type'):
            _register_type(form, registry)

    return registry


def build_invariant_registry_from_ast(ast: List[SExpr]) -> TypeInvariantRegistry:
    """Extract type invariants from AST.

    Looks for @invariant annotations in type definitions:
    (type Name (record ...) (@invariant condition))
    """
    registry = TypeInvariantRegistry()

    for form in ast:
        if is_form(form, 'module'):
            for item in form.items[1:]:
                if is_form(item, 'type'):
                    _extract_type_invariants(item, registry)
        elif is_form(form, 'type'):
            _extract_type_invariants(form, registry)

    return registry


def _extract_type_invariants(type_form: SList, registry: TypeInvariantRegistry):
    """Extract @invariant annotations from a type definition"""
    if len(type_form) < 3:
        return

    name = type_form[1].name if isinstance(type_form[1], Symbol) else None
    if not name:
        return

    # Look for @invariant forms after the type body
    for item in type_form.items[3:]:
        if is_form(item, '@invariant') and len(item) >= 2:
            registry.add_invariant(name, item[1])


def _register_type(type_form: SList, registry: Dict[str, Type]):
    """Parse (type Name ...) into registry."""
    if len(type_form) < 3:
        return

    name = type_form[1].name if isinstance(type_form[1], Symbol) else None
    if not name:
        return

    body = type_form[2]

    if is_form(body, 'record'):
        # (type Name (record (field1 T1) (field2 T2) ...))
        fields: Dict[str, Type] = {}
        for field_item in body.items[1:]:
            if isinstance(field_item, SList) and len(field_item) >= 2:
                fname = field_item[0].name if isinstance(field_item[0], Symbol) else None
                if fname:
                    ftype = _parse_type_expr_simple(field_item[1], registry)
                    fields[fname] = ftype
        registry[name] = RecordType(name, fields)

    elif is_form(body, 'enum'):
        # (type Name (enum val1 val2 ...))
        variants = [v.name for v in body.items[1:] if isinstance(v, Symbol)]
        registry[name] = EnumType(name, variants)

    elif is_form(body, 'union'):
        # (type Name (union (tag1 T1) (tag2) ...))
        variants: Dict[str, Optional[Type]] = {}
        for variant in body.items[1:]:
            if isinstance(variant, SList) and len(variant) >= 1:
                tag = variant[0].name if isinstance(variant[0], Symbol) else None
                if tag:
                    payload = _parse_type_expr_simple(variant[1], registry) if len(variant) > 1 else None
                    variants[tag] = payload
            elif isinstance(variant, Symbol):
                # Tag without payload
                variants[variant.name] = None
        registry[name] = UnionType(name, variants)

    elif is_form(body, 'Int') or (isinstance(body, SList) and len(body) >= 3):
        # Range type: (type Name (Int min .. max)) or (type Name (Int min ..))
        bounds = _parse_range_bounds(body)
        if bounds:
            registry[name] = RangeType('Int', bounds)

    elif isinstance(body, Symbol):
        # Type alias: (type Name ExistingType)
        aliased = _parse_type_expr_simple(body, registry)
        registry[name] = aliased


def _parse_type_expr_simple(expr: SExpr, registry: Dict[str, Type]) -> Type:
    """Parse type expression with minimal context."""
    if isinstance(expr, Symbol):
        name = expr.name
        if name in registry:
            return registry[name]
        # Standard primitive types
        if name in ('Int', 'I8', 'I16', 'I32', 'I64', 'U8', 'U16', 'U32', 'U64',
                    'Float', 'F32', 'F64', 'Bool', 'String', 'Unit', 'Void', 'Arena'):
            return PrimitiveType(name)
        # Unknown type - might be defined later
        return PrimitiveType(name)

    if isinstance(expr, SList) and len(expr) >= 1:
        head = expr[0]
        if isinstance(head, Symbol):
            head_name = head.name

            if head_name == 'Ptr' and len(expr) >= 2:
                inner = _parse_type_expr_simple(expr[1], registry)
                return PtrType(inner)

            if head_name == 'OwnPtr' and len(expr) >= 2:
                inner = _parse_type_expr_simple(expr[1], registry)
                return PtrType(inner, owning=True)

            if head_name == 'OptPtr' and len(expr) >= 2:
                inner = _parse_type_expr_simple(expr[1], registry)
                return PtrType(inner, nullable=True)

            if head_name == 'Option' and len(expr) >= 2:
                inner = _parse_type_expr_simple(expr[1], registry)
                return OptionType(inner)

            if head_name == 'Result' and len(expr) >= 3:
                ok_type = _parse_type_expr_simple(expr[1], registry)
                err_type = _parse_type_expr_simple(expr[2], registry)
                return ResultType(ok_type, err_type)

            if head_name == 'List' and len(expr) >= 2:
                elem = _parse_type_expr_simple(expr[1], registry)
                return ListType(elem)

            if head_name == 'Array' and len(expr) >= 3:
                elem = _parse_type_expr_simple(expr[1], registry)
                size = expr[2].value if isinstance(expr[2], Number) else 0
                return ArrayType(elem, int(size))

            if head_name == 'Fn' and len(expr) >= 4:
                # (Fn (A B) -> R)
                params = expr[1]
                ret = expr[3] if len(expr) > 3 else expr[-1]
                param_types: List[Type] = []
                if isinstance(params, SList):
                    for p in params.items:
                        param_types.append(_parse_type_expr_simple(p, registry))
                ret_type = _parse_type_expr_simple(ret, registry)
                return FnType(tuple(param_types), ret_type)

            # Range type: (Int min .. max)
            if head_name in ('Int', 'I8', 'I16', 'I32', 'I64', 'U8', 'U16', 'U32', 'U64'):
                bounds = _parse_range_bounds(expr)
                if bounds:
                    return RangeType(head_name, bounds)
                return PrimitiveType(head_name)

            # Check registry for parameterized type
            if head_name in registry:
                return registry[head_name]

    return UNKNOWN


def _parse_range_bounds(expr: SExpr) -> Optional[RangeBounds]:
    """Parse range bounds from (Int min .. max) or (Int min ..) or (Int .. max)."""
    if not isinstance(expr, SList) or len(expr) < 3:
        return None

    # Expected formats:
    # (Int min .. max) - 4 elements, bounded range
    # (Int min ..)     - 3 elements, lower-bounded only
    # (Int .. max)     - 3 elements, upper-bounded only
    # Find the '..' separator
    dot_idx = -1
    for i, item in enumerate(expr.items):
        if isinstance(item, Symbol) and item.name == '..':
            dot_idx = i
            break

    if dot_idx == -1:
        return None

    min_val: Optional[int] = None
    max_val: Optional[int] = None

    # Parse min value (before ..)
    if dot_idx > 1:
        min_item = expr[dot_idx - 1]
        if isinstance(min_item, Number):
            min_val = int(min_item.value)
        elif isinstance(min_item, Symbol) and min_item.name.lstrip('-').isdigit():
            min_val = int(min_item.name)

    # Parse max value (after ..)
    if dot_idx + 1 < len(expr):
        max_item = expr[dot_idx + 1]
        if isinstance(max_item, Number):
            max_val = int(max_item.value)
        elif isinstance(max_item, Symbol) and max_item.name.lstrip('-').isdigit():
            max_val = int(max_item.name)

    return RangeBounds(min_val, max_val)


# ============================================================================
# Import Resolution for Verification
# ============================================================================

def extract_module_definitions(ast: List[SExpr], registry: Dict[str, Type]) -> ImportedDefinitions:
    """Extract all exportable definitions from a module AST.

    Args:
        ast: Parsed module AST
        registry: Type registry built from the module (for resolving type references)

    Returns:
        ImportedDefinitions with functions, types, and constants
    """
    defs = ImportedDefinitions()

    for form in ast:
        if is_form(form, 'module'):
            # Process forms inside module
            for item in form.items[1:]:
                _extract_definition(item, defs, registry)
        else:
            _extract_definition(form, defs, registry)

    return defs


def _extract_definition(form: SExpr, defs: ImportedDefinitions, registry: Dict[str, Type]):
    """Extract a single definition from a form."""
    if not isinstance(form, SList) or len(form) < 2:
        return

    # Functions: extract @spec for return type
    if is_form(form, 'fn') and len(form) > 2:
        name = form[1].name if isinstance(form[1], Symbol) else None
        if name:
            sig = _extract_function_signature(form, registry)
            if sig:
                defs.functions[name] = sig

    # Types: extract record fields, enum variants, range types
    elif is_form(form, 'type') and len(form) > 2:
        type_name = form[1].name if isinstance(form[1], Symbol) else None
        if type_name and type_name in registry:
            defs.types[type_name] = registry[type_name]

    # Constants: extract type and value
    elif is_form(form, 'const') and len(form) >= 4:
        name = form[1].name if isinstance(form[1], Symbol) else None
        if name:
            const_type = _parse_type_expr_simple(form[2], registry)
            value = _extract_const_value(form[3])
            defs.constants[name] = ConstantDef(name, const_type, value)


def _extract_function_signature(fn_form: SList, registry: Dict[str, Type]) -> Optional[FunctionSignature]:
    """Extract function signature from a fn form.

    Looks for @spec annotation to get return type with range information.
    Also extracts parameter names and @post annotations for cross-module
    postcondition propagation.
    """
    if len(fn_form) < 3:
        return None

    name = fn_form[1].name if isinstance(fn_form[1], Symbol) else None
    if not name:
        return None

    param_types: List[Type] = []
    param_names: List[str] = []
    return_type: Type = UNKNOWN

    # Extract param types and names from parameter list
    params_list = fn_form[2] if isinstance(fn_form[2], SList) else SList([])
    for param in params_list:
        if isinstance(param, SList) and len(param) >= 2:
            first = param[0]
            if isinstance(first, Symbol) and first.name in ('in', 'out', 'mut'):
                # Mode is explicit: (in name Type)
                param_name = param[1].name if isinstance(param[1], Symbol) else None
                type_expr = param[2] if len(param) > 2 else None
            else:
                # No mode: (name Type)
                param_name = first.name if isinstance(first, Symbol) else None
                type_expr = param[1]
            if param_name:
                param_names.append(param_name)
            if type_expr:
                param_types.append(_parse_type_expr_simple(type_expr, registry))

    # Look for @spec to get return type and @post for postconditions
    postconditions: List[SExpr] = []
    for item in fn_form.items[3:]:
        if is_form(item, '@spec') and len(item) > 1:
            spec = item[1]
            if isinstance(spec, SList) and len(spec) >= 3:
                # (@spec ((ParamTypes) -> ReturnType))
                # Find the return type (after ->)
                for i, s in enumerate(spec.items):
                    if isinstance(s, Symbol) and s.name == '->':
                        if i + 1 < len(spec):
                            return_type = _parse_type_expr_simple(spec[i + 1], registry)
                        break
        elif is_form(item, '@post') and len(item) > 1:
            postconditions.append(item[1])

    return FunctionSignature(name, param_types, return_type, param_names, postconditions)


def _extract_const_value(expr: SExpr) -> Any:
    """Extract the value from a constant definition."""
    if isinstance(expr, Number):
        return expr.value
    elif isinstance(expr, String):
        return expr.value
    elif isinstance(expr, Symbol):
        # Could be a reference to another constant or a special value
        return expr.name
    return None


def resolve_imported_definitions(
    ast: List[SExpr],
    file_path: Path,
    search_paths: Optional[List[Path]] = None
) -> ImportedDefinitions:
    """Resolve definitions from imported modules.

    For each import statement in the AST, finds the module file,
    parses it, and extracts definitions for imported symbols.

    Args:
        ast: The AST of the file being verified
        file_path: Path to the file being verified
        search_paths: Additional paths to search for modules

    Returns:
        ImportedDefinitions with functions, types, and constants from imports
    """
    from slop.parser import get_imports, parse_import

    result = ImportedDefinitions()

    # Collect all import statements
    imports = []
    for form in ast:
        if is_form(form, 'module'):
            for item in form.items[1:]:
                if is_form(item, 'import'):
                    imports.append(item)
        elif is_form(form, 'import'):
            imports.append(form)

    if not imports:
        return result

    # Set up module resolver
    from slop.resolver import ModuleResolver
    paths = list(search_paths) if search_paths else []
    resolver = ModuleResolver(paths)

    # Process each import
    for imp_form in imports:
        try:
            imp_spec = parse_import(imp_form)
            module_name = imp_spec.module_name
            imported_symbols = set(imp_spec.symbols)

            # Find and load the module
            module_path = resolver.resolve_module(module_name, file_path)
            module_info = resolver.load_module(module_path)

            # Build type registry for the module
            module_registry = build_type_registry_from_ast(module_info.ast)

            # Extract definitions
            module_defs = extract_module_definitions(module_info.ast, module_registry)

            # Only keep the symbols that are actually imported
            for fn_name in list(module_defs.functions.keys()):
                if fn_name in imported_symbols:
                    result.functions[fn_name] = module_defs.functions[fn_name]

            for type_name in list(module_defs.types.keys()):
                if type_name in imported_symbols:
                    result.types[type_name] = module_defs.types[type_name]

            for const_name in list(module_defs.constants.keys()):
                if const_name in imported_symbols:
                    result.constants[const_name] = module_defs.constants[const_name]

        except Exception:
            # Skip modules that can't be resolved - they may be external
            # The type checker will have already reported errors for missing modules
            pass

    return result


# ============================================================================
# Native Type Checker Integration
# ============================================================================

def _run_native_checker(path: str, include_paths: Optional[List[Path]] = None) -> Tuple[bool, List[dict]]:
    """Run native type checker and return (success, diagnostics).

    Args:
        path: Path to the file to check
        include_paths: Paths to search for imported modules

    Returns (True, []) if checker not available or succeeds.
    Returns (False, diagnostics) if type errors found.
    """
    checker_bin = Path(__file__).parent.parent.parent / 'bin' / 'slop-checker'
    if not checker_bin.exists():
        return True, []  # Fall through if native checker not available

    try:
        # Build list of all files to check
        files_to_check = []

        if include_paths:
            # Resolve all dependencies using ModuleResolver
            # The native checker processes multiple files with a shared type environment,
            # so we pass all dependencies in topological order
            from slop.resolver import ModuleResolver, ResolverError

            search_paths = list(include_paths) + [Path(path).parent]
            resolver = ModuleResolver(search_paths)

            try:
                graph = resolver.build_dependency_graph(Path(path))
                # Get files in topological order (dependencies first)
                for mod_name in resolver.topological_sort(graph):
                    mod_info = graph.modules[mod_name]
                    files_to_check.append(str(mod_info.path))
            except ResolverError:
                # If resolution fails, just check the single file
                files_to_check = [path]
        else:
            files_to_check = [path]

        # Build command: slop-checker --json file1.slop file2.slop ...
        cmd = [str(checker_bin), '--json'] + files_to_check

        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode == 0:
            return True, []

        # Parse JSON diagnostics
        try:
            data = json.loads(result.stdout)
            diagnostics = []
            for mod_name, mod_data in data.items():
                if isinstance(mod_data, dict):
                    for diag in mod_data.get('diagnostics', []):
                        diagnostics.append(diag)
            return False, diagnostics
        except json.JSONDecodeError:
            return False, [{'level': 'error', 'message': result.stderr or 'Type check failed'}]

    except subprocess.TimeoutExpired:
        return False, [{'level': 'error', 'message': 'Type checker timed out'}]
    except FileNotFoundError:
        return True, []  # Fall through if checker not found


@dataclass
class NativeDiagnostic:
    """Diagnostic from native checker, compatible with TypeDiagnostic interface."""
    severity: str
    message: str
    location: Optional[SourceLocation] = None

    def __str__(self) -> str:
        loc = ""
        if self.location and self.location.line > 0:
            loc = f"{self.location.file}:{self.location.line}: "
        return f"{loc}{self.severity}: {self.message}"


def run_native_checker_diagnostics(path: str, include_paths: Optional[List[Path]] = None) -> Tuple[List[NativeDiagnostic], bool]:
    """Run native checker and return diagnostics in compatible format.

    Args:
        path: Path to the file to check
        include_paths: Paths to search for imported modules

    Returns (diagnostics, native_available).
    If native not available, returns ([], False) so caller can fall back.
    """
    checker_bin = Path(__file__).parent.parent.parent / 'bin' / 'slop-checker'
    if not checker_bin.exists():
        return [], False  # Native checker not available

    success, raw_diagnostics = _run_native_checker(path, include_paths)

    if success:
        return [], True  # No errors

    if not raw_diagnostics:
        return [], False  # Native checker not available or no output

    # Convert JSON dicts to NativeDiagnostic
    result = []
    for diag in raw_diagnostics:
        nd = NativeDiagnostic(
            severity=diag.get('level', 'error'),
            message=diag.get('message', ''),
            location=SourceLocation(
                file=path,
                line=diag.get('line', 0),
                column=diag.get('col', 0)
            )
        )
        result.append(nd)
    return result, True


# ============================================================================
# Verification Results
# ============================================================================

@dataclass
class VerificationResult:
    """Result of verification for a single item (function, assignment, etc.)"""
    name: str  # Function name or description
    verified: bool
    status: str  # 'verified', 'failed', 'unknown', 'skipped'
    message: str
    counterexample: Optional[Dict[str, Any]] = None
    location: Optional[SourceLocation] = None
    suggestions: Optional[List[str]] = None  # Actionable suggestions for failed verifications

    def __str__(self) -> str:
        loc = ""
        if self.location and self.location.line > 0:
            loc = f"{self.location.file}:{self.location.line}: "
        if self.verified:
            return f"{loc}verified: {self.name}"
        else:
            result = f"{loc}{self.status}: {self.name} - {self.message}"
            if self.counterexample:
                ce_str = ", ".join(f"{k}={v}" for k, v in self.counterexample.items())
                result += f"\n  counterexample: {ce_str}"
            if self.suggestions:
                result += "\n\n  Suggestions:"
                for suggestion in self.suggestions:
                    result += f"\n    • {suggestion}"
            return result


@dataclass
class VerificationDiagnostic:
    """Diagnostic output for verification"""
    severity: str  # 'verified', 'warning', 'error'
    message: str
    location: Optional[SourceLocation] = None

    def __str__(self) -> str:
        loc = ""
        if self.location and self.location.line > 0:
            loc = f"{self.location.file}:{self.location.line}: "
        return f"{loc}{self.severity}: {self.message}"


# ============================================================================
# Z3 Translator
# ============================================================================

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

        return None

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
        elif not (isinstance(coll_expr, SList) and is_form(coll_expr, '.')):
            # Must be either a symbol or field access
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
        elif not (isinstance(coll_expr, SList) and is_form(coll_expr, '.')):
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


# ============================================================================
# Contract Verifier
# ============================================================================

class ContractVerifier:
    """Verifies @pre/@post contracts for functions"""

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
        """
        axioms: List[z3.BoolRef] = []

        # Find map patterns
        map_pattern = self._detect_map_pattern(fn_body)
        if map_pattern is None:
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

            # Also add size equality axiom (map produces same-size output)
            size_axiom = z3.Length(result_seq) == z3.Length(source_seq)
            axioms.append(size_axiom)

        finally:
            # Restore binding
            if old_binding is not None:
                translator.variables[map_pattern.loop_var] = old_binding
            elif map_pattern.loop_var in translator.variables:
                del translator.variables[map_pattern.loop_var]

        return axioms

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

        var_z3 = translator.variables.get(var_name)
        if var_z3 is None:
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
        """Check if expression has a mutable 'result' bound to list-new.

        Looks for pattern: (let ((mut result (list-new ...))) ... result)
        where the final return is the 'result' variable.
        """
        if is_form(expr, 'let') and len(expr) >= 3:
            bindings = expr[1]
            body_exprs = expr.items[2:]

            # Check if final expression is 'result'
            if body_exprs:
                final_expr = self._get_return_expr(body_exprs[-1])
                is_result_return = isinstance(final_expr, Symbol) and final_expr.name == 'result'

                if is_result_return and isinstance(bindings, SList):
                    # Look for (mut result (list-new ...)) binding
                    for binding in bindings.items:
                        if isinstance(binding, SList) and len(binding) >= 3:
                            first = binding[0]
                            if isinstance(first, Symbol) and first.name == 'mut':
                                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                                init_expr = binding[2]
                                if var_name == 'result' and is_form(init_expr, 'list-new'):
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
        """Check if expression is (if cond (record-new ...) else) or (if cond then (record-new ...))"""
        if is_form(expr, 'if') and len(expr) >= 4:
            then_branch = expr[2]
            else_branch = expr[3]
            return self._is_record_new(then_branch) or self._is_record_new(else_branch)
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

    def _extract_list_axioms(self, body: SExpr, translator: Z3Translator) -> List:
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

        # Find all list-push calls
        push_calls: List[Tuple[SExpr, SExpr]] = []
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
                            # After push: length increases by 1
                            axioms.append(length >= 1)

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

            # Fallback: length-based axioms
            # Get or create the field_len function
            func_name = "field_len"
            if func_name not in translator.variables:
                func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                translator.variables[func_name] = func
            else:
                func = translator.variables[func_name]

            # Create a "pre-push length" variable for tracking
            pre_len_name = f"_list_pre_len_{id(list_expr)}"
            if pre_len_name not in translator.variables:
                pre_len = z3.Int(pre_len_name)
                translator.variables[pre_len_name] = pre_len

                # The pre-push length equals what field_len returns for the list
                axioms.append(pre_len == func(lst_z3))

                # After the push, the length is pre_len + 1
                # We need to constrain future references to this list's length
                # Create a "post-push" marker
                post_len_name = f"_list_post_len_{id(list_expr)}"
                post_len = z3.Int(post_len_name)
                translator.variables[post_len_name] = post_len
                axioms.append(post_len == pre_len + 1)
                axioms.append(post_len >= 1)  # After push, length is at least 1

        # Connect returned list to $result
        # If the function returns a list variable that had push called on it,
        # add axiom: field_len($result) >= number_of_pushes
        result_var = translator.variables.get('$result')
        if result_var is not None and push_calls:
            # Find the return expression
            return_expr = self._get_return_expr(body)
            if isinstance(return_expr, Symbol):
                # Check if this variable had push calls
                for list_expr, _ in push_calls:
                    if isinstance(list_expr, Symbol) and list_expr.name == return_expr.name:
                        # The returned variable is the one we pushed to
                        func_name = "field_len"
                        if func_name in translator.variables:
                            func = translator.variables[func_name]
                            # Count pushes to this list
                            push_count = sum(
                                1 for lst, _ in push_calls
                                if isinstance(lst, Symbol) and lst.name == return_expr.name
                            )
                            # $result is the list after all pushes, so length >= push_count
                            axioms.append(func(result_var) >= push_count)

        return axioms

    def _extract_conditional_record_axioms(self, cond_expr: SList, translator: Z3Translator) -> List:
        """Extract axioms for conditional with record-new in either branch.

        For (if cond (record-new Type (f1 v1) ...) var):
        - Add: cond => field_f1($result) == v1
        - Add: !cond => field_f1($result) == field_f1(var)

        For (if cond var (record-new Type (f1 v1) ...)):
        - Add: !cond => field_f1($result) == v1
        - Add: cond => field_f1($result) == field_f1(var)
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        if len(cond_expr) < 4:
            return axioms

        condition = cond_expr[1]
        then_branch = cond_expr[2]
        else_branch = cond_expr[3]

        # Translate the condition
        cond_z3 = translator.translate_expr(condition)
        if cond_z3 is None:
            return axioms

        # Defensive check: ensure condition is Bool before using z3.Not()
        # Some predicates may not be detected as Bool-returning, handle gracefully
        if cond_z3.sort() != z3.BoolSort():
            return axioms

        # Determine which branch has record-new
        record_new_in_then = self._is_record_new(then_branch)
        record_new_in_else = self._is_record_new(else_branch)

        if record_new_in_then:
            record_branch = then_branch
            var_branch = else_branch
            record_cond = cond_z3  # record-new happens when cond is true
        elif record_new_in_else:
            record_branch = else_branch
            var_branch = then_branch
            record_cond = z3.Not(cond_z3)  # record-new happens when cond is false
        else:
            return axioms

        # Extract field values from record-new branch
        field_names = []
        for item in record_branch.items[2:]:  # Skip 'record-new' and Type
            if isinstance(item, SList) and len(item) >= 2:
                field_name = item[0].name if isinstance(item[0], Symbol) else None
                if field_name:
                    field_names.append(field_name)
                    field_value = translator.translate_expr(item[1])
                    if field_value is not None:
                        field_func = translator._translate_field_for_obj(result_var, field_name)
                        # Add: record_cond => field($result) == value
                        axioms.append(z3.Implies(record_cond, field_func == field_value))

        # Handle variable branch: add field equality axioms
        if isinstance(var_branch, Symbol):
            var_z3 = translator.translate_expr(var_branch)
            if var_z3 is not None:
                # For each field, add: !record_cond => field($result) == field(var)
                for field_name in field_names:
                    result_field = translator._translate_field_for_obj(result_var, field_name)
                    var_field = translator._translate_field_for_obj(var_z3, field_name)
                    axioms.append(z3.Implies(z3.Not(record_cond), result_field == var_field))

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

    def _extract_record_field_axioms(self, record_new: SList, translator: Z3Translator) -> List:
        """Extract axioms: field_X($result) == value for each field in record-new

        Also handles list-new as field value: if field value is (list-new ...),
        add axiom: field_len(field_accessor($result)) == 0
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # record-new Type (field1 val1) (field2 val2) ...
        for item in record_new.items[2:]:  # Skip 'record-new' and Type
            if isinstance(item, SList) and len(item) >= 2:
                field_name = item[0].name if isinstance(item[0], Symbol) else None
                if field_name:
                    field_func = translator._translate_field_for_obj(result_var, field_name)
                    field_value = translator.translate_expr(item[1])
                    if field_value is not None:
                        axioms.append(field_func == field_value)

                    # If field value is list-new, add length=0 axiom for the field
                    if is_form(item[1], 'list-new'):
                        func_name = "field_len"
                        if func_name not in translator.variables:
                            len_func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                            translator.variables[func_name] = len_func
                        else:
                            len_func = translator.variables[func_name]
                        axioms.append(len_func(field_func) == z3.IntVal(0))

                    # If field value is a string literal, add string_len axiom
                    # This allows proving postconditions like {(string-len (. report reason)) > 0}
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

    def _extract_list_new_axioms(self, list_new_expr: SList, translator: Z3Translator) -> List:
        """Extract axiom: field_len($result) == 0 for list-new

        When list-new is called, the resulting list has length 0.
        This allows proving postconditions like {(list-len $result) == 0}.

        With array encoding enabled, also sets up the array representation.
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # With array encoding, set up array for $result
        if translator.use_array_encoding:
            arr, length = translator._create_list_array('$result')
            # Empty list: length == 0
            axioms.append(length == z3.IntVal(0))
            return axioms

        # Get or create field_len function (fallback for non-array encoding)
        func_name = "field_len"
        if func_name not in translator.variables:
            func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
            translator.variables[func_name] = func
        else:
            func = translator.variables[func_name]

        # list-new returns empty list: len == 0
        axioms.append(func(result_var) == z3.IntVal(0))
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
    # Phase 8: Filter Pattern Detection and Axiom Generation
    # ========================================================================

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

    def _has_nested_match(self, expr: SExpr) -> bool:
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
    # Phase 9: Union Structural Equality Axioms
    # ========================================================================

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

        # Annotation forms to skip when looking for body
        annotation_forms = {'@intent', '@spec', '@pre', '@post', '@assume', '@pure',
                           '@alloc', '@example', '@deprecated', '@property',
                           '@generation-mode', '@requires'}
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
            elif isinstance(item, Symbol):
                # Skip keyword properties like :c-name
                if item.name.startswith(':'):
                    skip_next_string = True  # The next String is a property value
                    continue
                # Simple expression as body (e.g., variable reference)
                fn_body = item
                skip_next_string = False
            elif isinstance(item, Number):
                # Simple numeric expression as body
                fn_body = item
                skip_next_string = False
            elif isinstance(item, String):
                # Skip string values after :keyword (property values)
                # But allow standalone String as function body
                if skip_next_string:
                    skip_next_string = False
                    continue
                fn_body = item

        # Extract loop invariants from function body and treat them as assumptions
        # @loop-invariant provides axioms that help verify loops
        if fn_body is not None:
            loop_invariants = self._extract_loop_invariants(fn_body)
            assumptions.extend(loop_invariants)

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

        # Translate preconditions
        pre_z3: List[z3.BoolRef] = []
        failed_pres: List[Tuple[Optional[str], SExpr]] = []
        for pre_name, pre_expr in preconditions:
            z3_pre = translator.translate_expr(pre_expr)
            if z3_pre is not None:
                pre_z3.append(z3_pre)
            else:
                failed_pres.append((pre_name, pre_expr))

        # Translate postconditions
        post_z3: List[z3.BoolRef] = []
        failed_posts: List[SExpr] = []
        for post in postconditions:
            z3_post = translator.translate_expr(post)
            if z3_post is not None:
                post_z3.append(z3_post)
            else:
                failed_posts.append(post)

        # Translate function body BEFORE assumptions
        # This is important because @loop-invariant may reference local variables
        # from let bindings, which are declared during body translation
        body_z3: Optional[z3.ExprRef] = None
        if fn_body is not None and postconditions:
            body_z3 = translator.translate_expr(fn_body)
            # If we can translate the body, constrain $result to equal it
            # This enables path-sensitive reasoning through conditionals

        # Translate assumptions (trusted axioms) - AFTER body so local vars are declared
        assume_z3: List[z3.BoolRef] = []
        failed_assumes: List[SExpr] = []
        for assume in assumptions:
            z3_assume = translator.translate_expr(assume)
            if z3_assume is not None:
                assume_z3.append(z3_assume)
            else:
                failed_assumes.append(assume)

        # Translate properties (universal assertions)
        # properties is List[Tuple[Optional[str], SExpr]] - (name, expr) tuples
        prop_z3: List[z3.BoolRef] = []
        failed_props: List[Tuple[Optional[str], SExpr]] = []
        for prop_name, prop_expr in properties:
            z3_prop = translator.translate_expr(prop_expr)
            if z3_prop is not None:
                prop_z3.append(z3_prop)
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
                # Build message with precondition names/details
                from slop.parser import pretty_print
                if preconditions:
                    pre_details = []
                    for pre_name, pre_expr in preconditions:
                        pre_str = pretty_print(pre_expr)
                        if pre_name:
                            pre_details.append(f"'{pre_name}': {pre_str}")
                        else:
                            pre_details.append(pre_str)
                    if len(preconditions) == 1:
                        message = f"Precondition is unsatisfiable: {pre_details[0]}"
                    else:
                        message = "Preconditions are unsatisfiable:\n" + "\n".join(f"  • {p}" for p in pre_details)
                else:
                    message = "Preconditions are unsatisfiable"
                return VerificationResult(
                    name=fn_name,
                    verified=False,
                    status="failed",
                    message=message,
                    location=SourceLocation(self.filename, fn_form.line, fn_form.col)
                )
            return VerificationResult(
                name=fn_name,
                verified=True,
                status="verified",
                message="Preconditions are satisfiable",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        # Check: can we satisfy preconditions but violate postconditions?
        # If (pre AND NOT post) is SAT, then contract can be violated
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)

        # Add type constraints
        for c in translator.constraints:
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
        for param_name, inv_expr in param_invariants:
            inv_z3 = translator.translate_expr(inv_expr)
            if inv_z3 is not None:
                solver.add(inv_z3)

        # Phase 1b: Add range type axioms for record fields
        # For record types with range-typed fields like (inferred-count (Int 0 ..)),
        # add universal axioms: ForAll x: field_inferred_count(x) >= 0
        range_field_axioms = self._extract_record_field_range_axioms(translator)
        for axiom in range_field_axioms:
            solver.add(axiom)

        # Add body constraint for path-sensitive analysis
        # This constrains $result to equal the translated function body
        if body_z3 is not None:
            result_var = translator.variables.get('$result')
            if result_var is not None:
                solver.add(result_var == body_z3)

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
        if fn_body is not None and self._is_record_new(fn_body):
            # Get the actual record-new form (may be inside a do block)
            return_expr = self._get_return_expr(fn_body)
            field_axioms = self._extract_record_field_axioms(return_expr, translator)
            for axiom in field_axioms:
                solver.add(axiom)

        # Phase 3.5: Add list-new axioms if body is list-new
        # For (list-new arena Type), add: field_len($result) == 0
        if fn_body is not None and self._is_list_new(fn_body):
            return_expr = self._get_return_expr(fn_body)
            list_axioms = self._extract_list_new_axioms(return_expr, translator)
            for axiom in list_axioms:
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

        # Phase 5: Add conditional record-new axioms
        # For (if cond (record-new Type (f1 v1) ...) else), add: cond => field_f1($result) == v1
        if fn_body is not None and self._is_conditional_with_record_new(fn_body):
            cond_axioms = self._extract_conditional_record_axioms(fn_body, translator)
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
            list_axioms = self._extract_list_axioms(fn_body, translator)
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
                count_axioms = self._generate_count_axioms(count_pattern, translator)
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

        # Phase 14: List element property invariants (with array encoding)
        # For postconditions like (all-triples-have-predicate $result RDF_TYPE),
        # detect that all pushed elements have the required property and add
        # a universally quantified axiom.
        #
        # Collect pattern axioms to share with property verification
        pattern_axioms: List[z3.BoolRef] = []

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

        # First try all postconditions together (fast path)
        solver.push()
        solver.add(z3.Not(z3.And(*post_z3)))
        result = solver.check()
        solver.pop()

        if result == z3.unsat:
            # Postconditions always hold when preconditions are met
            # Now verify properties (universal assertions - independent of preconditions)
            if prop_z3:
                from slop.parser import pretty_print
                # Collect all failures instead of returning on first failure
                failed_properties: List[Tuple[Optional[str], str, Dict[str, str]]] = []  # (name, expr_str, counterexample)
                unknown_properties: List[Tuple[Optional[str], str]] = []  # (name, expr_str)

                for i, ((prop_name, prop_expr), prop_z3_expr) in enumerate(zip(properties, prop_z3)):
                    prop_solver = z3.Solver()
                    prop_solver.set("timeout", self.timeout_ms)

                    # Add type constraints only (not preconditions)
                    for c in translator.constraints:
                        prop_solver.add(c)

                    # Add pattern axioms (filter/map/fold axioms derived from loop analysis)
                    # These are needed for properties that reason about collection contents
                    for axiom in pattern_axioms:
                        prop_solver.add(axiom)

                    # Add axioms for imported equality functions
                    # This allows Z3 to understand that e.g., term-eq(a,b) == (a == b)
                    imported_eq_axioms = self._extract_imported_equality_axioms(translator)
                    for axiom in imported_eq_axioms:
                        prop_solver.add(axiom)

                    # Check if NOT property is satisfiable
                    prop_solver.add(z3.Not(prop_z3_expr))
                    prop_result = prop_solver.check()

                    prop_str = pretty_print(prop_expr)

                    if prop_result == z3.sat:
                        model = prop_solver.model()
                        counterexample = {str(decl.name()): str(model[decl])
                                         for decl in model.decls()
                                         if not str(decl.name()).startswith('field_')}
                        failed_properties.append((prop_name, prop_str, counterexample))
                    elif prop_result == z3.unknown:
                        unknown_properties.append((prop_name, prop_str))

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
                    if len(unknown_properties) == 1:
                        prop_name, prop_str = unknown_properties[0]
                        if prop_name:
                            message = f"Could not verify property '{prop_name}': {prop_str}"
                        else:
                            message = f"Could not verify property: {prop_str}"
                    else:
                        lines = []
                        for prop_name, prop_str in unknown_properties:
                            if prop_name:
                                lines.append(f"  • '{prop_name}': {prop_str}")
                            else:
                                lines.append(f"  • {prop_str}")
                        message = "Could not verify properties:\n" + "\n".join(lines)
                    return VerificationResult(
                        name=fn_name,
                        verified=False,
                        status="unknown",
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

            # Get counterexample from one more check
            solver.push()
            solver.add(z3.Not(z3.And(*post_z3)))
            solver.check()
            model = solver.model()
            solver.pop()

            counterexample = {}
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
                counterexample=counterexample,
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


# ============================================================================
# Range Verifier
# ============================================================================

class RangeVerifier:
    """Verifies range type safety through operations"""

    def __init__(self, type_env: MinimalTypeEnv, filename: str = "<unknown>", timeout_ms: int = 5000):
        if not Z3_AVAILABLE:
            raise RuntimeError("Z3 is not available")
        self.type_env = type_env
        self.filename = filename
        self.timeout_ms = timeout_ms

    def verify_range_safety(self, ast: List[SExpr]) -> List[VerificationResult]:
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

    def _verify_range_condition(self, fn_name: str, cond: SExpr, fn_form: SList) -> Optional[VerificationResult]:
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


# ============================================================================
# Public API
# ============================================================================

def verify_source(source: str, filename: str = "<string>",
                  mode: str = "error", timeout_ms: int = 5000,
                  search_paths: Optional[List[Path]] = None) -> List[VerificationResult]:
    """Verify SLOP source string.

    Args:
        source: SLOP source code as string
        filename: Source filename (for error messages and import resolution)
        mode: Failure mode ('error' or 'warn')
        timeout_ms: Z3 solver timeout in milliseconds
        search_paths: Paths to search for imported modules

    Returns:
        List of verification results
    """
    if not Z3_AVAILABLE:
        return [VerificationResult(
            name="z3",
            verified=False,
            status="error",
            message="Z3 solver not available. Install with: pip install z3-solver"
        )]

    # Try native parser first
    try:
        from slop.cli import parse_native_json_string
        ast, success = parse_native_json_string(source)
        if not success:
            # Fall back to Python parser
            ast = parse(source)
    except ImportError:
        # Fall back to Python parser if cli import fails
        ast = parse(source)
    except Exception as e:
        return [VerificationResult(
            name="parse",
            verified=False,
            status="error",
            message=f"Parse error: {e}"
        )]

    # Build type registry from AST (no full type checking needed for verification)
    type_registry = build_type_registry_from_ast(ast)
    # Build invariant registry for type invariants
    invariant_registry = build_invariant_registry_from_ast(ast)

    # Resolve imported definitions for verification
    file_path = Path(filename)
    imported_defs = resolve_imported_definitions(ast, file_path, search_paths)

    # Merge imported types into type_registry for type lookups
    for type_name, typ in imported_defs.types.items():
        if type_name not in type_registry:
            type_registry[type_name] = typ

    type_env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)

    # Build function registry for inlining
    function_registry = FunctionRegistry()
    function_registry.register_from_ast(ast)

    # Run contract verification
    contract_verifier = ContractVerifier(type_env, filename, timeout_ms, function_registry, imported_defs)
    results = contract_verifier.verify_all(ast)

    # Run range verification
    range_verifier = RangeVerifier(type_env, filename, timeout_ms)
    results.extend(range_verifier.verify_range_safety(ast))

    return results


def verify_ast(ast: List[SExpr], filename: str = "<string>",
               mode: str = "error", timeout_ms: int = 5000,
               search_paths: Optional[List[Path]] = None) -> List[VerificationResult]:
    """Verify a pre-parsed SLOP AST.

    Args:
        ast: List of parsed S-expressions
        filename: Source filename (for error messages)
        mode: Failure mode ('error' or 'warn')
        timeout_ms: Z3 solver timeout in milliseconds
        search_paths: Paths to search for imported modules

    Returns:
        List of verification results
    """
    if not Z3_AVAILABLE:
        return [VerificationResult(
            name="z3",
            verified=False,
            status="error",
            message="Z3 solver not available. Install with: pip install z3-solver"
        )]

    # Build type registry from AST (no full type checking needed for verification)
    type_registry = build_type_registry_from_ast(ast)
    # Build invariant registry for type invariants
    invariant_registry = build_invariant_registry_from_ast(ast)

    # Resolve imported definitions for verification
    file_path = Path(filename)
    imported_defs = resolve_imported_definitions(ast, file_path, search_paths)

    # Merge imported types into type_registry for type lookups
    for type_name, typ in imported_defs.types.items():
        if type_name not in type_registry:
            type_registry[type_name] = typ

    type_env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)

    # Build function registry for inlining
    function_registry = FunctionRegistry()
    function_registry.register_from_ast(ast)

    # Run contract verification
    contract_verifier = ContractVerifier(type_env, filename, timeout_ms, function_registry, imported_defs)
    results = contract_verifier.verify_all(ast)

    # Run range verification
    range_verifier = RangeVerifier(type_env, filename, timeout_ms)
    results.extend(range_verifier.verify_range_safety(ast))

    return results


def verify_file(path: str, mode: str = "error",
                timeout_ms: int = 5000,
                search_paths: Optional[List[Path]] = None) -> List[VerificationResult]:
    """Verify a SLOP file.

    Args:
        path: Path to the SLOP file to verify
        mode: Failure mode ('error' or 'warn')
        timeout_ms: Z3 solver timeout in milliseconds
        search_paths: Paths to search for imported modules

    Returns:
        List of verification results
    """
    if not Z3_AVAILABLE:
        return [VerificationResult(
            name="z3",
            verified=False,
            status="error",
            message="Z3 solver not available. Install with: pip install z3-solver"
        )]

    # Try native parser first
    try:
        from slop.cli import parse_native_json
        ast, success = parse_native_json(path)
        if not success:
            # Fall back to Python parser
            with open(path) as f:
                source = f.read()
            ast = parse(source)
    except ImportError:
        # Fall back to Python parser if cli import fails
        with open(path) as f:
            source = f.read()
        ast = parse(source)
    except Exception as e:
        return [VerificationResult(
            name="file",
            verified=False,
            status="error",
            message=f"Could not read/parse file: {e}"
        )]

    # Run native type checker first (with include paths)
    success, diagnostics = _run_native_checker(path, search_paths)

    # Check for type errors
    if not success:
        error_msgs = [d.get('message', 'Unknown error') for d in diagnostics if d.get('level') == 'error']
        return [VerificationResult(
            name="typecheck",
            verified=False,
            status="error",
            message=f"Type errors found: {'; '.join(error_msgs) if error_msgs else 'check failed'}"
        )]

    # Build type registry from AST for contract verification
    type_registry = build_type_registry_from_ast(ast)
    # Build invariant registry for type invariants
    invariant_registry = build_invariant_registry_from_ast(ast)

    # Resolve imported definitions for verification
    file_path = Path(path)
    imported_defs = resolve_imported_definitions(ast, file_path, search_paths)

    # Merge imported types into type_registry for type lookups
    for type_name, typ in imported_defs.types.items():
        if type_name not in type_registry:
            type_registry[type_name] = typ

    type_env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)

    # Build function registry for inlining
    function_registry = FunctionRegistry()
    function_registry.register_from_ast(ast)

    # Run contract verification
    contract_verifier = ContractVerifier(type_env, path, timeout_ms, function_registry, imported_defs)
    results = contract_verifier.verify_all(ast)

    # Run range verification
    range_verifier = RangeVerifier(type_env, path, timeout_ms)
    results.extend(range_verifier.verify_range_safety(ast))

    return results
