"""
SLOP Z3 Verifier - Contract and range verification using Z3 SMT solver

Verifies:
- @pre/@post contract consistency
- Range type safety through arithmetic operations
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Tuple, Union
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
    """
    type_registry: Dict[str, Type] = field(default_factory=dict)
    _var_types: Dict[str, Type] = field(default_factory=dict)

    def lookup_var(self, name: str) -> Optional[Type]:
        """Look up the type of a variable"""
        return self._var_types.get(name)

    def bind_var(self, name: str, typ: Type):
        """Bind a variable to a type"""
        self._var_types[name] = typ


# ============================================================================
# Type Registry Builder (extract types from AST without full type checking)
# ============================================================================

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

    elif is_form(body, 'Int') or (isinstance(body, SList) and len(body) >= 4):
        # Range type: (type Name (Int min .. max))
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
    """Parse range bounds from (Int min .. max) or similar."""
    if not isinstance(expr, SList) or len(expr) < 4:
        return None

    # Expected format: (Int min .. max) or (Int min ..max) etc.
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
# Native Type Checker Integration
# ============================================================================

def _run_native_checker(path: str) -> Tuple[bool, List[dict]]:
    """Run native type checker and return (success, diagnostics).

    Returns (True, []) if checker not available or succeeds.
    Returns (False, diagnostics) if type errors found.
    """
    checker_bin = Path(__file__).parent.parent.parent / 'bin' / 'slop-checker'
    if not checker_bin.exists():
        return True, []  # Fall through if native checker not available

    try:
        result = subprocess.run(
            [str(checker_bin), '--json', path],
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

    def __init__(self, type_env: MinimalTypeEnv, filename: str = "<unknown>"):
        if not Z3_AVAILABLE:
            raise RuntimeError("Z3 is not available")
        self.type_env = type_env
        self.filename = filename
        self.variables: Dict[str, z3.ExprRef] = {}
        self.constraints: List[z3.BoolRef] = []
        self.enum_values: Dict[str, int] = {}  # 'Fizz' -> 0, etc.
        self._build_enum_map()

    def _build_enum_map(self):
        """Build mapping from enum variant names to integer values"""
        for typ in self.type_env.type_registry.values():
            if isinstance(typ, EnumType):
                for i, variant in enumerate(typ.variants):
                    self.enum_values[variant] = i
                    self.enum_values[f"'{variant}"] = i

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
        if isinstance(expr, Number):
            if isinstance(expr.value, float):
                return z3.RealVal(expr.value)
            return z3.IntVal(int(expr.value))

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
                        lst = self.translate_expr(expr[1])
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

                # Control flow - path sensitive analysis
                if op == 'if':
                    return self._translate_if(expr)

                if op == 'cond':
                    return self._translate_cond(expr)

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

        if op == '>':
            return left > right
        if op == '<':
            return left < right
        if op == '>=':
            return left >= right
        if op == '<=':
            return left <= right
        if op == '==':
            return left == right
        if op == '!=':
            return left != right

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
            if arg is not None:
                return z3.Not(arg)
            return None

        if op == 'and' and len(expr) >= 3:
            args = [self.translate_expr(e) for e in expr.items[1:]]
            if all(a is not None for a in args):
                return z3.And(*args)
            return None

        if op == 'or' and len(expr) >= 3:
            args = [self.translate_expr(e) for e in expr.items[1:]]
            if all(a is not None for a in args):
                return z3.Or(*args)
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


# ============================================================================
# Contract Verifier
# ============================================================================

class ContractVerifier:
    """Verifies @pre/@post contracts for functions"""

    def __init__(self, type_env: MinimalTypeEnv, filename: str = "<unknown>", timeout_ms: int = 5000):
        if not Z3_AVAILABLE:
            raise RuntimeError("Z3 is not available")
        self.type_env = type_env
        self.filename = filename
        self.timeout_ms = timeout_ms

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
        preconditions: List[SExpr] = []
        postconditions: List[SExpr] = []
        assumptions: List[SExpr] = []  # @assume - trusted axioms for verification
        spec_return_type: Optional[Type] = None
        fn_body: Optional[SExpr] = None  # Function body for path-sensitive analysis

        # Annotation forms to skip when looking for body
        annotation_forms = {'@intent', '@spec', '@pre', '@post', '@assume', '@pure',
                           '@alloc', '@example', '@deprecated', '@property',
                           '@generation-mode', '@requires'}

        for item in fn_form.items[3:]:
            if is_form(item, '@pre') and len(item) > 1:
                preconditions.append(item[1])
            elif is_form(item, '@post') and len(item) > 1:
                postconditions.append(item[1])
            elif is_form(item, '@assume') and len(item) > 1:
                assumptions.append(item[1])
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
            elif isinstance(item, (Symbol, Number)):
                # Simple expression as body
                fn_body = item

        # Skip if no contracts to verify
        if not preconditions and not postconditions and not assumptions:
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

        # Create translator and declare parameters
        translator = Z3Translator(self.type_env, self.filename)

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

        # Translate preconditions
        pre_z3: List[z3.BoolRef] = []
        failed_pres: List[SExpr] = []
        for pre in preconditions:
            z3_pre = translator.translate_expr(pre)
            if z3_pre is not None:
                pre_z3.append(z3_pre)
            else:
                failed_pres.append(pre)

        # Translate postconditions
        post_z3: List[z3.BoolRef] = []
        failed_posts: List[SExpr] = []
        for post in postconditions:
            z3_post = translator.translate_expr(post)
            if z3_post is not None:
                post_z3.append(z3_post)
            else:
                failed_posts.append(post)

        # Translate assumptions (trusted axioms)
        assume_z3: List[z3.BoolRef] = []
        failed_assumes: List[SExpr] = []
        for assume in assumptions:
            z3_assume = translator.translate_expr(assume)
            if z3_assume is not None:
                assume_z3.append(z3_assume)
            else:
                failed_assumes.append(assume)

        # Translate function body for path-sensitive analysis
        body_z3: Optional[z3.ExprRef] = None
        if fn_body is not None and postconditions:
            body_z3 = translator.translate_expr(fn_body)
            # If we can translate the body, constrain $result to equal it
            # This enables path-sensitive reasoning through conditionals

        # Report translation failures
        if failed_pres:
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message=f"Could not translate {len(failed_pres)} precondition(s)",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        if failed_posts:
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message=f"Could not translate {len(failed_posts)} postcondition(s)",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        if failed_assumes:
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message=f"Could not translate {len(failed_assumes)} assumption(s)",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        if not post_z3 and not postconditions:
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
                return VerificationResult(
                    name=fn_name,
                    verified=False,
                    status="failed",
                    message="Preconditions are unsatisfiable",
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

        # Add body constraint for path-sensitive analysis
        # This constrains $result to equal the translated function body
        if body_z3 is not None:
            result_var = translator.variables.get('$result')
            if result_var is not None:
                solver.add(result_var == body_z3)

        # Add negation of postconditions
        solver.add(z3.Not(z3.And(*post_z3)))

        result = solver.check()

        if result == z3.unsat:
            # Postconditions always hold when preconditions are met
            return VerificationResult(
                name=fn_name,
                verified=True,
                status="verified",
                message="Contract verified",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )
        elif result == z3.sat:
            # Found a counterexample
            model = solver.model()
            counterexample = {}
            for decl in model.decls():
                name = decl.name()
                if not name.startswith('field_'):  # Skip internal functions
                    counterexample[name] = str(model[decl])

            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message="Contract may be violated",
                counterexample=counterexample,
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )
        else:
            # Unknown (timeout or undecidable)
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="unknown",
                message="Verification timed out or undecidable",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
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
                  mode: str = "error", timeout_ms: int = 5000) -> List[VerificationResult]:
    """Verify SLOP source string"""
    if not Z3_AVAILABLE:
        return [VerificationResult(
            name="z3",
            verified=False,
            status="error",
            message="Z3 solver not available. Install with: pip install z3-solver"
        )]

    try:
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
    type_env = MinimalTypeEnv(type_registry=type_registry)

    # Run contract verification
    contract_verifier = ContractVerifier(type_env, filename, timeout_ms)
    results = contract_verifier.verify_all(ast)

    # Run range verification
    range_verifier = RangeVerifier(type_env, filename, timeout_ms)
    results.extend(range_verifier.verify_range_safety(ast))

    return results


def verify_ast(ast: List[SExpr], filename: str = "<string>",
               mode: str = "error", timeout_ms: int = 5000) -> List[VerificationResult]:
    """Verify a pre-parsed SLOP AST.

    Args:
        ast: List of parsed S-expressions
        filename: Source filename (for error messages)
        mode: Failure mode ('error' or 'warn')
        timeout_ms: Z3 solver timeout in milliseconds

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
    type_env = MinimalTypeEnv(type_registry=type_registry)

    # Run contract verification
    contract_verifier = ContractVerifier(type_env, filename, timeout_ms)
    results = contract_verifier.verify_all(ast)

    # Run range verification
    range_verifier = RangeVerifier(type_env, filename, timeout_ms)
    results.extend(range_verifier.verify_range_safety(ast))

    return results


def verify_file(path: str, mode: str = "error",
                timeout_ms: int = 5000) -> List[VerificationResult]:
    """Verify a SLOP file"""
    if not Z3_AVAILABLE:
        return [VerificationResult(
            name="z3",
            verified=False,
            status="error",
            message="Z3 solver not available. Install with: pip install z3-solver"
        )]

    try:
        with open(path) as f:
            source = f.read()
        ast = parse(source)
    except Exception as e:
        return [VerificationResult(
            name="file",
            verified=False,
            status="error",
            message=f"Could not read file: {e}"
        )]

    # Run native type checker first
    success, diagnostics = _run_native_checker(path)

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
    type_env = MinimalTypeEnv(type_registry=type_registry)

    # Run contract verification
    contract_verifier = ContractVerifier(type_env, path, timeout_ms)
    results = contract_verifier.verify_all(ast)

    # Run range verification
    range_verifier = RangeVerifier(type_env, path, timeout_ms)
    results.extend(range_verifier.verify_range_safety(ast))

    return results
