"""
SSA (Static Single Assignment) versioning for verification.

Manages variable versioning to enable precise reasoning about value flow
through assignments in loops and conditional statements.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Any, TYPE_CHECKING

from .z3_setup import Z3_AVAILABLE, z3

if TYPE_CHECKING:
    from slop.parser import SExpr
    from .translator import Z3Translator


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
    defining_expr: Optional['SExpr'] = None  # The expression that defined this version
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

    def init_variable(self, var_name: str, z3_var: Any, defining_expr: Optional['SExpr'] = None):
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

    def create_new_version(self, var_name: str, defining_expr: Optional['SExpr'] = None,
                           is_loop_version: bool = False) -> SSAVersion:
        """Create a new version of a variable (for set! or loop iteration).

        Returns the new SSAVersion with an appropriately typed Z3 variable.
        """
        if not Z3_AVAILABLE:
            raise RuntimeError("Z3 is not available")

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


__all__ = [
    'SSAVersion',
    'SSAContext',
]
