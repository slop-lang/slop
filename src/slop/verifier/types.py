"""
Core dataclass types used throughout the verifier.

These are lightweight type containers with no dependencies on other verifier modules.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, TYPE_CHECKING

if TYPE_CHECKING:
    from slop.parser import SExpr
    from slop.types import Type


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
    type_registry: Dict[str, 'Type'] = field(default_factory=dict)
    _var_types: Dict[str, 'Type'] = field(default_factory=dict)
    invariant_registry: Optional['TypeInvariantRegistry'] = None

    def lookup_var(self, name: str) -> Optional['Type']:
        """Look up the type of a variable"""
        return self._var_types.get(name)

    def bind_var(self, name: str, typ: 'Type'):
        """Bind a variable to a type"""
        self._var_types[name] = typ

    def get_invariants_for_type(self, type_name: str) -> List['SExpr']:
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
    param_types: List['Type']  # Parameter types in order
    return_type: 'Type'  # Return type (may include range bounds)
    params: List[str] = field(default_factory=list)  # Parameter names for postcondition substitution
    postconditions: List['SExpr'] = field(default_factory=list)  # @post annotations
    assumptions: List['SExpr'] = field(default_factory=list)  # @assume annotations


@dataclass
class ConstantDef:
    """Definition of an imported constant."""
    name: str
    type: 'Type'
    value: Any  # String, int, float


@dataclass
class ImportedDefinitions:
    """Definitions extracted from imported modules for verification."""
    functions: Dict[str, FunctionSignature] = field(default_factory=dict)
    types: Dict[str, 'Type'] = field(default_factory=dict)  # RecordType, EnumType, UnionType, RangeType
    constants: Dict[str, ConstantDef] = field(default_factory=dict)

    def merge(self, other: 'ImportedDefinitions'):
        """Merge another ImportedDefinitions into this one."""
        self.functions.update(other.functions)
        self.types.update(other.types)
        self.constants.update(other.constants)


# Forward declaration for TypeInvariantRegistry - actual implementation in registry.py
class TypeInvariantRegistry:
    """Registry of type invariants extracted from @invariant annotations.

    This is a forward declaration - the full implementation is in registry.py.
    """

    def __init__(self):
        self.invariants: Dict[str, List['SExpr']] = {}

    def add_invariant(self, type_name: str, condition: 'SExpr'):
        """Add an invariant for a type"""
        if type_name not in self.invariants:
            self.invariants[type_name] = []
        self.invariants[type_name].append(condition)

    def get_invariants(self, type_name: str) -> List['SExpr']:
        """Get all invariants for a type"""
        return self.invariants.get(type_name, [])


__all__ = [
    'SourceLocation',
    'MinimalTypeEnv',
    'FunctionSignature',
    'ConstantDef',
    'ImportedDefinitions',
    'TypeInvariantRegistry',
]
