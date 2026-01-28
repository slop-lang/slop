"""
SLOP Z3 Verifier - Contract and range verification using Z3 SMT solver.

Verifies:
- @pre/@post contract consistency
- Range type safety through arithmetic operations
- @property universal assertions
"""
from __future__ import annotations

# Z3 setup and availability
from .z3_setup import Z3_AVAILABLE, z3, _find_system_z3

# Core types
from .types import (
    SourceLocation,
    MinimalTypeEnv,
    FunctionSignature,
    ConstantDef,
    ImportedDefinitions,
)

# Loop patterns
from .loop_patterns import (
    TypeInvariant,
    FilterPatternInfo,
    MapPatternInfo,
    FieldSource,
    InnerLoopInfo,
    NestedLoopPatternInfo,
    CountPatternInfo,
    FoldPatternInfo,
    FindPatternInfo,
    SetBinding,
    LoopContext,
    WhileLoopContext,
)

# SSA versioning
from .ssa import SSAVersion, SSAContext

# Registry classes
from .registry import FunctionDef, FunctionRegistry, TypeInvariantRegistry

# Type building
from .type_builder import (
    build_type_registry_from_ast,
    build_invariant_registry_from_ast,
)

# Import resolution
from .imports import (
    extract_module_definitions,
    resolve_imported_definitions,
)

# Native checker
from .native_checker import (
    NativeDiagnostic,
    _run_native_checker,
    run_native_checker_diagnostics,
)

# Results
from .results import VerificationResult, VerificationDiagnostic

# Weakest precondition
from .wp import WeakestPrecondition

# Invariant inference
from .invariant_inference import InferredInvariant, InvariantInferencer

# Z3 Translator
from .translator import Z3Translator

# Verifiers
from .contract_verifier import ContractVerifier
from .range_verifier import RangeVerifier

# Public API
from .api import verify_source, verify_ast, verify_file


__all__ = [
    # Z3 availability
    'Z3_AVAILABLE',
    'z3',
    '_find_system_z3',

    # Core types
    'SourceLocation',
    'MinimalTypeEnv',
    'FunctionSignature',
    'ConstantDef',
    'ImportedDefinitions',

    # Loop patterns
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

    # SSA
    'SSAVersion',
    'SSAContext',

    # Registry
    'FunctionDef',
    'FunctionRegistry',
    'TypeInvariantRegistry',

    # Type building
    'build_type_registry_from_ast',
    'build_invariant_registry_from_ast',

    # Imports
    'extract_module_definitions',
    'resolve_imported_definitions',

    # Native checker
    'NativeDiagnostic',
    '_run_native_checker',
    'run_native_checker_diagnostics',

    # Results
    'VerificationResult',
    'VerificationDiagnostic',

    # WP
    'WeakestPrecondition',

    # Invariant inference
    'InferredInvariant',
    'InvariantInferencer',

    # Translator
    'Z3Translator',

    # Verifiers
    'ContractVerifier',
    'RangeVerifier',

    # Public API
    'verify_source',
    'verify_ast',
    'verify_file',
]
