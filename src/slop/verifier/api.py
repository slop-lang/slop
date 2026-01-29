"""
Public API for the SLOP verifier.

Provides the main entry points for verifying SLOP source code, AST, and files.
"""
from __future__ import annotations

from pathlib import Path
from typing import List, Optional, TYPE_CHECKING

from .z3_setup import Z3_AVAILABLE
from .types import MinimalTypeEnv
from .results import VerificationResult
from .registry import FunctionRegistry
from .type_builder import build_type_registry_from_ast, build_invariant_registry_from_ast
from .imports import resolve_imported_definitions
from .native_checker import _run_native_checker
from .contract_verifier import ContractVerifier
from .range_verifier import RangeVerifier

if TYPE_CHECKING:
    from slop.parser import SExpr


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

    # Use native parser - no Python fallback
    from slop.cli import parse_native_json_string
    ast, success = parse_native_json_string(source)
    if not success:
        error_msg = ast if isinstance(ast, str) else "Native parser failed"
        return [VerificationResult(
            name="parse",
            verified=False,
            status="error",
            message=f"Parse error: {error_msg}. Native parser is required."
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


def verify_ast(ast: List['SExpr'], filename: str = "<string>",
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

    # Use native parser - no Python fallback
    from slop.cli import parse_native_json
    ast, success = parse_native_json(path)
    if not success:
        error_msg = ast if isinstance(ast, str) else "Native parser failed"
        return [VerificationResult(
            name="parse",
            verified=False,
            status="error",
            message=f"Could not parse file: {error_msg}. Native parser is required."
        )]

    # Run native type checker first (with include paths)
    native_success, diagnostics = _run_native_checker(path, search_paths)

    # Check for type errors
    if not native_success:
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


__all__ = [
    'verify_source',
    'verify_ast',
    'verify_file',
]
