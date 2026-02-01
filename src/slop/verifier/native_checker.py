"""
Native type checker integration.

Provides functions to invoke the native slop-checker binary and
parse its diagnostics into a format usable by the verifier.
"""
from __future__ import annotations

import subprocess
import json
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Tuple

from .types import SourceLocation


def _run_native_checker(path: str, include_paths: Optional[List[Path]] = None) -> Tuple[bool, List[dict]]:
    """Run native type checker and return (success, diagnostics).

    Args:
        path: Path to the file to check
        include_paths: Paths to search for imported modules

    Returns (True, []) if checker not available or succeeds.
    Returns (False, diagnostics) if type errors found.
    """
    # Prefer merged slop-compiler binary, fall back to standalone slop-checker
    bin_dir = Path(__file__).parent.parent.parent.parent / 'bin'
    compiler_bin = bin_dir / 'slop-compiler'
    checker_bin = bin_dir / 'slop-checker'
    if compiler_bin.exists():
        use_bin = compiler_bin
        use_compiler = True
    elif checker_bin.exists():
        use_bin = checker_bin
        use_compiler = False
    else:
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

        # Build command
        cmd = [str(use_bin)]
        if use_compiler:
            cmd.append('check')
        cmd.extend(['--json'] + files_to_check)

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
    bin_dir = Path(__file__).parent.parent.parent.parent / 'bin'
    if not (bin_dir / 'slop-compiler').exists() and not (bin_dir / 'slop-checker').exists():
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


__all__ = [
    'NativeDiagnostic',
    '_run_native_checker',
    'run_native_checker_diagnostics',
]
