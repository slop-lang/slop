"""
SLOP File Discovery - Utilities for discovering .slop files in directories and globs

Supports:
- Directory paths (recursive search)
- Explicit file paths
- Glob patterns (e.g., "lib/**/*.slop")
"""

import fnmatch
from pathlib import Path
from typing import List, Optional, Set


def discover_slop_files(
    paths: List[str],
    pattern: str = "*.slop",
    exclude: Optional[List[str]] = None,
    recursive: bool = True,
    base_dir: Optional[Path] = None
) -> List[Path]:
    """Discover .slop files from paths (files, dirs, or globs).

    Args:
        paths: List of paths - can be directories, files, or glob patterns
        pattern: File pattern to match in directories (default: "*.slop")
        exclude: List of directory/file patterns to exclude
        recursive: Whether to search directories recursively (default: True)
        base_dir: Base directory for resolving relative paths (default: cwd)

    Returns:
        Sorted list of unique .slop file paths, sorted by modification time (newest first)
    """
    if base_dir is None:
        base_dir = Path.cwd()

    exclude = exclude or []
    discovered: Set[Path] = set()

    for path_str in paths:
        path = Path(path_str)

        # Make relative paths absolute based on base_dir
        if not path.is_absolute():
            path = base_dir / path

        if '**' in path_str or '*' in path_str or '?' in path_str:
            # Glob pattern - use glob matching
            discovered.update(_discover_from_glob(path_str, base_dir, exclude))
        elif path.is_file():
            # Explicit file
            if path.suffix == '.slop' and not _is_excluded(path, exclude, base_dir):
                discovered.add(path.resolve())
        elif path.is_dir():
            # Directory - search for .slop files
            discovered.update(_discover_from_directory(path, pattern, exclude, recursive, base_dir))

    # Sort by modification time (newest first), then by path for stability
    result = sorted(discovered, key=lambda p: (-p.stat().st_mtime if p.exists() else 0, str(p)))
    return result


def _discover_from_directory(
    directory: Path,
    pattern: str,
    exclude: List[str],
    recursive: bool,
    base_dir: Path
) -> Set[Path]:
    """Discover files in a directory matching the pattern."""
    discovered: Set[Path] = set()

    if recursive:
        glob_pattern = f"**/{pattern}"
    else:
        glob_pattern = pattern

    for file_path in directory.glob(glob_pattern):
        if file_path.is_file() and not _is_excluded(file_path, exclude, base_dir):
            discovered.add(file_path.resolve())

    return discovered


def _discover_from_glob(
    glob_pattern: str,
    base_dir: Path,
    exclude: List[str]
) -> Set[Path]:
    """Discover files matching a glob pattern."""
    discovered: Set[Path] = set()

    # Handle both absolute and relative glob patterns
    if Path(glob_pattern).is_absolute():
        # For absolute patterns, we need to break them down
        # This is tricky - just iterate from root
        parts = Path(glob_pattern).parts
        # Find where the glob starts
        root_parts = []
        for i, part in enumerate(parts):
            if '*' in part or '?' in part:
                break
            root_parts.append(part)

        if root_parts:
            root = Path(*root_parts)
            remaining = str(Path(*parts[len(root_parts):]))
            for file_path in root.glob(remaining):
                if file_path.is_file() and file_path.suffix == '.slop':
                    if not _is_excluded(file_path, exclude, base_dir):
                        discovered.add(file_path.resolve())
    else:
        # Relative glob pattern - use base_dir
        for file_path in base_dir.glob(glob_pattern):
            if file_path.is_file() and file_path.suffix == '.slop':
                if not _is_excluded(file_path, exclude, base_dir):
                    discovered.add(file_path.resolve())

    return discovered


def _is_excluded(
    file_path: Path,
    exclude: List[str],
    base_dir: Path
) -> bool:
    """Check if a file path matches any exclusion pattern."""
    if not exclude:
        return False

    # Get relative path for matching
    try:
        rel_path = file_path.resolve().relative_to(base_dir.resolve())
        rel_str = str(rel_path)
    except ValueError:
        # File is not under base_dir, use absolute path
        rel_str = str(file_path)

    for pattern in exclude:
        # Check if pattern matches file path or any parent directory
        if fnmatch.fnmatch(rel_str, pattern):
            return True
        if fnmatch.fnmatch(file_path.name, pattern):
            return True
        # Check if file is in an excluded directory
        for parent in file_path.parents:
            if fnmatch.fnmatch(parent.name, pattern):
                return True
            try:
                parent_rel = str(parent.resolve().relative_to(base_dir.resolve()))
                if fnmatch.fnmatch(parent_rel, pattern):
                    return True
            except ValueError:
                pass

    return False


def format_discovery_results(
    files: List[Path],
    base_dir: Optional[Path] = None
) -> str:
    """Format discovery results for display.

    Args:
        files: List of discovered file paths
        base_dir: Base directory for relative path display

    Returns:
        Formatted string showing discovered files
    """
    if not files:
        return "No .slop files found"

    if base_dir is None:
        base_dir = Path.cwd()

    lines = [f"Found {len(files)} .slop file(s):"]
    for f in files:
        try:
            rel = f.relative_to(base_dir)
            lines.append(f"  {rel}")
        except ValueError:
            lines.append(f"  {f}")

    return "\n".join(lines)
