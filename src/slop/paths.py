"""
SLOP Path Resolution - Centralized path handling with SLOP_HOME support

Provides path resolution for SLOP resources with environment variable override.
When SLOP_HOME is set, it takes priority over package-relative paths.

Expected SLOP_HOME structure:
    $SLOP_HOME/
    ├── lib/std/     # Standard library modules
    ├── examples/    # Example SLOP programs
    ├── bin/         # Native toolchain binaries
    └── spec/        # Language specification files
"""

import os
from pathlib import Path
from typing import Optional, List


def get_slop_home() -> Optional[Path]:
    """Get SLOP_HOME path from environment if set and valid.

    Returns:
        Path to SLOP_HOME if set and exists, None otherwise.
    """
    slop_home = os.environ.get('SLOP_HOME')
    if slop_home:
        path = Path(slop_home)
        if path.is_dir():
            return path
    return None


def _get_package_root() -> Path:
    """Get the package root directory (project root).

    paths.py is at src/slop/paths.py, so package root is three levels up.
    """
    return Path(__file__).parent.parent.parent


def get_spec_dir() -> Optional[Path]:
    """Get the spec directory path.

    Checks SLOP_HOME/spec/ first, falls back to package-relative spec/.

    Returns:
        Path to spec directory if it exists, None otherwise.
    """
    # Check SLOP_HOME first
    slop_home = get_slop_home()
    if slop_home:
        spec_path = slop_home / "spec"
        if spec_path.is_dir():
            return spec_path

    # Fall back to package-relative path
    pkg_root = _get_package_root()
    spec_path = pkg_root / "spec"
    if spec_path.is_dir():
        return spec_path

    return None


def get_examples_dir() -> Optional[Path]:
    """Get the examples directory path.

    Checks SLOP_HOME/examples/ first, falls back to package-relative examples/.

    Returns:
        Path to examples directory if it exists, None otherwise.
    """
    # Check SLOP_HOME first
    slop_home = get_slop_home()
    if slop_home:
        examples_path = slop_home / "examples"
        if examples_path.is_dir():
            return examples_path

    # Fall back to package-relative path
    pkg_root = _get_package_root()
    examples_path = pkg_root / "examples"
    if examples_path.is_dir():
        return examples_path

    return None


def get_stdlib_dir() -> Optional[Path]:
    """Get the standard library directory path.

    Checks SLOP_HOME/lib/std/ first, falls back to package-relative lib/std/.

    Returns:
        Path to stdlib directory if it exists, None otherwise.
    """
    # Check SLOP_HOME first
    slop_home = get_slop_home()
    if slop_home:
        stdlib_path = slop_home / "lib" / "std"
        if stdlib_path.is_dir():
            return stdlib_path

    # Fall back to package-relative path
    pkg_root = _get_package_root()
    stdlib_path = pkg_root / "lib" / "std"
    if stdlib_path.is_dir():
        return stdlib_path

    return None


def get_bin_dir() -> Optional[Path]:
    """Get the native binaries directory path.

    Checks SLOP_HOME/bin/ first, falls back to package-relative bin/.

    Returns:
        Path to bin directory if it exists, None otherwise.
    """
    # Check SLOP_HOME first
    slop_home = get_slop_home()
    if slop_home:
        bin_path = slop_home / "bin"
        if bin_path.is_dir():
            return bin_path

    # Fall back to package-relative path
    pkg_root = _get_package_root()
    bin_path = pkg_root / "bin"
    if bin_path.is_dir():
        return bin_path

    return None


def find_native_binary(name: str) -> Optional[Path]:
    """Find a native SLOP component binary.

    Search order:
    1. SLOP_HOME/bin/slop-{name}
    2. Package-relative bin/slop-{name}
    3. Package-relative lib/compiler/{name}/slop-{name}
    4. Current working directory slop-{name}
    5. Current working directory build/slop-{name}

    Args:
        name: Component name (e.g., 'parser', 'transpiler', 'checker')

    Returns:
        Path to binary if found, None otherwise.
    """
    binary_name = f"slop-{name}"
    pkg_root = _get_package_root()

    # Build search locations in priority order
    locations = []

    # 1. SLOP_HOME/bin/ (highest priority)
    slop_home = get_slop_home()
    if slop_home:
        locations.append(slop_home / "bin" / binary_name)

    # 2. Package-relative bin/
    locations.append(pkg_root / "bin" / binary_name)

    # 3. Package-relative lib/compiler/{name}/ (native components built in-place)
    locations.append(pkg_root / "lib" / "compiler" / name / binary_name)

    # 4. Current working directory
    locations.append(Path.cwd() / binary_name)

    # 5. Current working directory build/
    locations.append(Path.cwd() / "build" / binary_name)

    for loc in locations:
        if loc.exists():
            return loc

    return None


def list_stdlib_modules() -> List[Path]:
    """List all standard library module files.

    Finds .slop files in the stdlib directory that are not in test directories.

    Returns:
        List of paths to stdlib module files, sorted by name.
    """
    stdlib_dir = get_stdlib_dir()
    if not stdlib_dir:
        return []

    modules = []
    for slop_file in stdlib_dir.rglob("*.slop"):
        # Skip test files
        if "tests" in slop_file.parts or "test" in slop_file.name:
            continue
        modules.append(slop_file)

    return sorted(modules, key=lambda p: p.name)


def get_stdlib_include_paths() -> List[Path]:
    """Get all standard library module directories as include paths.

    Returns directories that should be added to module search paths
    so that standard library modules can be imported by name.

    Returns:
        List of paths to stdlib module directories.
    """
    stdlib_dir = get_stdlib_dir()
    if not stdlib_dir:
        return []

    paths = []
    for subdir in stdlib_dir.iterdir():
        if subdir.is_dir() and not subdir.name.startswith('.'):
            paths.append(subdir)

    return sorted(paths, key=lambda p: p.name)


def list_examples() -> List[Path]:
    """List all example SLOP files.

    Returns:
        List of paths to example files, sorted by name.
    """
    examples_dir = get_examples_dir()
    if not examples_dir:
        return []

    return sorted(examples_dir.glob("*.slop"), key=lambda p: p.name)


def find_project_config(start_path: Path) -> Optional[Path]:
    """Search upward from start_path for a slop.toml file."""
    current = start_path.resolve()
    # Search up to 10 parent directories
    for _ in range(10):
        config_path = current / "slop.toml"
        if config_path.exists():
            return config_path
        parent = current.parent
        if parent == current:
            break
        current = parent
    return None


def get_resolved_paths() -> dict:
    """Get all resolved paths for diagnostic purposes.

    Returns:
        Dict containing resolved paths and SLOP_HOME status.
    """
    return {
        'slop_home': get_slop_home(),
        'slop_home_env': os.environ.get('SLOP_HOME'),
        'spec_dir': get_spec_dir(),
        'examples_dir': get_examples_dir(),
        'stdlib_dir': get_stdlib_dir(),
        'bin_dir': get_bin_dir(),
        'package_root': _get_package_root(),
    }
