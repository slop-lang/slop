#!/usr/bin/env python3
"""
Generate bootstrap C files using slop's module resolution.

This script uses slop's existing module resolution to determine the correct
build order, then calls the native transpiler and writes the C files to
the bootstrap directory.

Usage: python3 generate_c.py <tool_dir> <output_dir>
  tool_dir: Directory containing slop.toml (e.g., lib/compiler/parser)
  output_dir: Where to write the C files (e.g., bootstrap/parser)
"""

import sys
import os
import json
import subprocess
from pathlib import Path

# Add the slop package to the path
script_dir = Path(__file__).parent
project_root = script_dir.parent
sys.path.insert(0, str(project_root / "src"))

from slop.parser import parse_file
from slop.resolver import ModuleResolver
from slop.providers import load_project_config
from slop import paths


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <tool_dir> <output_dir>")
        sys.exit(1)

    tool_dir = Path(sys.argv[1]).resolve()
    output_dir = Path(sys.argv[2]).resolve()

    # Change to tool directory for config loading
    original_cwd = os.getcwd()
    os.chdir(tool_dir)

    try:
        # Load project config
        project_cfg, build_cfg, _, _ = load_project_config(None)

        if not project_cfg or not project_cfg.entry:
            print(f"Error: No entry point in {tool_dir}/slop.toml")
            sys.exit(1)

        entry_file = Path(project_cfg.entry)

        # Get include paths from config
        include_paths = []
        if build_cfg and build_cfg.include:
            include_paths = [str(tool_dir / p) for p in build_cfg.include]

        # Add standard library paths
        stdlib_paths = paths.get_stdlib_include_paths()
        for stdlib_path in stdlib_paths:
            if str(stdlib_path) not in include_paths:
                include_paths.append(str(stdlib_path))

        # Parse entry file
        ast = parse_file(str(entry_file))

        # Resolve modules
        search_paths = [Path(p) for p in include_paths]
        resolver = ModuleResolver(search_paths)
        graph = resolver.build_dependency_graph(entry_file)
        order = resolver.topological_sort(graph)

        print(f"  Build order: {', '.join(order)}")

        # Get source files in order
        source_files = [str(graph.modules[name].path) for name in order]

        # Find native compiler
        compiler_bin = project_root / "bin" / "slop-compiler"
        if not compiler_bin.exists():
            print(f"Error: Native compiler not found at {compiler_bin}")
            sys.exit(1)

        # Call native compiler
        cmd = [str(compiler_bin), "transpile"] + source_files
        result = subprocess.run(cmd, capture_output=True, text=True)

        if result.returncode != 0:
            print(f"Transpiler failed:\n{result.stderr}")
            sys.exit(1)

        # Parse JSON output
        try:
            modules = json.loads(result.stdout)
        except json.JSONDecodeError as e:
            print(f"Failed to parse transpiler output: {e}")
            print(f"Output: {result.stdout[:500]}...")
            sys.exit(1)

        # Create output directory
        output_dir.mkdir(parents=True, exist_ok=True)

        # Clear existing files
        for f in output_dir.glob("slop_*.h"):
            f.unlink()
        for f in output_dir.glob("slop_*.c"):
            f.unlink()

        # Write C files
        for mod_name, content in modules.items():
            c_name = mod_name.replace("-", "_").replace("/", "_")
            header_path = output_dir / f"slop_{c_name}.h"
            impl_path = output_dir / f"slop_{c_name}.c"

            header = content.get("header", "")
            impl = content.get("impl", "")

            # Fix runtime include path
            header = header.replace('#include "slop_runtime.h"', '#include "../runtime/slop_runtime.h"')

            # Write header
            with open(header_path, 'w') as f:
                f.write(header)

            # Write implementation with includes
            with open(impl_path, 'w') as f:
                f.write('#include "../runtime/slop_runtime.h"\n')
                f.write(f'#include "slop_{c_name}.h"\n\n')
                f.write(impl)

        print(f"  Generated {len(modules)} modules in {output_dir}")

    finally:
        os.chdir(original_cwd)


if __name__ == "__main__":
    main()
