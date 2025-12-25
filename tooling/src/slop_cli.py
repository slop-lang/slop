#!/usr/bin/env python3
"""
SLOP CLI - Command-line interface for SLOP toolchain

Commands:
  parse      Parse and validate SLOP files
  transpile  Convert SLOP to C
  fill       Fill holes with LLM generation
  check      Validate types and contracts
  build      Full pipeline: fill → transpile → compile
"""

import argparse
import sys
import os
from pathlib import Path

from parser import parse, parse_file, pretty_print, find_holes, is_form
from transpiler import Transpiler, transpile
from hole_filler import HoleFiller, extract_hole, classify_tier
from providers import (
    MockProvider, create_default_configs, load_config, create_from_config
)


def cmd_parse(args):
    """Parse and display SLOP file"""
    try:
        ast = parse_file(args.input)
        
        if args.holes:
            total = 0
            for form in ast:
                holes = find_holes(form)
                for h in holes:
                    info = extract_hole(h)
                    tier = classify_tier(info)
                    total += 1
                    print(f"Hole: {info.prompt}")
                    print(f"  Type: {info.type_expr}")
                    print(f"  Tier: {tier.name}")
                    if info.must_use:
                        print(f"  Must use: {', '.join(info.must_use)}")
                    print()
            print(f"Found {total} holes", file=sys.stderr)
        else:
            for form in ast:
                print(pretty_print(form))
                print()
        
        return 0
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


def cmd_transpile(args):
    """Transpile SLOP to C"""
    try:
        with open(args.input) as f:
            source = f.read()
        
        c_code = transpile(source)
        
        if args.output:
            with open(args.output, 'w') as f:
                f.write(c_code)
            print(f"Wrote {args.output}")
        else:
            print(c_code)
        
        return 0
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


def cmd_fill(args):
    """Fill holes with LLM"""
    try:
        ast = parse_file(args.input)

        # Count holes
        total_holes = sum(len(find_holes(form)) for form in ast)
        if total_holes == 0:
            print("No holes to fill")
            if args.output:
                with open(args.input) as f:
                    Path(args.output).write_text(f.read())
            return 0

        print(f"Found {total_holes} holes")

        # Create filler from config or use mock
        if args.config:
            try:
                config = load_config(args.config)
                configs, provider = create_from_config(config)
                print(f"Loaded config from {args.config}")
            except Exception as e:
                print(f"Error loading config: {e}", file=sys.stderr)
                return 1
        else:
            configs = create_default_configs()
            provider = MockProvider()
            print("Note: No --config specified. Using mock provider.")
            print("      Create slop.toml from slop.toml.example for real LLM generation.")

        filler = HoleFiller(configs, provider)
        print("Filling holes...")
        
        # For now, just report what would be filled
        for form in ast:
            holes = find_holes(form)
            for h in holes:
                info = extract_hole(h)
                tier = classify_tier(info)
                result = filler.fill(info, {})
                status = "✓" if result.success else "✗"
                print(f"  {status} {info.prompt[:50]}... ({tier.name})")
        
        return 0
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        return 1


def cmd_check(args):
    """Validate SLOP file"""
    try:
        ast = parse_file(args.input)
        
        errors = []
        warnings = []
        
        for form in ast:
            # Check for unfilled holes
            holes = find_holes(form)
            for h in holes:
                info = extract_hole(h)
                errors.append(f"Unfilled hole: {info.prompt}")
            
            # Check function annotations
            if is_form(form, 'fn') or is_form(form, 'impl'):
                has_intent = any(is_form(item, '@intent') for item in form.items)
                has_spec = any(is_form(item, '@spec') for item in form.items)
                
                fn_name = form[1].name if len(form) > 1 else "unknown"
                
                if not has_intent:
                    warnings.append(f"Function '{fn_name}' missing @intent")
                if not has_spec:
                    warnings.append(f"Function '{fn_name}' missing @spec")
        
        for w in warnings:
            print(f"Warning: {w}")
        for e in errors:
            print(f"Error: {e}")
        
        if errors:
            print(f"\n{len(errors)} errors")
            return 1
        
        print("✓ All checks passed")
        return 0
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


def cmd_build(args):
    """Full build pipeline"""
    try:
        input_path = Path(args.input)
        output = args.output or input_path.stem
        
        print(f"Building {input_path} -> {output}")
        
        # Parse
        print("  Parsing...")
        ast = parse_file(args.input)
        
        # Check for holes
        total_holes = sum(len(find_holes(form)) for form in ast)
        if total_holes > 0:
            print(f"  Warning: {total_holes} unfilled holes")
        
        # Transpile
        print("  Transpiling to C...")
        with open(args.input) as f:
            source = f.read()
        c_code = transpile(source)
        
        c_file = f"{output}.c"
        with open(c_file, 'w') as f:
            f.write(c_code)
        
        # Compile
        print("  Compiling...")
        import subprocess
        
        runtime_path = Path(__file__).parent.parent.parent / "runtime"
        
        compile_cmd = [
            "cc",
            "-O2",
            "-I", str(runtime_path),
            "-o", output,
            c_file,
        ]
        
        if args.debug:
            compile_cmd.insert(1, "-g")
            compile_cmd.insert(2, "-DSLOP_DEBUG")
        
        result = subprocess.run(compile_cmd, capture_output=True, text=True)
        
        if result.returncode != 0:
            print(f"Compilation failed:\n{result.stderr}")
            return 1
        
        print(f"✓ Built {output}")
        return 0
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


def main():
    parser = argparse.ArgumentParser(
        description='SLOP - Symbolic LLM-Optimized Programming',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('-v', '--verbose', action='store_true')
    
    subparsers = parser.add_subparsers(dest='command')
    
    # parse
    p = subparsers.add_parser('parse', help='Parse SLOP file')
    p.add_argument('input')
    p.add_argument('--holes', action='store_true', help='Show only holes')
    
    # transpile
    p = subparsers.add_parser('transpile', help='Convert to C')
    p.add_argument('input')
    p.add_argument('-o', '--output')
    
    # fill
    p = subparsers.add_parser('fill', help='Fill holes with LLM')
    p.add_argument('input')
    p.add_argument('-o', '--output')
    p.add_argument('-c', '--config', help='Path to TOML config file')
    p.add_argument('-v', '--verbose', action='store_true')
    
    # check
    p = subparsers.add_parser('check', help='Validate')
    p.add_argument('input')
    
    # build
    p = subparsers.add_parser('build', help='Full pipeline')
    p.add_argument('input')
    p.add_argument('-o', '--output')
    p.add_argument('-c', '--config', help='Path to TOML config file')
    p.add_argument('--debug', action='store_true')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        return 0
    
    commands = {
        'parse': cmd_parse,
        'transpile': cmd_transpile,
        'fill': cmd_fill,
        'check': cmd_check,
        'build': cmd_build,
    }
    
    return commands[args.command](args)


if __name__ == '__main__':
    sys.exit(main())
