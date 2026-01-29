"""
Import resolution for verification.

Extracts definitions from imported modules so the verifier can use
function signatures, types, and constants from dependencies.
"""
from __future__ import annotations

from pathlib import Path
from typing import Dict, List, Optional, Any, TYPE_CHECKING

from slop.parser import SList, Symbol, Number, String, is_form
from slop.types import Type, UNKNOWN

from .types import FunctionSignature, ConstantDef, ImportedDefinitions
from .type_builder import build_type_registry_from_ast, _parse_type_expr_simple

if TYPE_CHECKING:
    from slop.parser import SExpr


def extract_module_definitions(ast: List['SExpr'], registry: Dict[str, Type]) -> ImportedDefinitions:
    """Extract all exportable definitions from a module AST.

    Args:
        ast: Parsed module AST
        registry: Type registry built from the module (for resolving type references)

    Returns:
        ImportedDefinitions with functions, types, and constants
    """
    defs = ImportedDefinitions()

    for form in ast:
        if is_form(form, 'module'):
            # Process forms inside module
            for item in form.items[1:]:
                _extract_definition(item, defs, registry)
        else:
            _extract_definition(form, defs, registry)

    return defs


def _extract_definition(form: 'SExpr', defs: ImportedDefinitions, registry: Dict[str, Type]):
    """Extract a single definition from a form."""
    if not isinstance(form, SList) or len(form) < 2:
        return

    # Functions: extract @spec for return type
    if is_form(form, 'fn') and len(form) > 2:
        name = form[1].name if isinstance(form[1], Symbol) else None
        if name:
            sig = _extract_function_signature(form, registry)
            if sig:
                defs.functions[name] = sig

    # Types: extract record fields, enum variants, range types
    elif is_form(form, 'type') and len(form) > 2:
        type_name = form[1].name if isinstance(form[1], Symbol) else None
        if type_name and type_name in registry:
            defs.types[type_name] = registry[type_name]

    # Constants: extract type and value
    elif is_form(form, 'const') and len(form) >= 4:
        name = form[1].name if isinstance(form[1], Symbol) else None
        if name:
            const_type = _parse_type_expr_simple(form[2], registry)
            value = _extract_const_value(form[3])
            defs.constants[name] = ConstantDef(name, const_type, value)


def _extract_function_signature(fn_form: SList, registry: Dict[str, Type]) -> Optional[FunctionSignature]:
    """Extract function signature from a fn form.

    Looks for @spec annotation to get return type with range information.
    Also extracts parameter names and @post annotations for cross-module
    postcondition propagation.
    """
    if len(fn_form) < 3:
        return None

    name = fn_form[1].name if isinstance(fn_form[1], Symbol) else None
    if not name:
        return None

    param_types: List[Type] = []
    param_names: List[str] = []
    return_type: Type = UNKNOWN

    # Extract param types and names from parameter list
    params_list = fn_form[2] if isinstance(fn_form[2], SList) else SList([])
    for param in params_list:
        if isinstance(param, SList) and len(param) >= 2:
            first = param[0]
            if isinstance(first, Symbol) and first.name in ('in', 'out', 'mut'):
                # Mode is explicit: (in name Type)
                param_name = param[1].name if isinstance(param[1], Symbol) else None
                type_expr = param[2] if len(param) > 2 else None
            else:
                # No mode: (name Type)
                param_name = first.name if isinstance(first, Symbol) else None
                type_expr = param[1]
            if param_name:
                param_names.append(param_name)
            if type_expr:
                param_types.append(_parse_type_expr_simple(type_expr, registry))

    # Look for @spec to get return type, @post for postconditions, @assume for assumptions
    postconditions: List['SExpr'] = []
    assumptions: List['SExpr'] = []
    for item in fn_form.items[3:]:
        if is_form(item, '@spec') and len(item) > 1:
            spec = item[1]
            if isinstance(spec, SList) and len(spec) >= 3:
                # (@spec ((ParamTypes) -> ReturnType))
                # Find the return type (after ->)
                for i, s in enumerate(spec.items):
                    if isinstance(s, Symbol) and s.name == '->':
                        if i + 1 < len(spec):
                            return_type = _parse_type_expr_simple(spec[i + 1], registry)
                        break
        elif is_form(item, '@post') and len(item) > 1:
            postconditions.append(item[1])
        elif is_form(item, '@assume') and len(item) > 1:
            assumptions.append(item[1])

    return FunctionSignature(name, param_types, return_type, param_names, postconditions, assumptions)


def _extract_const_value(expr: 'SExpr') -> Any:
    """Extract the value from a constant definition."""
    if isinstance(expr, Number):
        return expr.value
    elif isinstance(expr, String):
        return expr.value
    elif isinstance(expr, Symbol):
        # Could be a reference to another constant or a special value
        return expr.name
    return None


def resolve_imported_definitions(
    ast: List['SExpr'],
    file_path: Path,
    search_paths: Optional[List[Path]] = None
) -> ImportedDefinitions:
    """Resolve definitions from imported modules.

    For each import statement in the AST, finds the module file,
    parses it, and extracts definitions for imported symbols.

    Args:
        ast: The AST of the file being verified
        file_path: Path to the file being verified
        search_paths: Additional paths to search for modules

    Returns:
        ImportedDefinitions with functions, types, and constants from imports
    """
    from slop.parser import get_imports, parse_import

    result = ImportedDefinitions()

    # Collect all import statements
    imports = []
    for form in ast:
        if is_form(form, 'module'):
            for item in form.items[1:]:
                if is_form(item, 'import'):
                    imports.append(item)
        elif is_form(form, 'import'):
            imports.append(form)

    if not imports:
        return result

    # Set up module resolver
    from slop.resolver import ModuleResolver
    paths = list(search_paths) if search_paths else []
    resolver = ModuleResolver(paths)

    # Process each import
    for imp_form in imports:
        try:
            imp_spec = parse_import(imp_form)
            module_name = imp_spec.module_name
            imported_symbols = set(imp_spec.symbols)

            # Find and load the module
            module_path = resolver.resolve_module(module_name, file_path)
            module_info = resolver.load_module(module_path)

            # Build type registry for the module
            module_registry = build_type_registry_from_ast(module_info.ast)

            # Extract definitions
            module_defs = extract_module_definitions(module_info.ast, module_registry)

            # Only keep the symbols that are actually imported
            for fn_name in list(module_defs.functions.keys()):
                if fn_name in imported_symbols:
                    result.functions[fn_name] = module_defs.functions[fn_name]

            for type_name in list(module_defs.types.keys()):
                if type_name in imported_symbols:
                    result.types[type_name] = module_defs.types[type_name]

            for const_name in list(module_defs.constants.keys()):
                if const_name in imported_symbols:
                    result.constants[const_name] = module_defs.constants[const_name]

        except Exception:
            # Skip modules that can't be resolved - they may be external
            # The type checker will have already reported errors for missing modules
            pass

    return result


__all__ = [
    'extract_module_definitions',
    'resolve_imported_definitions',
]
