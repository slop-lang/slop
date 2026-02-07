"""Generate clean FFI headers from SLOP library builds.

Parses generated per-module headers and .slop source files to produce a single
standalone header containing only public API types and function declarations.
"""

import re
from pathlib import Path


def generate_ffi_header(project_name, results, source_files):
    """Generate a clean FFI header from transpiled module headers and source files.

    Args:
        project_name: Project name (e.g. "growl")
        results: Dict of {module_name: (header_content, impl_content)} from transpiler
        source_files: List of .slop source file paths (strings)

    Returns:
        String containing the complete FFI header
    """
    # Step 1: Find public C names from :c-name annotations in source files
    public_names = _find_public_names(source_files)
    if not public_names:
        return ""

    # Step 2: Parse all headers to collect type definitions and function declarations
    all_headers = ""
    for mod_name, (header, _impl) in results.items():
        all_headers += header + "\n"

    typedefs = _parse_typedefs(all_headers)
    structs = _parse_structs(all_headers)
    enums = _parse_enums(all_headers)
    list_defines = _parse_container_macros(all_headers, "SLOP_LIST_DEFINE")
    option_defines = _parse_container_macros(all_headers, "SLOP_OPTION_DEFINE")
    func_decls = _parse_function_decls(all_headers)
    define_aliases = _parse_define_aliases(all_headers)

    # Step 3: Identify public function declarations
    # Build reverse alias map: clean_name -> mangled_name
    alias_to_mangled = {}
    for mangled, clean in define_aliases.items():
        alias_to_mangled[clean] = mangled

    public_decls = []
    for name in sorted(public_names):
        if name in func_decls:
            public_decls.append((name, func_decls[name]))
        elif name in alias_to_mangled:
            mangled = alias_to_mangled[name]
            if mangled in func_decls:
                public_decls.append((name, func_decls[mangled]))

    if not public_decls:
        return ""

    # Step 4: Collect all type defs into unified registry
    all_type_defs = {}  # name -> (kind, content)
    for name, content in typedefs.items():
        all_type_defs[name] = ("typedef", content)
    for name, content in structs.items():
        all_type_defs[name] = ("struct", content)
    for name, content in enums.items():
        all_type_defs[name] = ("enum", content)
    for elem_type, container_name in list_defines.items():
        all_type_defs[container_name] = ("list", (elem_type, container_name))
    for elem_type, container_name in option_defines.items():
        all_type_defs[container_name] = ("option", (elem_type, container_name))

    # Step 5: Trace type dependencies from public function signatures
    needed_types = set()
    for _name, decl in public_decls:
        _trace_types(decl, all_type_defs, needed_types, structs, enums, typedefs)

    # Step 6: Topologically sort type definitions
    sorted_types = _topo_sort(needed_types, all_type_defs, structs, enums, typedefs)

    # Step 7: Emit header
    guard = f"{project_name.upper()}_H"
    lines = []
    lines.append(f"/* {project_name}.h - Auto-generated FFI header. Do not edit. */")
    lines.append(f"#ifndef {guard}")
    lines.append(f"#define {guard}")
    lines.append("")
    lines.append("#include <stdint.h>")
    lines.append("#include <stdbool.h>")
    lines.append("#include <stddef.h>")
    lines.append("")
    lines.append("#ifdef __cplusplus")
    lines.append('extern "C" {')
    lines.append("#endif")
    lines.append("")
    lines.append("/* Opaque runtime types */")
    lines.append("typedef struct slop_arena slop_arena;")
    lines.append("typedef struct slop_map slop_map;")
    lines.append("")
    lines.append("/* Runtime value types */")
    lines.append("typedef struct { size_t len; const char* data; } slop_string;")
    lines.append("typedef struct { bool has_value; slop_string value; } slop_option_string;")
    lines.append("typedef struct { void* fn; void* env; } slop_closure_t;")
    lines.append("")

    # Emit type definitions in dependency order
    if sorted_types:
        lines.append("/* Type definitions */")
        for type_name in sorted_types:
            if type_name not in all_type_defs:
                continue
            kind, content = all_type_defs[type_name]
            if kind == "typedef":
                lines.append(content)
            elif kind == "enum":
                lines.append(content)
            elif kind == "struct":
                lines.append(content)
            elif kind == "list":
                elem_type, container_name = content
                lines.append(f"typedef struct {{ size_t len; size_t cap; {elem_type}* data; }} {container_name};")
            elif kind == "option":
                elem_type, container_name = content
                lines.append(f"typedef struct {{ bool has_value; {elem_type} value; }} {container_name};")
            lines.append("")

    # Emit public function declarations
    lines.append("/* Public API */")
    for name, decl in public_decls:
        lines.append(decl)
    lines.append("")

    # Emit #define aliases: module-prefixed name -> actual c-name symbol
    # Original headers have: #define index_indexed_graph_create rdf_indexed_graph_create
    # (module_name maps to c_name). Preserve that direction for FFI consumers.
    public_name_set = {name for name, _ in public_decls}
    aliases_out = []
    for mangled, clean in sorted(define_aliases.items()):
        if clean in public_name_set:
            aliases_out.append((mangled, clean))
    if aliases_out:
        for mangled, clean in aliases_out:
            lines.append(f"#define {mangled} {clean}")
        lines.append("")

    lines.append("#ifdef __cplusplus")
    lines.append("}")
    lines.append("#endif")
    lines.append("")
    lines.append(f"#endif /* {guard} */")
    lines.append("")

    return "\n".join(lines)


def _find_public_names(source_files):
    """Extract :c-name values from .slop source files."""
    names = set()
    pattern = re.compile(r':c-name\s+"([^"]+)"')
    for path in source_files:
        try:
            text = Path(path).read_text()
        except (OSError, IOError):
            continue
        for m in pattern.finditer(text):
            name = m.group(1)
            if name != "main":
                names.add(name)
    return names


def _parse_typedefs(header):
    """Parse simple typedef aliases (not struct/enum typedefs)."""
    result = {}
    for line in header.split("\n"):
        line = line.strip()
        if not line.startswith("typedef "):
            continue
        if line.startswith("typedef struct {") or line.startswith("typedef enum {"):
            continue
        # Skip "typedef struct X X;" forward decl/redecl
        if re.match(r"typedef\s+struct\s+(\w+)\s+\1\s*;", line):
            continue
        m = re.match(r"typedef\s+(.+?)\s+(\w+)\s*;", line)
        if m:
            name = m.group(2)
            if name in ("slop_string", "slop_option_string", "slop_closure_t"):
                continue
            result[name] = line
    return result


def _parse_structs(header):
    """Parse struct definitions: struct X { ... }; typedef struct X X;"""
    result = {}
    # Handle structs with nested union/struct blocks
    pattern = re.compile(
        r"(struct\s+(\w+)\s*\{(?:[^{}]*(?:\{[^{}]*\}[^{}]*)*)\})\s*;"
        r"\s*\n\s*typedef\s+struct\s+\2\s+\2\s*;",
        re.DOTALL,
    )
    for m in pattern.finditer(header):
        name = m.group(2)
        if name.startswith("slop_chan_"):
            continue
        result[name] = m.group(0)
    return result


def _parse_enums(header):
    """Parse typedef enum { ... } name;"""
    result = {}
    pattern = re.compile(r"(typedef\s+enum\s*\{[^}]*\}\s*(\w+)\s*;)", re.DOTALL)
    for m in pattern.finditer(header):
        result[m.group(2)] = m.group(1)
    return result


def _parse_container_macros(header, macro_name):
    """Parse SLOP_LIST_DEFINE(ElemType, Name) or SLOP_OPTION_DEFINE(ElemType, Name)."""
    result = {}
    seen_containers = set()
    pattern = re.compile(rf"{re.escape(macro_name)}\((\w+),\s*(\w+)\)")
    for m in pattern.finditer(header):
        elem_type = m.group(1)
        container_name = m.group(2)
        if container_name == "slop_option_string":
            continue
        if container_name not in seen_containers:
            result[elem_type] = container_name
            seen_containers.add(container_name)
    return result


def _parse_function_decls(header):
    """Parse non-static function declarations."""
    result = {}
    for line in header.split("\n"):
        line = line.strip()
        if line.startswith("static ") or line.startswith("#") or line.startswith("typedef "):
            continue
        if line.startswith("struct ") or line.startswith("enum "):
            continue
        m = re.match(r"([\w][\w\s*]+?)\s+(\w+)\s*\(([^)]*)\)\s*;", line)
        if m:
            result[m.group(2)] = line
    return result


def _parse_define_aliases(header):
    """Parse #define mangled clean function name aliases."""
    result = {}
    pattern = re.compile(r"^#define\s+(\w+)\s+(\w+)\s*$", re.MULTILINE)
    for m in pattern.finditer(header):
        mangled = m.group(1)
        clean = m.group(2)
        # Only function aliases (skip include guards etc.)
        if "_" in mangled and "_" in clean and not mangled.startswith("SLOP_"):
            result[mangled] = clean
    return result


# Types provided in the header preamble — don't collect from parsed headers
_BUILTIN_TYPES = {
    "void", "int", "char", "bool", "size_t",
    "int8_t", "int16_t", "int32_t", "int64_t",
    "uint8_t", "uint16_t", "uint32_t", "uint64_t",
    "slop_arena", "slop_map", "slop_string", "slop_option_string", "slop_closure_t",
}

_TYPE_RE = re.compile(r"\b([a-zA-Z_]\w+)\b")

# Words that appear in declarations but are not type references
_NON_TYPE_WORDS = {
    "struct", "union", "enum", "typedef", "const", "static", "inline",
    "return", "if", "else", "switch", "case", "for", "while", "do",
    "break", "continue", "sizeof", "true", "false", "NULL",
    "SLOP_PRE",
    # Common parameter/field names
    "key", "data", "tag", "has_value", "value", "len", "cap",
    "arena", "subject", "predicate", "object", "fn", "env",
    "a", "b", "g", "t", "d", "v", "config", "input", "individual", "result",
    "id", "triples", "seen", "by_predicate", "iteration",
    "worker_count", "channel_buffer", "max_iterations",
    "graph", "delta", "index", "size", "spo", "pso", "osp",
    "inferred_count", "iterations", "reason", "witnesses",
    "reason_success", "reason_inconsistent",
    "term_iri", "term_blank", "term_literal",
    "datatype", "lang",
    "subj", "pred", "obj", "callback",
    "msg_delta", "msg_inconsistent", "msg_done",
}


def _extract_type_refs(text):
    """Extract potential type name references from C text."""
    refs = set()
    for m in _TYPE_RE.finditer(text):
        word = m.group(1)
        if word in _BUILTIN_TYPES or word in _NON_TYPE_WORDS:
            continue
        if word.startswith("slop_hash_") or word.startswith("slop_eq_"):
            continue
        refs.add(word)
    return refs


def _trace_types(text, all_type_defs, needed, structs, enums, typedefs):
    """Recursively collect type definitions referenced from text."""
    refs = _extract_type_refs(text)
    for ref in refs:
        if ref in needed:
            continue
        if ref not in all_type_defs:
            continue
        needed.add(ref)
        kind, content = all_type_defs[ref]
        if kind == "struct" and ref in structs:
            _trace_types(structs[ref], all_type_defs, needed, structs, enums, typedefs)
        elif kind == "enum" and ref in enums:
            _trace_types(enums[ref], all_type_defs, needed, structs, enums, typedefs)
        elif kind == "typedef" and ref in typedefs:
            _trace_types(typedefs[ref], all_type_defs, needed, structs, enums, typedefs)
        elif kind == "list":
            elem_type, _ = content
            _trace_types(elem_type, all_type_defs, needed, structs, enums, typedefs)
        elif kind == "option":
            elem_type, _ = content
            _trace_types(elem_type, all_type_defs, needed, structs, enums, typedefs)


def _get_deps(type_name, all_type_defs, structs, enums, typedefs):
    """Get direct type dependencies for topological sorting."""
    if type_name not in all_type_defs:
        return set()
    kind, content = all_type_defs[type_name]
    if kind == "struct" and type_name in structs:
        text = structs[type_name]
    elif kind == "enum" and type_name in enums:
        text = enums[type_name]
    elif kind == "typedef" and type_name in typedefs:
        text = typedefs[type_name]
    elif kind in ("list", "option"):
        elem_type, _ = content
        return {elem_type} & set(all_type_defs.keys())
    else:
        return set()
    refs = _extract_type_refs(text)
    return {r for r in refs if r in all_type_defs and r != type_name}


def _topo_sort(needed_types, all_type_defs, structs, enums, typedefs):
    """Topologically sort types so dependencies come first."""
    if not needed_types:
        return []

    # Build in-degree map: if t depends on d, d must come before t
    in_degree = {t: 0 for t in needed_types}
    # edges[d] = set of types that depend on d (d must come first)
    dependents = {t: set() for t in needed_types}

    for t in needed_types:
        deps = _get_deps(t, all_type_defs, structs, enums, typedefs) & needed_types
        in_degree[t] = len(deps)
        for d in deps:
            dependents[d].add(t)

    # Kahn's algorithm
    queue = sorted([t for t in needed_types if in_degree[t] == 0])
    result = []
    while queue:
        node = queue.pop(0)
        result.append(node)
        for dep in sorted(dependents[node]):
            in_degree[dep] -= 1
            if in_degree[dep] == 0:
                queue.append(dep)
                queue.sort()

    # Append any remaining (cycles) in sorted order
    for t in sorted(needed_types):
        if t not in result:
            result.append(t)

    return result
