"""
SLOP Schema Converter - Deterministic type generation from schemas

Converts:
- JSON Schema → SLOP types
- SQL DDL → SLOP types
- OpenAPI → SLOP types + function signatures with holes

Every converter emits one `(module ...)` that exports what it defines, and the
output is meant to pass `slop check` as it stands (apart from the holes an
OpenAPI conversion leaves for the implementation).

A schema construct with no SLOP equivalent (a free-form object, a value with
no type, a mixed-type enum, an unknown SQL column type, ...) is never emitted as
an undefined type. It becomes `String` -- the value kept as its JSON or SQL
text -- with a `;;` comment at the field, and a warning is reported to the
caller (`slop derive` prints them on stderr).
"""

import json
import math
import re
import sys
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple


# Builtin type names a generated type must not shadow.
RESERVED_TYPE_NAMES = {
    'Int', 'I8', 'I16', 'I32', 'I64', 'U8', 'U16', 'U32', 'U64',
    'Float', 'F32', 'F64', 'Bool', 'String', 'Bytes', 'Char', 'Byte',
    'List', 'Array', 'Slice', 'Map', 'Set', 'Ptr', 'ScopedPtr', 'OptPtr',
    'Fn', 'Option', 'Result', 'Chan', 'Thread', 'Arena', 'Unit', 'Void',
    'Any', 'Mutex', 'Cond', 'Atomic',
}

# Names a generated enum variant or union tag must not take: the builtin
# variants and the literals.
RESERVED_VARIANTS = {'some', 'none', 'ok', 'error', 'true', 'false', 'nil', 'else'}

INT_TYPE_HEADS = {'Int', 'I8', 'I16', 'I32', 'I64', 'U8', 'U16', 'U32', 'U64'}
FLOAT_TYPE_HEADS = {'Float', 'F32', 'F64'}
CONTAINER_TYPE_HEADS = {'List', 'Map', 'Set', 'Array', 'Slice'}


# ---------------------------------------------------------------------------
# Naming and text helpers
# ---------------------------------------------------------------------------

def _split_words(s: str) -> List[str]:
    """Split an identifier-ish string into words on case and non-alnum breaks."""
    s = re.sub(r'([a-z0-9])([A-Z])', r'\1 \2', str(s))
    s = re.sub(r'([A-Z]+)([A-Z][a-z])', r'\1 \2', s)
    return [w for w in re.split(r'[^A-Za-z0-9]+', s) if w]


def to_kebab(s: str, prefix: str = 'x') -> str:
    """A valid SLOP kebab-case identifier for s.

    Non-alphanumerics become '-', camelCase is split, and a name that would
    start with a digit (or be empty) is prefixed with `prefix`.
    """
    out = '-'.join(w.lower() for w in _split_words(s))
    if not out:
        return prefix
    if out[0].isdigit():
        return f"{prefix}-{out}"
    return out


def to_pascal(s: str, prefix: str = 'T') -> str:
    """A valid SLOP PascalCase type name for s."""
    out = ''.join(w.capitalize() for w in _split_words(s))
    if not out:
        return prefix
    if out[0].isdigit():
        out = prefix + out
    return out


def _singular(word: str) -> str:
    if word.endswith('ies') and len(word) > 3:
        return word[:-3] + 'y'
    if word.endswith('sses'):
        return word[:-2]
    if word.endswith('s') and not word.endswith('ss') and len(word) > 1:
        return word[:-1]
    return word


def _one_line(text: Any) -> str:
    return ' '.join(str(text).split())


def slop_string(text: Any) -> str:
    """A SLOP string literal for text, escaped for the native parser."""
    out = []
    for ch in str(text):
        if ch == '\\':
            out.append('\\\\')
        elif ch == '"':
            out.append('\\"')
        elif ch == '\n':
            out.append('\\n')
        elif ch == '\t':
            out.append('\\t')
        elif ch == '\r':
            out.append('\\r')
        elif ord(ch) < 32 or ord(ch) == 127:
            out.append(' ')
        else:
            out.append(ch)
    return '"' + ''.join(out) + '"'


def _comment(text: Any) -> str:
    return ';; ' + _one_line(text)


def _option(t: str) -> str:
    return t if t.startswith('(Option ') else f"(Option {t})"


def _unique(name: str, used: set) -> str:
    candidate, i = name, 2
    while candidate in used:
        candidate = f"{name}-{i}"
        i += 1
    used.add(candidate)
    return candidate


def _number_literal(value: Any) -> str:
    if isinstance(value, float) and value.is_integer():
        return str(int(value))
    return str(value)


def _float_literal(value: Any) -> str:
    text = repr(float(value))
    if 'inf' in text or 'nan' in text:
        raise ValueError(text)
    if '.' not in text and 'e' not in text:
        text += '.0'
    return text


def parse_type(expr: str) -> Tuple[str, List[str]]:
    """Split a SLOP type expression into its head and top-level arguments."""
    expr = expr.strip()
    if not expr.startswith('('):
        return expr, []
    inner = expr[1:-1]
    parts, depth, cur = [], 0, ''
    for ch in inner:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if ch.isspace() and depth == 0:
            if cur:
                parts.append(cur)
            cur = ''
        else:
            cur += ch
    if cur:
        parts.append(cur)
    return (parts[0], parts[1:]) if parts else ('', [])


class _Namer:
    """Module-wide registry of type names and enum/union variant names.

    SLOP resolves a variant by name across the whole module, so two enums (or
    unions) in one output must never share one.
    """

    def __init__(self):
        self.types = set(RESERVED_TYPE_NAMES)
        self.variants = set(RESERVED_VARIANTS)

    def claim_type(self, base: str, suffix: str = 'Schema') -> str:
        if len(base) == 1:
            # A single uppercase letter reads as a generic type variable.
            base += 'Type'
        if base not in self.types:
            self.types.add(base)
            return base
        if base in RESERVED_TYPE_NAMES and base + suffix not in self.types:
            self.types.add(base + suffix)
            return base + suffix
        i = 2
        while f"{base}{i}" in self.types:
            i += 1
        self.types.add(f"{base}{i}")
        return f"{base}{i}"

    def claim_variants(self, names: List[str], prefix: str) -> List[str]:
        """Claim names (already unique among themselves) for one enum/union.

        A name another type already has (or a reserved one such as `none`)
        is prefixed with this type's kebab name.
        """
        result = []
        taken = set(self.variants) | set(names)
        for n in names:
            if n in self.variants:
                base = n if n.startswith(prefix + '-') else f"{prefix}-{n}"
                n = _unique(base, taken)
            result.append(n)
        self.variants.update(result)
        return result


def _render_module(name: str, header: List[str], annotations: List[str],
                   forms: List[str], exports: List[str]) -> str:
    lines = list(header)
    lines.append(f"(module {name}")
    if exports:
        export_lines, cur = [], "(export"
        for e in exports:
            if len(cur) + len(e) + 1 > 76:
                export_lines.append(cur)
                cur = "  "
                cur += e
            else:
                cur += ' ' + e
        export_lines.append(cur + ")")
        for line in export_lines:
            lines.append('  ' + line)
    for a in annotations:
        lines.append('  ' + a)
    for form in forms:
        lines.append('')
        for line in form.split('\n'):
            lines.append(('  ' + line) if line.strip() else '')
    lines.append(')')
    return '\n'.join(lines) + '\n'


def _module_name(name: Optional[str], title: str) -> str:
    """The module name: one given (a file stem) as-is when it is a valid
    identifier, else the kebab-case of it or of the schema's title."""
    if name and re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', name):
        return name
    return to_kebab(name or title, 'derived')


@dataclass
class SlopType:
    """Represents a SLOP type definition"""
    name: str
    definition: str
    comment: Optional[str] = None

    def to_slop(self) -> str:
        lines = []
        if self.comment:
            for line in str(self.comment).split('\n'):
                lines.append(_comment(line))
        lines.append(f"(type {self.name} {self.definition})")
        return '\n'.join(lines)


@dataclass
class SlopFunction:
    """Represents a SLOP function definition with hole"""
    name: str
    params: List[tuple]  # [(param_name, type_str), ...]
    return_type: str
    intent: str
    hole_prompt: str
    hole_tier: str
    context: Optional[List[str]] = None         # Whitelist of available identifiers
    preconditions: Optional[List[str]] = None   # @pre expressions
    postconditions: Optional[List[str]] = None  # @post expressions
    # [(args, result), ...]: args is the list of rendered argument
    # expressions, one per parameter in order; result is the expected value.
    examples: Optional[List[tuple]] = None

    def to_slop(self) -> str:
        lines = []

        # Function signature
        param_str = ' '.join(f"({p[0]} {p[1]})" for p in self.params)
        lines.append(f"(fn {self.name} ({param_str})")

        lines.append(f"  (@intent {slop_string(_one_line(self.intent))})")

        param_types = ' '.join(p[1] for p in self.params)
        lines.append(f"  (@spec (({param_types}) -> {self.return_type}))")

        for pre in self.preconditions or []:
            lines.append(f"  (@pre {pre})")

        for post in self.postconditions or []:
            lines.append(f"  (@post {post})")

        # (@example (args...) -> result): the argument list is always
        # parenthesized, even for a single argument.
        for (args, output) in self.examples or []:
            if isinstance(args, str):
                args = [args]
            lines.append(f"  (@example ({' '.join(args)}) -> {output})")

        context_str = ""
        if self.context:
            context_str = f"\n    :context ({' '.join(self.context)})"

        lines.append(f"  (hole {self.return_type} {slop_string(_one_line(self.hole_prompt))}")
        lines.append(f"    :complexity {self.hole_tier}{context_str}))")

        return '\n'.join(lines)


# ---------------------------------------------------------------------------
# JSON Schema
# ---------------------------------------------------------------------------

def _is_null_schema(s: Any) -> bool:
    return isinstance(s, dict) and (s.get('type') == 'null' or s.get('const', 0) is None
                                    or s.get('enum') == [None])


class JsonSchemaConverter:
    """Convert JSON Schema to SLOP types

    Mapping:
    - object with properties    → (record ...), properties not in `required` → (Option T)
    - object with only additionalProperties → (Map String T)
    - array                     → (List T) with minItems/maxItems as a range
    - string                    → String, (String min .. max); a format such as
                                  date-time stays String with a `;; format:` comment;
                                  uuid → (String 36 .. 36)
    - integer / number          → (Int min .. max) / (Float min .. max)
    - string enum / const       → (enum ...), variants sanitized and unique module-wide
    - oneOf / anyOf             → (union (tag T) ...), tags named from the $ref target
                                  or `<type>-<i>`; a null alternative makes it (Option T)
    - allOf of objects          → one record with the merged properties
    - ["T", "null"], nullable   → (Option T)
    - anything else             → String plus a comment and a warning
    """

    def __init__(self, namer: Optional[_Namer] = None):
        self.namer = namer or _Namer()
        self._reset()

    def _reset(self):
        self.types: List[SlopType] = []
        self.type_names: Dict[str, str] = {}
        self.warnings: List[str] = []
        self.ref_types: Dict[str, str] = {}      # schema name → SLOP type name
        self.ref_schemas: Dict[str, Any] = {}    # schema name → schema
        # record type → [(json property, field name, type expr)]
        self.records: Dict[str, List[Tuple[str, str, str]]] = {}
        self.enum_values: Dict[str, Dict[Any, str]] = {}  # enum type → {json value: variant}
        self.aliases: Dict[str, str] = {}         # alias type → aliased type expr
        self.unions: set = set()
        self._enum_by_values: Dict[tuple, str] = {}
        self._defined: set = set()

    # -- entry points -------------------------------------------------------

    def convert(self, schema: dict, root_name: str = "Root",
                module_name: Optional[str] = None) -> str:
        """Convert JSON Schema to a SLOP module of type definitions"""
        self.namer = _Namer()
        self._reset()

        named = {}
        for key in ('definitions', '$defs'):
            if isinstance(schema.get(key), dict):
                named.update(schema[key])
        self.add_named_schemas(named)

        root_keys = ('type', 'properties', 'items', 'enum', 'const', 'oneOf',
                     'anyOf', 'allOf', '$ref', 'additionalProperties')
        root_type = None
        if any(k in schema for k in root_keys):
            root_type = self.namer.claim_type(to_pascal(root_name, 'Root'))
        self.convert_named_schemas()
        if root_type:
            root_schema = {k: v for k, v in schema.items()
                           if k not in ('definitions', '$defs')}
            self._convert_named(root_type, root_schema)

        exports = [t.name for t in self.types]
        return _render_module(
            _module_name(module_name, root_name),
            [";; Generated by slop derive from JSON Schema"],
            ['(@derived-from "jsonschema")', "(@generation-mode deterministic)"],
            [t.to_slop() for t in self.types],
            exports)

    def add_named_schemas(self, schemas: Dict[str, Any]):
        """Register named schemas (definitions, components) so $refs resolve."""
        for name, schema in schemas.items():
            if name in self.ref_types:
                continue
            self.ref_types[name] = self.namer.claim_type(to_pascal(name))
            self.ref_schemas[name] = schema

    def convert_named_schemas(self):
        # String enums first, so an inline enum with the same values reuses the
        # named one instead of defining a second enum with the same variants.
        items = list(self.ref_schemas.items())
        enums = [(n, s) for n, s in items if isinstance(s, dict) and 'enum' in s]
        rest = [(n, s) for n, s in items if not (isinstance(s, dict) and 'enum' in s)]
        for name, schema in enums + rest:
            self._convert_named(self.ref_types[name], schema)

    def convert_inline(self, schema: Any, name_hint: str) -> str:
        """Type expression for a schema met outside the named schemas."""
        return self._convert_schema(schema, name_hint, [])

    def is_record(self, type_expr: str) -> bool:
        return self.resolve_alias(type_expr) in self.records

    def resolve_alias(self, type_expr: str) -> str:
        seen = set()
        while type_expr in self.aliases and type_expr not in seen:
            seen.add(type_expr)
            type_expr = self.aliases[type_expr]
        return type_expr

    # -- internals ----------------------------------------------------------

    def _define(self, name: str, definition: str, comment: Optional[str] = None):
        self.types.append(SlopType(name, definition, comment))
        self.type_names[name] = name
        self._defined.add(name)

    def _take_name(self, hint: str, top: bool) -> str:
        return hint if top else self.namer.claim_type(hint)

    def _convert_named(self, tname: str, schema: Any):
        if tname in self._defined:
            return
        notes: List[str] = []
        expr = self._convert_schema(schema, tname, notes, top=True)
        if expr == _option(tname):
            expr = tname  # a nullable named schema: nullability applies at its uses
        if expr != tname and tname not in self._defined:
            self._define(tname, expr, '\n'.join(notes) if notes else None)
            self.aliases[tname] = expr

    def _warn(self, where: str, reason: str, notes: List[str]) -> str:
        self.warnings.append(f"{where}: {reason}; using String")
        notes.append(f"{reason}: kept as String (JSON text)")
        return "String"

    def _resolve_ref(self, ref: str, where: str, notes: List[str]) -> str:
        if not ref.startswith('#'):
            return self._warn(where, f"external $ref {ref} is not supported", notes)
        key = ref.split('/')[-1].replace('~1', '/').replace('~0', '~')
        if key not in self.ref_types:
            return self._warn(where, f"unresolved $ref {ref}", notes)
        return self.ref_types[key]

    def _deref(self, schema: Any) -> Any:
        seen = 0
        while isinstance(schema, dict) and '$ref' in schema and seen < 32:
            key = schema['$ref'].split('/')[-1].replace('~1', '/').replace('~0', '~')
            if key not in self.ref_schemas:
                return None
            schema = self.ref_schemas[key]
            seen += 1
        return schema

    def _convert_schema(self, schema: Any, name: str, notes: List[str],
                        top: bool = False) -> str:
        """Convert a schema node, returning a type expression"""
        if not isinstance(schema, dict) or not schema:
            return self._warn(name, "schema accepts any value", notes)

        if '$ref' in schema:
            return self._resolve_ref(schema['$ref'], name, notes)

        if schema.get('nullable') is True:
            inner = {k: v for k, v in schema.items() if k != 'nullable'}
            return _option(self._convert_schema(inner, name, notes, top))

        if 'const' in schema:
            return self._convert_const(schema, name, notes, top)
        if 'enum' in schema:
            return self._convert_enum(schema, name, notes, top)
        if 'oneOf' in schema or 'anyOf' in schema:
            return self._convert_union(schema, name, notes, top)
        if 'allOf' in schema:
            return self._convert_all_of(schema, name, notes, top)

        schema_type = schema.get('type')
        if isinstance(schema_type, list):
            non_null = [t for t in schema_type if t != 'null']
            nullable = len(non_null) < len(schema_type)
            if not non_null:
                return self._warn(name, "type null has no SLOP equivalent", notes)
            if len(non_null) == 1:
                inner = self._convert_schema({**schema, 'type': non_null[0]}, name, notes, top)
            else:
                variants = [{**schema, 'type': t} for t in non_null]
                inner = self._convert_union({'oneOf': variants}, name, notes, top)
            return _option(inner) if nullable else inner

        if schema_type is None:
            if 'properties' in schema or 'additionalProperties' in schema:
                schema_type = 'object'
            elif 'items' in schema:
                schema_type = 'array'
            else:
                return self._warn(name, "schema has no type", notes)

        if schema_type == "object":
            return self._convert_object(schema, name, notes, top)
        elif schema_type == "array":
            return self._convert_array(schema, name, notes)
        elif schema_type == "string":
            return self._convert_string(schema, notes)
        elif schema_type == "integer":
            return self._convert_integer(schema)
        elif schema_type == "number":
            return self._convert_number(schema, notes)
        elif schema_type == "boolean":
            return "Bool"
        elif schema_type == "null":
            return self._warn(name, "type null has no SLOP equivalent", notes)
        return self._warn(name, f"unknown type {schema_type!r}", notes)

    def _convert_object(self, schema: dict, name: str, notes: List[str],
                        top: bool = False) -> str:
        """Convert object schema to record type"""
        properties = schema.get("properties") or {}

        if not properties:
            extra = schema.get('additionalProperties')
            if isinstance(extra, dict) and extra:
                value = self._convert_schema(extra, f"{name}Value", notes)
                return f"(Map String {value})"
            return self._warn(name, "free-form object", notes)

        tname = self._take_name(name, top)
        required = set(schema.get("required") or [])
        used: set = set()
        fields: List[Tuple[str, str, str]] = []
        lines: List[str] = []
        for prop_name, prop_schema in properties.items():
            field_notes: List[str] = []
            field_type = self._convert_schema(
                prop_schema, f"{tname}{to_pascal(prop_name)}", field_notes)
            # A record cannot hold itself by value.
            if field_type in (tname, _option(tname)):
                field_type = f"(Option (Ptr {tname}))"
            if prop_name not in required:
                field_type = _option(field_type)
            field_name = _unique(to_kebab(prop_name, 'field'), used)
            if field_name != to_kebab(prop_name, 'field') or not re.fullmatch(
                    r'[A-Za-z][A-Za-z0-9_-]*', str(prop_name)):
                field_notes.insert(0, f"JSON property {json.dumps(prop_name)}")
            fields.append((prop_name, field_name, field_type))
            for n in field_notes:
                lines.append(_comment(n))
            lines.append(f"({field_name} {field_type})")

        self._define(tname, "(record\n    " + "\n    ".join(lines) + ")")
        self.records[tname] = fields
        return tname

    def _convert_array(self, schema: dict, name: str, notes: List[str]) -> str:
        """Convert array schema to List type"""
        items = schema.get("items")
        if isinstance(items, list):
            return self._warn(name, "tuple-typed array (items is a list)", notes)
        item_type = self._convert_schema(items or {}, f"{name}Item", notes)

        min_items = schema.get("minItems")
        max_items = schema.get("maxItems")
        if min_items is not None and max_items is not None:
            return f"(List {item_type} {min_items} .. {max_items})"
        elif min_items is not None:
            return f"(List {item_type} {min_items} ..)"
        elif max_items is not None:
            return f"(List {item_type} 0 .. {max_items})"
        return f"(List {item_type})"

    def _convert_string(self, schema: dict, notes: List[str]) -> str:
        """Convert string schema with constraints"""
        min_len = schema.get("minLength")
        max_len = schema.get("maxLength")
        format_ = schema.get("format")
        pattern = schema.get("pattern")

        if format_:
            notes.append(f"format: {format_}")
        if pattern:
            notes.append(f"pattern: {pattern}")
        if format_ == "uuid":
            return "(String 36 .. 36)"

        if min_len is not None and max_len is not None:
            return f"(String {min_len} .. {max_len})"
        elif min_len is not None:
            return f"(String {min_len} ..)"
        elif max_len is not None:
            return f"(String .. {max_len})"
        return "String"

    def _convert_integer(self, schema: dict) -> str:
        """Convert integer schema with constraints"""
        minimum = schema.get("minimum")
        maximum = schema.get("maximum")
        exclusive_min = schema.get("exclusiveMinimum")
        exclusive_max = schema.get("exclusiveMaximum")

        # Draft 4 spells exclusivity as a boolean beside minimum/maximum;
        # later drafts give the exclusive bound itself.
        if exclusive_min is True and minimum is not None:
            minimum = math.floor(minimum) + 1
        elif isinstance(exclusive_min, (int, float)) and not isinstance(exclusive_min, bool):
            minimum = math.floor(exclusive_min) + 1
        if exclusive_max is True and maximum is not None:
            maximum = math.ceil(maximum) - 1
        elif isinstance(exclusive_max, (int, float)) and not isinstance(exclusive_max, bool):
            maximum = math.ceil(exclusive_max) - 1
        if minimum is not None:
            minimum = math.ceil(minimum)
        if maximum is not None:
            maximum = math.floor(maximum)

        if minimum is not None and maximum is not None:
            return f"(Int {minimum} .. {maximum})"
        elif minimum is not None:
            return f"(Int {minimum} ..)"
        elif maximum is not None:
            return f"(Int .. {maximum})"
        return "Int"

    def _convert_number(self, schema: dict, notes: List[str]) -> str:
        """Convert number schema"""
        minimum = schema.get("minimum")
        maximum = schema.get("maximum")
        if schema.get('exclusiveMinimum') is not None or schema.get('exclusiveMaximum') is not None:
            notes.append("exclusive bound shown as inclusive")
            if not isinstance(schema.get('exclusiveMinimum'), bool) and schema.get('exclusiveMinimum') is not None:
                minimum = schema['exclusiveMinimum']
            if not isinstance(schema.get('exclusiveMaximum'), bool) and schema.get('exclusiveMaximum') is not None:
                maximum = schema['exclusiveMaximum']

        if minimum is not None and maximum is not None:
            return f"(Float {_number_literal(minimum)} .. {_number_literal(maximum)})"
        elif minimum is not None:
            return f"(Float {_number_literal(minimum)} ..)"
        elif maximum is not None:
            return f"(Float .. {_number_literal(maximum)})"
        return "Float"

    def _convert_const(self, schema: dict, name: str, notes: List[str], top: bool) -> str:
        value = schema['const']
        if isinstance(value, str):
            return self._convert_enum({'enum': [value]}, name, notes, top)
        if isinstance(value, bool):
            notes.append(f"const: {json.dumps(value)}")
            return "Bool"
        if isinstance(value, int):
            notes.append(f"const: {value}")
            return "Int"
        if isinstance(value, float):
            notes.append(f"const: {value}")
            return "Float"
        return self._warn(name, f"const {json.dumps(value)}", notes)

    def _convert_enum(self, schema: dict, name: str, notes: List[str], top: bool = False) -> str:
        """Convert enum schema"""
        values = schema.get("enum") or []
        non_null = [v for v in values if v is not None]
        schema_type = schema.get('type')
        nullable = (None in values or schema_type == 'null'
                    or (isinstance(schema_type, list) and 'null' in schema_type))

        if not non_null:
            return self._warn(name, "enum with no non-null value", notes)
        if all(isinstance(v, str) for v in non_null):
            result = self._string_enum(non_null, name, top)
        elif all(isinstance(v, bool) for v in non_null):
            result = "Bool"
        elif all(isinstance(v, int) and not isinstance(v, bool) for v in non_null):
            notes.append("enum: " + ', '.join(str(v) for v in non_null))
            result = f"(Int {min(non_null)} .. {max(non_null)})"
        elif all(isinstance(v, (int, float)) and not isinstance(v, bool) for v in non_null):
            notes.append("enum: " + ', '.join(str(v) for v in non_null))
            result = "Float"
        else:
            return self._warn(name, "enum mixing value types", notes)
        return _option(result) if nullable else result

    def _string_enum(self, values: List[str], name: str, top: bool) -> str:
        key = tuple(dict.fromkeys(values))
        if not top and key in self._enum_by_values:
            return self._enum_by_values[key]

        tname = self._take_name(name, top)
        used: set = set()
        variants = [_unique(to_kebab(v, 'v') if v.strip() else 'empty', used) for v in key]
        variants = self.namer.claim_variants(variants, to_kebab(tname))
        self.enum_values[tname] = dict(zip(key, variants))
        comment = None
        if any(v != var for v, var in zip(key, variants)):
            comment = "JSON values: " + ' '.join(json.dumps(v) for v in key)
        self._define(tname, f"(enum {' '.join(variants)})", comment)
        self._enum_by_values.setdefault(key, tname)
        return tname

    def _convert_union(self, schema: dict, name: str, notes: List[str], top: bool = False) -> str:
        """Convert oneOf/anyOf to union"""
        variants = schema.get("oneOf") or schema.get("anyOf") or []
        non_null = [v for v in variants if not _is_null_schema(v)]
        nullable = len(non_null) < len(variants)

        if not non_null:
            return self._warn(name, "oneOf/anyOf with no non-null alternative", notes)
        if len(non_null) == 1:
            inner = self._convert_schema(non_null[0], name, notes, top)
            return _option(inner) if nullable else inner

        tname = self._take_name(name, top)
        prefix = to_kebab(tname)
        tags, payloads, payload_notes, used = [], [], [], set()
        for i, variant in enumerate(non_null):
            vnotes: List[str] = []
            if isinstance(variant, dict) and '$ref' in variant:
                payload = self._resolve_ref(variant['$ref'], tname, vnotes)
                tag = to_kebab(payload) if payload != 'String' or not vnotes else f"{prefix}-{i}"
            else:
                payload = self._convert_schema(variant, f"{tname}V{i}", vnotes)
                tag = f"{prefix}-{i}"
            tags.append(_unique(tag, used))
            payloads.append(payload)
            payload_notes.append(vnotes)

        tags = self.namer.claim_variants(tags, prefix)
        lines = []
        for tag, payload, vnotes in zip(tags, payloads, payload_notes):
            for n in vnotes:
                lines.append(_comment(n))
            lines.append(f"({tag} {payload})")
        self._define(tname, "(union\n    " + "\n    ".join(lines) + ")")
        self.unions.add(tname)
        result = tname
        return _option(result) if nullable else result

    def _convert_all_of(self, schema: dict, name: str, notes: List[str], top: bool) -> str:
        parts = schema['allOf']
        rest = {k: v for k, v in schema.items() if k != 'allOf'}
        if len(parts) == 1 and 'properties' not in rest:
            return self._convert_schema(parts[0], name, notes, top)

        properties: Dict[str, Any] = {}
        required: List[str] = []
        pending = list(parts) + ([rest] if 'properties' in rest else [])
        depth = 0
        while pending and depth < 64:
            depth += 1
            part = self._deref(pending.pop(0))
            if not isinstance(part, dict):
                return self._warn(name, "allOf with an unresolvable part", notes)
            if 'allOf' in part:
                pending = list(part['allOf']) + pending
                if 'properties' not in part:
                    continue
            if part.get('type', 'object') != 'object' or (
                    'properties' not in part and any(k in part for k in ('oneOf', 'anyOf', 'enum'))):
                return self._warn(name, "allOf mixing non-object schemas", notes)
            properties.update(part.get('properties') or {})
            required.extend(part.get('required') or [])
        merged = {'type': 'object', 'properties': properties, 'required': required}
        return self._convert_object(merged, name, notes, top)

    # -- example values -----------------------------------------------------

    def is_container(self, type_expr: str) -> bool:
        type_expr = self.resolve_alias(type_expr)
        head, args = parse_type(type_expr)
        if head == 'Option' and args:
            return self.is_container(args[0])
        return head in CONTAINER_TYPE_HEADS

    def _field_comparable(self, type_expr: str) -> bool:
        """Whether slop test can compare a record field of this type.

        A container field is compared by identity, so its contents cannot be
        asserted. And the 0.4.0 tester mis-compiles some fields it should
        handle: a ranged String field is compared with C `==`, an Option of a
        container through a `.len` the Option does not have. A field of any
        type but a scalar, a plain String, an enum, or an Option of one of
        those is therefore written `_`, so the example still compiles.
        """
        head, args = parse_type(self.resolve_alias(type_expr))
        if head == 'Option' and args:
            inner = parse_type(self.resolve_alias(args[0]))[0]
            return inner != 'Option' and self._field_comparable(args[0])
        if head == 'String':
            return not args
        return (head in INT_TYPE_HEADS or head in FLOAT_TYPE_HEADS or head == 'Bool'
                or head in self.enum_values)

    def render_value(self, value: Any, type_expr: str, nested: bool,
                     in_record: bool = False) -> Optional[str]:
        """A SLOP expression for a JSON example value of type_expr, or None.

        `nested` is true inside an expected result, where a container is
        rendered `_` (it cannot be compared); `in_record` marks a record
        field, where whatever slop test cannot compare is rendered `_`.
        Outside an expected result (an argument), a value that cannot be
        written gives None, and the caller drops the example.
        """
        type_expr = self.resolve_alias(type_expr)
        head, args = parse_type(type_expr)
        if nested and (self.is_container(type_expr)
                       or (in_record and not self._field_comparable(type_expr))):
            return '_'
        if head == 'Option':
            if value is None:
                return '(none)'
            inner = self.render_value(value, args[0], nested) if args else None
            return f"(some {inner})" if inner is not None else None
        if value is None:
            return None
        if head in INT_TYPE_HEADS:
            if isinstance(value, float) and value.is_integer():
                value = int(value)
            if not isinstance(value, int) or isinstance(value, bool):
                return None
            if '..' in args:
                idx = args.index('..')
                lo = args[idx - 1] if idx > 0 else None
                hi = args[idx + 1] if idx + 1 < len(args) else None
                try:
                    if lo is not None and value < int(lo):
                        return None
                    if hi is not None and value > int(hi):
                        return None
                except ValueError:
                    return None
            return str(value)
        if head in FLOAT_TYPE_HEADS:
            if not isinstance(value, (int, float)) or isinstance(value, bool):
                return None
            try:
                return _float_literal(value)
            except ValueError:
                return None
        if head == 'Bool':
            return ('true' if value else 'false') if isinstance(value, bool) else None
        if head == 'String':
            return slop_string(value) if isinstance(value, str) else None
        if head in self.enum_values:
            variant = self.enum_values[head].get(value) if isinstance(value, str) else None
            return f"'{variant}" if variant else None
        if head in self.records:
            if not isinstance(value, dict):
                return None
            parts = []
            for prop, field_name, field_type in self.records[head]:
                if prop in value:
                    rendered = self.render_value(value[prop], field_type, nested, True)
                elif parse_type(field_type)[0] == 'Option':
                    rendered = '(none)' if not nested or self._field_comparable(field_type) else '_'
                else:
                    return None
                if rendered is None:
                    return None
                parts.append(f"({field_name} {rendered})")
            return f"(record-new {head} {' '.join(parts)})"
        return None


# ---------------------------------------------------------------------------
# SQL DDL
# ---------------------------------------------------------------------------

_SQL_IDENT = r'(?:"(?:[^"]|"")+"|`[^`]+`|\[[^\]]+\]|[A-Za-z_][\w$]*)'
_SQL_QNAME = _SQL_IDENT + r'(?:\s*\.\s*' + _SQL_IDENT + r')*'

_SQL_TEXT = {'VARCHAR', 'CHAR', 'CHARACTER', 'NCHAR', 'NVARCHAR', 'VARCHAR2',
             'NVARCHAR2', 'CHARACTER VARYING', 'CHAR VARYING', 'BPCHAR',
             'NATIONAL CHARACTER VARYING', 'NATIONAL CHAR VARYING', 'VARYING'}
_SQL_LONG_TEXT = {'TEXT', 'TINYTEXT', 'MEDIUMTEXT', 'LONGTEXT', 'CLOB', 'NCLOB',
                  'NTEXT', 'CITEXT', 'STRING', 'NAME'}
_SQL_AS_TEXT = {  # no SLOP type of their own: kept as text, noted, no warning
    'DATE', 'TIME', 'TIMETZ', 'DATETIME', 'DATETIME2', 'DATETIMEOFFSET',
    'SMALLDATETIME', 'TIMESTAMP', 'TIMESTAMPTZ', 'INTERVAL', 'JSON', 'JSONB',
    'XML', 'INET', 'CIDR', 'MACADDR', 'MACADDR8', 'TSVECTOR', 'TSQUERY',
    'ENUM', 'SET', 'MONEY_TEXT'}
_SQL_INT = {
    'INT': ('Int', 'U32'), 'INTEGER': ('Int', 'U32'), 'INT4': ('Int', 'U32'),
    'MEDIUMINT': ('Int', 'U32'), 'SERIAL': ('Int', 'U32'), 'SERIAL4': ('Int', 'U32'),
    'BIGINT': ('I64', 'U64'), 'INT8': ('I64', 'U64'), 'BIGSERIAL': ('I64', 'U64'),
    'SERIAL8': ('I64', 'U64'), 'SMALLINT': ('I16', 'U16'), 'INT2': ('I16', 'U16'),
    'SMALLSERIAL': ('I16', 'U16'), 'SERIAL2': ('I16', 'U16'), 'TINYINT': ('I8', 'U8'),
    'YEAR': ('Int', 'U32')}
_SQL_SERIAL = {'SERIAL', 'SERIAL2', 'SERIAL4', 'SERIAL8', 'BIGSERIAL', 'SMALLSERIAL'}
_SQL_DOUBLE = {'DOUBLE', 'DOUBLE PRECISION', 'FLOAT8', 'BINARY_DOUBLE'}
_SQL_SINGLE = {'REAL', 'FLOAT4', 'BINARY_FLOAT'}
_SQL_EXACT = {'DECIMAL', 'NUMERIC', 'DEC', 'NUMBER', 'MONEY', 'SMALLMONEY', 'FIXED'}
_SQL_BOOL = {'BOOLEAN', 'BOOL'}
_SQL_BYTES = {'BLOB', 'TINYBLOB', 'MEDIUMBLOB', 'LONGBLOB', 'BYTEA', 'BINARY',
              'VARBINARY', 'IMAGE', 'RAW'}
_SQL_UUID = {'UUID', 'UNIQUEIDENTIFIER'}
_SQL_ALL_TYPES = (_SQL_TEXT | _SQL_LONG_TEXT | _SQL_AS_TEXT | set(_SQL_INT) | _SQL_DOUBLE
                  | _SQL_SINGLE | _SQL_EXACT | _SQL_BOOL | _SQL_BYTES | _SQL_UUID
                  | {'FLOAT', 'BIT'})


def _sql_unquote(ident: str) -> str:
    ident = ident.strip()
    if len(ident) >= 2 and ident[0] == '"' and ident[-1] == '"':
        return ident[1:-1].replace('""', '"')
    if len(ident) >= 2 and ident[0] == '`' and ident[-1] == '`':
        return ident[1:-1]
    if len(ident) >= 2 and ident[0] == '[' and ident[-1] == ']':
        return ident[1:-1]
    return ident


def _sql_qname_parts(qname: str) -> List[str]:
    return [_sql_unquote(p) for p in re.findall(_SQL_IDENT, qname)]


def _strip_sql_comments(sql: str) -> str:
    def repl(m):
        text = m.group(0)
        if text.startswith('--') or text.startswith('/*'):
            return ' '
        return text
    return re.sub(r"'(?:[^']|'')*'|--[^\n]*|/\*.*?\*/", repl, sql, flags=re.DOTALL)


def _sql_split_top_level(body: str) -> List[str]:
    parts, depth, cur, quote = [], 0, '', None
    for ch in body:
        if quote:
            cur += ch
            if ch == quote:
                quote = None
            continue
        if ch in ("'", '"', '`'):
            quote = ch
        elif ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        elif ch == ',' and depth == 0:
            parts.append(cur.strip())
            cur = ''
            continue
        cur += ch
    if cur.strip():
        parts.append(cur.strip())
    return parts


def _sql_balanced(sql: str, open_idx: int) -> Optional[Tuple[str, int]]:
    """Body between the paren at open_idx and its match, and the end index."""
    depth, quote = 0, None
    for i in range(open_idx, len(sql)):
        ch = sql[i]
        if quote:
            if ch == quote:
                quote = None
            continue
        if ch in ("'", '"', '`'):
            quote = ch
        elif ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                return sql[open_idx + 1:i], i
    return None


def _sql_flatten(text: str) -> str:
    """Modifiers with string literals and parenthesized groups blanked out."""
    text = re.sub(r"'(?:[^']|'')*'", "''", text)
    prev = None
    while prev != text:
        prev = text
        text = re.sub(r'\([^()]*\)', '()', text)
    return text.upper()


class SqlSchemaConverter:
    """Convert SQL DDL (CREATE TABLE) to SLOP record types

    A column is (Option T) unless it is NOT NULL, part of the primary key, or
    a SERIAL. DECIMAL/NUMERIC become Float, dates and times String, each with
    a comment naming the SQL type. Postgres `CREATE TYPE ... AS ENUM` becomes
    an enum. Any other unknown column type becomes String with a warning.
    """

    _CREATE_TABLE = re.compile(
        r'\bCREATE\s+(?:OR\s+REPLACE\s+)?(?:(?:GLOBAL|LOCAL)\s+)?'
        r'(?:TEMP(?:ORARY)?\s+|UNLOGGED\s+)?TABLE\s+(?:IF\s+NOT\s+EXISTS\s+)?'
        r'(' + _SQL_QNAME + r')\s*\(', re.IGNORECASE)
    _CREATE_ENUM = re.compile(
        r'\bCREATE\s+TYPE\s+(' + _SQL_QNAME + r')\s+AS\s+ENUM\s*\(', re.IGNORECASE)
    _TABLE_CONSTRAINT = re.compile(
        r'^(?:CONSTRAINT|PRIMARY\s+KEY|FOREIGN\s+KEY|CHECK|EXCLUDE|PERIOD\s+FOR)\b',
        re.IGNORECASE)
    _INDEX_CONSTRAINT = re.compile(
        r'^(?:UNIQUE|INDEX|KEY|FULLTEXT|SPATIAL)\b(?:\s+(?:KEY|INDEX))?\s*'
        r'(?P<name>' + _SQL_IDENT + r')?\s*\(', re.IGNORECASE)
    _COLUMN_TYPE = re.compile(
        r'(?P<base>(?:NATIONAL\s+)?(?:CHARACTER|CHAR)\s+VARYING|DOUBLE\s+PRECISION|'
        r'[A-Za-z_][\w]*)\s*(?:\((?P<args>[^)]*)\))?(?P<array>(?:\s*\[\s*\d*\s*\])*)',
        re.IGNORECASE)

    def __init__(self):
        self.warnings: List[str] = []

    def convert(self, sql: str, module_name: Optional[str] = None) -> str:
        """Convert SQL CREATE TABLE statements to a SLOP module"""
        self.warnings = []
        self.namer = _Namer()
        self.enums: Dict[str, str] = {}  # lowercased SQL enum type name → SLOP type
        types: List[SlopType] = []
        sql = _strip_sql_comments(sql)

        for m in self._CREATE_ENUM.finditer(sql):
            found = _sql_balanced(sql, m.end() - 1)
            if not found:
                continue
            values = [v.replace("''", "'") for v in re.findall(r"'((?:[^']|'')*)'", found[0])]
            sql_name = _sql_qname_parts(m.group(1))[-1]
            tname = self.namer.claim_type(to_pascal(sql_name), 'Enum')
            used: set = set()
            variants = [_unique(to_kebab(v, 'v') if v.strip() else 'empty', used) for v in values]
            variants = self.namer.claim_variants(variants, to_kebab(tname))
            if not variants:
                continue
            types.append(SlopType(tname, f"(enum {' '.join(variants)})",
                                  f"From enum type: {sql_name}"))
            self.enums[sql_name.lower()] = tname

        for m in self._CREATE_TABLE.finditer(sql):
            found = _sql_balanced(sql, m.end() - 1)
            if not found:
                continue
            parts = _sql_qname_parts(m.group(1))
            table = parts[-1]
            type_name = self.namer.claim_type(to_pascal(table, 'Table'), 'Row')
            lines = self._parse_columns(found[0], '.'.join(parts))
            definition = "(record\n    " + "\n    ".join(lines) + ")" if lines else "(record)"
            types.append(SlopType(type_name, definition, f"From table: {'.'.join(parts)}"))

        return _render_module(
            _module_name(module_name, 'schema'),
            [";; Generated by slop derive from SQL DDL"],
            ['(@derived-from "sql")', "(@generation-mode deterministic)"],
            [t.to_slop() for t in types],
            [t.name for t in types])

    def _parse_columns(self, columns_str: str, table: str) -> List[str]:
        """SLOP field lines (with comment lines) for the columns of one table"""
        parts = _sql_split_top_level(columns_str)

        # Columns named by a table-level PRIMARY KEY are never optional.
        pk_columns = set()
        for part in parts:
            pk = re.search(r'\bPRIMARY\s+KEY\s*\(([^)]*)\)', part, re.IGNORECASE)
            if pk and self._is_table_constraint(part):
                pk_columns.update(_sql_unquote(c).lower()
                                  for c in pk.group(1).split(',') if c.strip())

        lines, used = [], set()
        for part in parts:
            if self._is_table_constraint(part):
                continue
            name_match = re.match(_SQL_IDENT, part)
            if not name_match:
                continue
            col_name = _sql_unquote(name_match.group(0))
            rest = part[name_match.end():].strip()
            where = f"{table}.{col_name}"

            notes: List[str] = []
            type_match = self._COLUMN_TYPE.match(rest)
            if not type_match:
                self.warnings.append(f"{where}: column has no type; using String")
                notes.append("no column type: kept as String")
                slop_type, base, modifiers = "String", '', rest
            else:
                base = re.sub(r'\s+', ' ', type_match.group('base').upper())
                modifiers = rest[type_match.end():]
                slop_type = self._sql_type_to_slop(
                    base, type_match.group('args'), _sql_flatten(modifiers),
                    type_match.group(0).strip(), where, notes)
                if type_match.group('array'):
                    slop_type = f"(List {slop_type})"

            flat = _sql_flatten(modifiers)
            not_null = (re.search(r'\bNOT\s+NULL\b', flat)
                        or re.search(r'\bPRIMARY\s+KEY\b', flat)
                        or col_name.lower() in pk_columns
                        or base in _SQL_SERIAL)
            if not not_null:
                slop_type = _option(slop_type)

            field_name = _unique(to_kebab(col_name, 'col'), used)
            for n in notes:
                lines.append(_comment(n))
            lines.append(f"({field_name} {slop_type})")
        return lines

    def _is_table_constraint(self, part: str) -> bool:
        if self._TABLE_CONSTRAINT.match(part):
            return True
        m = self._INDEX_CONSTRAINT.match(part)
        if not m:
            return False
        # `key VARCHAR(10)` is a column named key, not a KEY index.
        name = m.group('name')
        return not (name and name.upper() in _SQL_ALL_TYPES)

    def _sql_type_to_slop(self, sql_type: str, args: Optional[str], modifiers: str,
                          spelled: str, where: str, notes: List[str]) -> str:
        """Convert a normalized SQL base type (and its arguments) to SLOP"""
        sql_type = sql_type.upper()
        nums = [int(n) for n in re.findall(r'\d+', args or '')]
        length = nums[0] if nums else None
        unsigned = bool(re.search(r'\bUNSIGNED\b', modifiers))

        if sql_type in _SQL_TEXT:
            return f"(String .. {length})" if length else "String"
        if sql_type in _SQL_LONG_TEXT:
            return "String"
        if sql_type in _SQL_INT:
            return _SQL_INT[sql_type][1 if unsigned else 0]
        if sql_type == 'FLOAT':
            return "Float" if length and length > 24 else "F32"
        if sql_type in _SQL_SINGLE:
            return "F32"
        if sql_type in _SQL_DOUBLE:
            return "Float"
        if sql_type in _SQL_EXACT:
            notes.append(f"{spelled}: exact decimal held as Float")
            return "Float"
        if sql_type in _SQL_BOOL:
            return "Bool"
        if sql_type == 'BIT':
            if length is None or length == 1:
                return "Bool"
            notes.append(spelled)
            return "Bytes"
        if sql_type in _SQL_BYTES:
            return f"(Bytes .. {length})" if length else "Bytes"
        if sql_type in _SQL_UUID:
            return "(String 36 .. 36)"
        if sql_type.lower() in self.enums:
            return self.enums[sql_type.lower()]
        if sql_type in _SQL_AS_TEXT or sql_type.startswith('TIMESTAMP'):
            notes.append(f"{spelled}: kept as String")
            return "String"
        self.warnings.append(f"{where}: unsupported SQL type {spelled}; using String")
        notes.append(f"unsupported SQL type {spelled}: kept as String")
        return "String"


# ---------------------------------------------------------------------------
# OpenAPI
# ---------------------------------------------------------------------------

_HTTP_METHODS = ('get', 'post', 'put', 'patch', 'delete')


@dataclass
class _Operation:
    method: str
    path: str
    op: dict
    fn_name: str
    path_params: List[tuple]    # (name, type, schema, example-or-_MISSING)
    query_params: List[tuple]   # (name, type, schema, example-or-_MISSING, required)
    body_type: Optional[str]    # parameter type, (Ptr T) for a record
    return_type: str
    response_example: Any
    resource: Optional[str] = None  # key into OpenApiConverter.resources


_MISSING = object()


@dataclass
class _Resource:
    key: str          # kebab singular, e.g. pet
    plural: str       # kebab, e.g. pets
    type_name: str    # record type stored, e.g. Pet
    id_type: str      # e.g. PetId
    insert_type: Optional[str]  # record type a POST body carries, e.g. NewPet


class OpenApiConverter:
    """Convert OpenAPI 3.x (and Swagger 2.0) specs to SLOP types and function signatures

    Storage modes:
    - 'stub': a minimal State record plus a (@requires storage ...) block that
              declares the state-* functions the handlers' holes may call
    - 'map':  a Map-based State record and implemented state-* CRUD helpers
    - 'none': just types + one function with a hole per operation

    A path's resource is its last segment that is not a parameter, an `api`
    prefix or a version (`/api/v1/pets/{id}` → pet). Storage is generated
    for a resource only when a record type for it is known: a schema of that
    name, or the record its operations return.
    """

    def __init__(self, storage_mode: str = 'stub', module_name: Optional[str] = None):
        if storage_mode not in ('stub', 'map', 'none'):
            raise ValueError(f"unknown storage mode {storage_mode!r} (stub, map or none)")
        self.storage_mode = storage_mode
        self.module_name = module_name
        self._reset()

    def _reset(self):
        self.namer = _Namer()
        self.json_converter = JsonSchemaConverter(self.namer)
        self.types: List[SlopType] = []
        self.functions: List[SlopFunction] = []
        self.error_codes: set = set()
        self.error_variants: List[str] = []
        self.resources: Dict[str, _Resource] = {}
        self.resource_types: List[str] = []
        self.warnings: List[str] = []
        self.spec: dict = {}

    def convert(self, spec: dict, module_name: Optional[str] = None) -> str:
        """Convert OpenAPI spec to SLOP module with types and function stubs"""
        self._reset()
        self.spec = spec
        title = (spec.get('info') or {}).get('title') or 'Api'
        paths = spec.get('paths') or {}

        # 1. Error codes first, so ApiError's variants keep their plain names
        self._collect_error_codes(paths)
        self._generate_error_type()
        if self.storage_mode in ('stub', 'map'):
            self.namer.claim_type('State')

        # 2. Component schemas (Swagger 2.0 keeps them under definitions)
        schemas = dict(spec.get('definitions') or {})
        schemas.update((spec.get('components') or {}).get('schemas') or {})
        self.json_converter.add_named_schemas(schemas)
        self.json_converter.convert_named_schemas()

        # 3. Operations, then the resources they touch, then the functions
        operations = self._collect_operations(paths)
        if self.storage_mode in ('stub', 'map'):
            self._identify_resources(operations)
        for operation in operations:
            self.functions.append(self._build_function(operation))

        self.types = self.json_converter.types + self.types
        self.warnings = self.json_converter.warnings + self.warnings
        return self._generate_output(title, module_name or self.module_name)

    # -- spec walking -------------------------------------------------------

    def _deref(self, obj: Any) -> Any:
        """Follow a local $ref to a parameter, request body or response."""
        for _ in range(32):
            if not (isinstance(obj, dict) and isinstance(obj.get('$ref'), str)
                    and obj['$ref'].startswith('#/')):
                return obj
            target: Any = self.spec
            for part in obj['$ref'][2:].split('/'):
                part = part.replace('~1', '/').replace('~0', '~')
                if not isinstance(target, dict) or part not in target:
                    return {}
                target = target[part]
            obj = target
        return obj

    def _collect_error_codes(self, paths: dict):
        """Collect all HTTP error codes used in spec"""
        for path, methods in paths.items():
            if not isinstance(methods, dict):
                continue
            for method, operation in methods.items():
                if method not in ('get', 'post', 'put', 'patch', 'delete', 'head', 'options'):
                    continue
                if not isinstance(operation, dict):
                    continue
                for code_str in (operation.get('responses') or {}).keys():
                    try:
                        code = int(code_str)
                        if 400 <= code < 600:
                            self.error_codes.add(code)
                    except (TypeError, ValueError):
                        pass  # 'default', '4XX' or other non-numeric

    def _generate_error_type(self):
        """Generate unified ApiError enum from collected error codes"""
        error_map = {
            400: 'bad-request',
            401: 'unauthorized',
            403: 'forbidden',
            404: 'not-found',
            405: 'method-not-allowed',
            409: 'conflict',
            422: 'validation-error',
            429: 'too-many-requests',
            500: 'internal-error',
            502: 'bad-gateway',
            503: 'service-unavailable',
            504: 'gateway-timeout',
        }
        variants = [error_map.get(code, f'error-{code}') for code in sorted(self.error_codes)]
        variants.append('unknown-error')
        self.error_type = self.namer.claim_type('ApiError')
        self.error_variants = self.namer.claim_variants(variants, to_kebab(self.error_type))
        self.types.append(SlopType(
            self.error_type,
            f"(enum {' '.join(self.error_variants)})",
            "HTTP API error codes"
        ))

    def _collect_operations(self, paths: dict) -> List[_Operation]:
        operations, used_names = [], set()
        for path, methods in paths.items():
            if not isinstance(methods, dict):
                continue
            shared = methods.get('parameters') or []
            for method, operation in methods.items():
                if method not in _HTTP_METHODS or not isinstance(operation, dict):
                    continue
                operations.append(self._analyze_operation(
                    method, path, operation, shared, used_names))
        return operations

    def _analyze_operation(self, method: str, path: str, operation: dict,
                           shared_params: list, used_names: set) -> _Operation:
        fn_name = _unique(self._path_to_function_name(method, path), used_names)
        hint = to_pascal(fn_name)

        params: Dict[tuple, dict] = {}
        for raw in list(shared_params) + list(operation.get('parameters') or []):
            param = self._deref(raw)
            if isinstance(param, dict) and 'name' in param:
                params[(param.get('in'), param['name'])] = param

        used_params = {'arena', 'state', 'body'}
        path_params, query_params, body_type = [], [], None
        for (location, raw_name), param in params.items():
            if location not in ('path', 'query', 'body'):
                continue
            schema = param.get('schema')
            if schema is None and 'type' in param:  # Swagger 2.0 inline parameter
                schema = {k: v for k, v in param.items()
                          if k not in ('name', 'in', 'required', 'description')}
            schema = schema or {}
            if location == 'body':  # Swagger 2.0 body parameter
                body_type = self._body_param_type(schema, f"{hint}Body")
                continue
            name = _unique(to_kebab(raw_name, 'param'), used_params)
            ptype = self.json_converter.convert_inline(schema, f"{hint}{to_pascal(raw_name)}")
            example = self._param_example(param, schema)
            if location == 'path':
                path_params.append((name, ptype, schema, example))
            else:
                query_params.append((name, ptype, schema, example, bool(param.get('required'))))

        if 'requestBody' in operation:
            body_schema = self._extract_body_schema(self._deref(operation['requestBody']))
            if body_schema:
                body_type = self._body_param_type(body_schema, f"{hint}Body")

        return_type, response_example = self._extract_response(operation, f"{hint}Response")
        # The operation as seen with the path-level parameters merged in.
        operation = {**operation, 'parameters': list(params.values())}
        return _Operation(method, path, operation, fn_name, path_params, query_params,
                          body_type, return_type, response_example)

    def _body_param_type(self, schema: dict, hint: str) -> str:
        body_type = self.json_converter.convert_inline(schema, hint)
        if self.json_converter.is_record(body_type):
            return f"(Ptr {body_type})"
        return body_type

    @staticmethod
    def _param_example(param: dict, schema: dict) -> Any:
        if 'example' in param:
            return param['example']
        if isinstance(param.get('examples'), dict) and param['examples']:
            first = next(iter(param['examples'].values()))
            if isinstance(first, dict) and 'value' in first:
                return first['value']
        if isinstance(schema, dict) and 'example' in schema:
            return schema['example']
        return _MISSING

    @staticmethod
    def _json_content(content: Any) -> Optional[dict]:
        if not isinstance(content, dict) or not content:
            return None
        if 'application/json' in content:
            return content['application/json']
        for media, value in content.items():
            if 'json' in media:
                return value
        return next(iter(content.values()))

    def _extract_body_schema(self, request_body: Any) -> Optional[dict]:
        """Extract schema from request body"""
        media = self._json_content((request_body or {}).get('content'))
        return media.get('schema') if isinstance(media, dict) else None

    def _extract_response(self, operation: dict, hint: str) -> Tuple[str, Any]:
        """Success response type and its example (or _MISSING)"""
        responses = operation.get('responses') or {}
        success = sorted((str(c), r) for c, r in responses.items()
                         if re.fullmatch(r'2(\d\d|XX)', str(c)))
        for _, response in success:
            response = self._deref(response)
            if not isinstance(response, dict):
                continue
            media = self._json_content(response.get('content'))
            schema = media.get('schema') if isinstance(media, dict) else response.get('schema')
            if not schema:
                continue
            example = _MISSING
            if isinstance(media, dict):
                if 'example' in media:
                    example = media['example']
                elif isinstance(media.get('examples'), dict) and media['examples']:
                    first = next(iter(media['examples'].values()))
                    if isinstance(first, dict) and 'value' in first:
                        example = first['value']
            elif isinstance(response.get('examples'), dict):  # Swagger 2.0
                example = response['examples'].get('application/json', _MISSING)
            return self.json_converter.convert_inline(schema, hint), example
        return 'Unit', _MISSING

    def _schema_to_type(self, schema: dict, hint: str = 'Inline') -> str:
        """Convert OpenAPI schema to SLOP type reference"""
        return self.json_converter.convert_inline(schema, hint)

    # -- resources ----------------------------------------------------------

    @staticmethod
    def _resource_segment(path: str) -> Optional[str]:
        """The last path segment that names a resource, or None"""
        segments = [s for s in path.split('/') if s and not s.startswith('{')]
        meaningful = [s for s in segments
                      if s.lower() not in ('api', 'rest')
                      and not re.fullmatch(r'v\d+(\.\d+)*', s.lower())]
        return meaningful[-1] if meaningful else None

    def _identify_resources(self, operations: List[_Operation]):
        """Group operations by resource and decide what storage each gets"""
        records = self.json_converter.records
        groups: Dict[str, List[_Operation]] = {}
        plurals: Dict[str, str] = {}
        for op in operations:
            segment = self._resource_segment(op.path)
            if segment:
                rname = to_pascal(_singular(to_kebab(segment)))
                groups.setdefault(rname, []).append(op)
                if to_kebab(segment) != to_kebab(rname):
                    plurals.setdefault(rname, to_kebab(segment))

        for rname, ops in groups.items():
            type_name = rname if rname in records else None
            if type_name is None:
                # No schema of that name: the record an item lookup or a
                # create returns, or the element of a listing. A GET that
                # returns one record and takes no id (`/health`) is not a
                # collection, so it names no resource.
                for op in ops:
                    inner = self.json_converter.resolve_alias(op.return_type)
                    head, args = parse_type(inner)
                    if head == 'List' and args and op.method == 'get':
                        inner = self.json_converter.resolve_alias(args[0])
                    elif not (op.method == 'post' or (op.method == 'get' and op.path_params)):
                        continue
                    if inner in records:
                        type_name = inner
                        break
            if type_name is None:
                continue

            insert_type = None
            for op in ops:
                if op.method == 'post' and op.body_type and op.body_type.startswith('(Ptr '):
                    insert_type = parse_type(op.body_type)[1][0]
                    break
            if insert_type is None and f"New{type_name}" in records:
                insert_type = f"New{type_name}"

            key = to_kebab(rname)
            resource = _Resource(key, plurals.get(rname, f"{key}s"), type_name,
                                 self.namer.claim_type(f"{rname}Id"), insert_type)
            self.resources[key] = resource
            self.resource_types.append(rname)
            for op in ops:
                op.resource = key

    def _storage_fn(self, op: _Operation) -> Optional[str]:
        resource = self.resources.get(op.resource) if op.resource else None
        if resource is None:
            return None
        if op.method == 'get':
            return (f"state-get-{resource.key}" if op.path_params
                    else f"state-list-{resource.plural}")
        if op.method == 'post':
            return f"state-insert-{resource.key}" if resource.insert_type else None
        if op.method == 'delete':
            return f"state-delete-{resource.key}"
        return f"state-get-{resource.key}"  # put / patch: read, then write back

    # -- functions ----------------------------------------------------------

    def _build_function(self, op: _Operation) -> SlopFunction:
        params, context, preconditions = [], [], []
        uses_storage = op.resource is not None
        if uses_storage:
            # POST needs the arena for state-insert-*, and a collection GET
            # needs one for state-list-*: listing builds a new (List T) out of
            # the map, so it allocates just as inserting does (#83).
            if op.method == 'post' or (op.method == 'get' and not op.path_params):
                params.append(('arena', 'Arena'))
                context.append('arena')
            params.append(('state', '(Ptr State)'))
            context.append('state')
            preconditions.append("(!= state nil)")

        for name, ptype, schema, _ in op.path_params:
            params.append((name, ptype))
            context.append(name)
            if schema.get('type') in ('integer', 'number'):
                if 'minimum' in schema:
                    preconditions.append(f"(>= {name} {_number_literal(schema['minimum'])})")
                if 'maximum' in schema:
                    preconditions.append(f"(<= {name} {_number_literal(schema['maximum'])})")

        for name, ptype, _, _, required in op.query_params:
            params.append((name, ptype if required else _option(ptype)))
            context.append(name)

        if op.body_type:
            params.append(('body', op.body_type))
            context.append('body')
            if op.body_type.startswith('(Ptr '):
                preconditions.append("(!= body nil)")

        storage_fn = self._storage_fn(op)
        if storage_fn:
            context.append(storage_fn)

        summary = op.op.get('summary') or ''
        description = op.op.get('description') or ''
        intent = _one_line(summary or description or f"{op.method.upper()} {op.path}")
        if len(intent) > 100:
            intent = intent[:97].rstrip() + '...'

        examples = None if uses_storage else self._extract_examples(op)

        return SlopFunction(
            name=op.fn_name,
            params=params,
            return_type=f"(Result {op.return_type} {self.error_type})",
            intent=intent,
            hole_prompt=self._generate_hole_prompt(op.method, op.path, op.op, storage_fn),
            hole_tier=self._classify_operation_tier(op.method, op.op),
            context=context or None,
            preconditions=preconditions or None,
            postconditions=self._extract_postconditions(op.op, op.return_type),
            examples=examples,
        )

    def _extract_postconditions(self, operation: dict, return_type: str) -> Optional[List[str]]:
        """Generate @post conditions from response schema"""
        posts = []
        head = parse_type(self.json_converter.resolve_alias(return_type))[0]
        if head == 'List':
            # list-len, not len: `len` is not a builtin in the checker, the
            # transpiler or the runtime. And the binding is `xs` rather
            # than `list`, which is a reserved form name (#83).
            posts.append(
                "(match $result ((ok xs) (>= (list-len xs) 0)) ((error _) true))"
            )
        elif head == 'Ptr':
            # Only a pointer can be nil; a record value never is.
            posts.append("(match $result ((ok val) (!= val nil)) ((error _) true))")
        return posts or None

    def _extract_examples(self, op: _Operation) -> Optional[List[tuple]]:
        """One @example from the spec's parameter and response examples, if expressible

        Every parameter needs a value (an optional query parameter without an
        example is passed as (none)), a request body cannot be written as an
        argument, and the response example must render against the return
        type. Otherwise no example is emitted.
        """
        if op.response_example is _MISSING or op.body_type or op.return_type == 'Unit':
            return None
        if op.response_example is None:
            return None
        conv = self.json_converter
        args = []
        for _, ptype, _, example in op.path_params:
            if example is _MISSING:
                return None
            rendered = conv.render_value(example, ptype, nested=False)
            if rendered is None:
                return None
            args.append(rendered)
        for _, ptype, _, example, required in op.query_params:
            if example is _MISSING:
                if required:
                    return None
                args.append('(none)')
                continue
            rendered = conv.render_value(example, ptype if required else _option(ptype),
                                         nested=False)
            if rendered is None:
                return None
            args.append(rendered)
        if not args:
            return None
        if conv.is_container(op.return_type):
            return None
        expected = conv.render_value(op.response_example, op.return_type, nested=True)
        if expected is None or expected == '_':
            return None
        return [(args, f"(ok {expected})")]

    def _generate_hole_prompt(self, method: str, path: str, operation: dict,
                              storage_fn: Optional[str] = None) -> str:
        """Generate descriptive hole prompt"""
        prompts = {
            'get': "Fetch data from storage",
            'post': "Create new resource and persist to storage",
            'put': "Update existing resource in storage",
            'patch': "Partially update resource fields",
            'delete': "Remove resource from storage"
        }
        base = prompts.get(method.lower(), f"Handle {method.upper()} request")

        params = [self._deref(p) for p in operation.get('parameters') or []]
        path_params = [p['name'] for p in params
                       if isinstance(p, dict) and p.get('in') == 'path' and 'name' in p]
        if path_params:
            base += f" using {', '.join(path_params)}"

        if storage_fn:
            base += f". Use {storage_fn}"

        return base

    def _classify_operation_tier(self, method: str, operation: dict) -> str:
        """Determine hole complexity tier for an operation"""
        params = [self._deref(p) for p in operation.get('parameters') or []]
        params = [p for p in params if isinstance(p, dict)]
        has_pagination = any(
            p.get('name') in ('page', 'limit', 'offset', 'cursor', 'skip', 'take')
            for p in params
        )

        method_lower = method.lower()
        if method_lower == 'get':
            # GET with path param is simple lookup
            path_params = [p for p in params if p.get('in') == 'path']
            if path_params and not has_pagination:
                return 'tier-1'
            return 'tier-2'
        elif method_lower in ('post', 'delete'):
            return 'tier-2'
        elif method_lower in ('put', 'patch'):
            return 'tier-3'
        return 'tier-2'

    # -- output -------------------------------------------------------------

    def _generate_output(self, title: str, module_name: Optional[str] = None) -> str:
        """Generate complete SLOP module based on storage mode"""
        forms: List[str] = []
        exports: List[str] = []

        for t in self.types:
            forms.append(t.to_slop())
            exports.append(t.name)

        if self.storage_mode == 'stub':
            forms.extend(self._generate_stub_state())
            exports.append('State')
            exports.extend(r.id_type for r in self.resources.values())
            if self.resources:
                forms.append(self._generate_requires_block())
        elif self.storage_mode == 'map':
            forms.extend(self._generate_state_types())
            exports.append('State')
            exports.extend(r.id_type for r in self.resources.values())
            helpers = self._generate_state_functions()
            forms.extend(text for _, text in helpers)
            exports.extend(name for name, _ in helpers)

        for fn in self.functions:
            forms.append(fn.to_slop())
            exports.append(fn.name)

        return _render_module(
            _module_name(module_name, title),
            [";; Generated by slop derive from OpenAPI"],
            ['(@derived-from "openapi")', "(@generation-mode deterministic)"],
            forms, exports)

    def _id_types(self) -> List[str]:
        return [f"(type {r.id_type} (Int 1 ..))" for r in self.resources.values()]

    def _generate_stub_state(self) -> List[str]:
        state = (";; Storage state: add the fields your storage implementation needs\n"
                 "(type State (record))")
        return self._id_types() + [state]

    def _generate_requires_block(self) -> str:
        """Generate (@requires storage ...) block for stub mode"""
        lines = [";; Storage requirements (interactive - resolve before filling holes)"]
        lines.append("(@requires storage")
        lines.append('  :prompt "Which storage approach for this API?"')
        lines.append("  :options (")
        lines.append('    ("In-memory Map - simple, good for prototypes" map)')
        lines.append('    ("Database stubs - I\'ll provide db-* implementations" db)')
        lines.append('    ("Custom - I\'ll implement storage myself" custom))')

        for r in self.resources.values():
            lines.append(f"  ;; {r.type_name} storage functions")
            lines.append(f"  (state-get-{r.key} ((state (Ptr State)) (id {r.id_type})) "
                         f"-> (Option {r.type_name}))")
            lines.append(f"  (state-list-{r.plural} ((arena Arena) (state (Ptr State)) "
                         f"(limit (Option Int))) -> (List {r.type_name}))")
            if r.insert_type:
                lines.append(f"  (state-insert-{r.key} ((arena Arena) (state (Ptr State)) "
                             f"(item (Ptr {r.insert_type}))) -> {r.type_name})")
            lines.append(f"  (state-delete-{r.key} ((state (Ptr State)) (id {r.id_type})) -> Bool)")

        lines[-1] += ")"
        return '\n'.join(lines)

    def _generate_state_types(self) -> List[str]:
        """Generate State type for map mode"""
        state_fields = []
        for r in self.resources.values():
            state_fields.append(f"  ({r.plural} (Map {r.id_type} {r.type_name}))")
            state_fields.append(f"  (next-{r.key}-id {r.id_type})")
        if state_fields:
            state = ";; State (generated for Map-based storage)\n(type State (record\n" \
                    + '\n'.join(state_fields) + "))"
        else:
            state = ";; State (generated for Map-based storage)\n(type State (record))"
        return self._id_types() + [state]

    def _generate_state_functions(self) -> List[Tuple[str, str]]:
        """Generate CRUD helper functions for map mode, as (name, text) pairs"""
        fns: List[Tuple[str, str]] = []
        records = self.json_converter.records

        body = [";; State helper functions (deterministic - no holes)",
                "(fn state-new ((arena Arena))",
                '  (@intent "Create new empty state")',
                "  (@spec ((Arena) -> (Ptr State)))",
                "  (@alloc arena)",
                "  (let ((s (cast (Ptr State) (arena-alloc arena (sizeof State)))))"]
        for r in self.resources.values():
            # (map-new arena K V), not (map-empty): the latter has never
            # existed in the checker, the transpiler or the runtime (#83).
            body.append(f"    (set! s {r.plural} (map-new arena {r.id_type} {r.type_name}))")
            body.append(f"    (set! s next-{r.key}-id 1)")
        body.append("    s))")
        fns.append(('state-new', '\n'.join(body)))

        for r in self.resources.values():
            t = r.type_name
            if r.insert_type:
                fields = {f: ty for _, f, ty in records.get(t, [])}
                new_fields = {f: ty for _, f, ty in records.get(r.insert_type, [])}
                lines = [f"(fn make-{r.key}-from-new ((arena Arena) (id {r.id_type}) "
                         f"(item (Ptr {r.insert_type})))",
                         f'  (@intent "Create {t} from {r.insert_type} with assigned ID")',
                         f"  (@spec ((Arena {r.id_type} (Ptr {r.insert_type})) -> {t}))",
                         "  (@alloc arena)",
                         f"  (let ((p (cast (Ptr {t}) (arena-alloc arena (sizeof {t})))))"]
                id_head = parse_type(self.json_converter.resolve_alias(fields.get('id', '')))
                if id_head[0] == 'Int' or id_head[0] in INT_TYPE_HEADS:
                    lines.append("    (set! p id id)")
                elif id_head[0] == 'Option' and id_head[1] and parse_type(
                        self.json_converter.resolve_alias(id_head[1][0]))[0] in INT_TYPE_HEADS:
                    lines.append("    (set! p id (some id))")
                elif 'id' in fields:
                    lines.append(f"    ;; id is {fields['id']}, not an integer: it is not assigned")
                copied, skipped = [], []
                for f, ty in fields.items():
                    if f == 'id':
                        continue
                    if new_fields.get(f) == ty:
                        copied.append(f)
                        lines.append(f"    (set! p {f} (. item {f}))")
                    else:
                        skipped.append(f)
                if skipped:
                    lines.append(f"    ;; not in {r.insert_type} with the same type, left zeroed: "
                                 + ' '.join(skipped))
                lines.append("    (deref p)))")
                fns.append((f"make-{r.key}-from-new", '\n'.join(lines)))

            fns.append((f"state-get-{r.key}", f"""(fn state-get-{r.key} ((state (Ptr State)) (id {r.id_type}))
  (@intent "Get {r.key} by ID from state")
  (@spec (((Ptr State) {r.id_type}) -> (Option {t})))
  (@pure)
  (map-get (. state {r.plural}) id))"""))
            # map-values is not an implemented builtin -- it has no checker
            # entry and no transpiler lowering, only a for-each element-type
            # helper. map-keys plus map-get is the same walk using builtins
            # that exist. It allocates, so the function takes the arena and is
            # no longer @pure (#83).
            fns.append((f"state-list-{r.plural}", f"""(fn state-list-{r.plural} ((arena Arena) (state (Ptr State)) (limit (Option Int)))
  (@intent "List all {r.plural} from state")
  (@spec ((Arena (Ptr State) (Option Int)) -> (List {t})))
  (@alloc arena)
  (let ((out (list-new arena {t})))
    (for-each (k (map-keys (. state {r.plural})))
      (match (map-get (. state {r.plural}) k)
        ((some v) (list-push out v))
        ((none) (do))))
    out))"""))
            if r.insert_type:
                fns.append((f"state-insert-{r.key}", f"""(fn state-insert-{r.key} ((arena Arena) (state (Ptr State)) (item (Ptr {r.insert_type})))
  (@intent "Insert new {r.key} into state")
  (@spec ((Arena (Ptr State) (Ptr {r.insert_type})) -> {t}))
  (@alloc arena)
  (let ((id (. state next-{r.key}-id)))
    (set! state next-{r.key}-id (+ id 1))
    (let ((new-item (make-{r.key}-from-new arena id item)))
      (map-put (. state {r.plural}) id new-item)
      new-item)))"""))
            fns.append((f"state-delete-{r.key}", f"""(fn state-delete-{r.key} ((state (Ptr State)) (id {r.id_type}))
  (@intent "Delete {r.key} from state by ID")
  (@spec (((Ptr State) {r.id_type}) -> Bool))
  (if (map-has (. state {r.plural}) id)
    (do (map-remove (. state {r.plural}) id) true)
    false))"""))

        return fns

    def _path_to_function_name(self, method: str, path: str) -> str:
        """Convert HTTP method + path to function name"""
        parts = []
        for seg in (s for s in path.split('/') if s):
            if seg.startswith('{') and seg.endswith('}'):
                parts.append(f"by-{to_kebab(seg[1:-1], 'param')}")
            else:
                parts.append(to_kebab(seg, 'seg'))

        verb_map = {
            'get': 'get',
            'post': 'create',
            'put': 'update',
            'patch': 'patch',
            'delete': 'delete'
        }
        prefix = verb_map.get(method.lower(), to_kebab(method))
        return f"{prefix}-{'-'.join(parts) or 'root'}"

    def _to_type_name(self, s: str) -> str:
        return to_pascal(s)

    def _to_kebab(self, s: str) -> str:
        return to_kebab(s)


# ---------------------------------------------------------------------------
# File-level entry points
# ---------------------------------------------------------------------------

def detect_schema_format(data: dict) -> str:
    """Detect schema format from parsed content"""
    if "openapi" in data:
        return "openapi"
    elif "swagger" in data:
        return "swagger"  # OpenAPI 2.x
    elif "paths" in data:
        return "openapi"
    else:
        return "jsonschema"


def _report(warnings_out: Optional[list], warnings: List[str]):
    if warnings_out is not None:
        warnings_out.extend(warnings)
    else:
        for w in warnings:
            print(f"warning: {w}", file=sys.stderr)


def convert_json_schema(schema_path: str, module_name: Optional[str] = None,
                        warnings: Optional[list] = None) -> str:
    """Convert JSON Schema file to SLOP"""
    schema = load_spec(schema_path)
    name = schema.get("title") or "Root"
    converter = JsonSchemaConverter()
    output = converter.convert(schema, name, module_name=module_name)
    _report(warnings, converter.warnings)
    return output


def convert_sql(sql_path: str, module_name: Optional[str] = None,
                warnings: Optional[list] = None) -> str:
    """Convert SQL DDL file to SLOP"""
    with open(sql_path) as f:
        sql = f.read()
    converter = SqlSchemaConverter()
    output = converter.convert(sql, module_name=module_name)
    _report(warnings, converter.warnings)
    return output


def convert_openapi(spec_path: str, storage_mode: str = 'stub',
                    module_name: Optional[str] = None,
                    warnings: Optional[list] = None) -> str:
    """Convert OpenAPI spec file to SLOP"""
    spec = load_spec(spec_path)
    converter = OpenApiConverter(storage_mode=storage_mode)
    output = converter.convert(spec, module_name=module_name)
    _report(warnings, converter.warnings)
    return output


def load_spec(path: str) -> dict:
    """Load spec from JSON or YAML file"""
    if path.endswith(('.yaml', '.yml')):
        try:
            import yaml
        except ImportError:
            raise ImportError(
                "PyYAML required for YAML files. Install with: pip install pyyaml"
            )
        with open(path) as f:
            data = yaml.safe_load(f)
    else:
        with open(path) as f:
            data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected a JSON/YAML object at the top level")
    return data


_load_spec = load_spec
