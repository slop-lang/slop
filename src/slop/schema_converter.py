"""
SLOP Schema Converter - Deterministic type generation from schemas

Converts:
- JSON Schema → SLOP types
- SQL DDL → SLOP types
- OpenAPI → SLOP types + signatures
"""

import json
import re
from typing import Dict, List, Optional, Any
from dataclasses import dataclass


@dataclass
class SlopType:
    """Represents a SLOP type definition"""
    name: str
    definition: str
    comment: Optional[str] = None

    def to_slop(self) -> str:
        lines = []
        if self.comment:
            lines.append(f";; {self.comment}")
        lines.append(f"(type {self.name} {self.definition})")
        return '\n'.join(lines)


class JsonSchemaConverter:
    """Convert JSON Schema to SLOP types"""

    def __init__(self):
        self.types: List[SlopType] = []
        self.type_names: Dict[str, str] = {}

    def convert(self, schema: dict, root_name: str = "Root") -> str:
        """Convert JSON Schema to SLOP type definitions"""
        self.types = []
        self.type_names = {}

        # Handle definitions/components first
        if "definitions" in schema:
            for name, defn in schema["definitions"].items():
                self._convert_schema(defn, self._to_type_name(name))

        if "$defs" in schema:
            for name, defn in schema["$defs"].items():
                self._convert_schema(defn, self._to_type_name(name))

        # Convert root schema
        self._convert_schema(schema, root_name)

        # Generate output
        lines = [";; Generated from JSON Schema", ""]
        for t in self.types:
            lines.append(t.to_slop())
            lines.append("")

        return '\n'.join(lines)

    def _convert_schema(self, schema: dict, name: str) -> str:
        """Convert a schema node, returning type expression"""
        if "$ref" in schema:
            ref = schema["$ref"].split("/")[-1]
            return self._to_type_name(ref)

        schema_type = schema.get("type", "any")

        if schema_type == "object":
            return self._convert_object(schema, name)
        elif schema_type == "array":
            return self._convert_array(schema, name)
        elif schema_type == "string":
            return self._convert_string(schema)
        elif schema_type == "integer":
            return self._convert_integer(schema)
        elif schema_type == "number":
            return self._convert_number(schema)
        elif schema_type == "boolean":
            return "Bool"
        elif "enum" in schema:
            return self._convert_enum(schema, name)
        elif "oneOf" in schema or "anyOf" in schema:
            return self._convert_union(schema, name)
        else:
            return "Any"

    def _convert_object(self, schema: dict, name: str) -> str:
        """Convert object schema to record type"""
        properties = schema.get("properties", {})
        required = set(schema.get("required", []))

        if not properties:
            return "(Map String Any)"

        fields = []
        for prop_name, prop_schema in properties.items():
            field_type = self._convert_schema(prop_schema, f"{name}{self._to_type_name(prop_name)}")

            if prop_name not in required:
                field_type = f"(Option {field_type})"

            field_name = self._to_field_name(prop_name)
            fields.append(f"({field_name} {field_type})")

        definition = "(record\n    " + "\n    ".join(fields) + ")"

        self.types.append(SlopType(name, definition))
        self.type_names[name] = name
        return name

    def _convert_array(self, schema: dict, name: str) -> str:
        """Convert array schema to List type"""
        items = schema.get("items", {})
        item_type = self._convert_schema(items, f"{name}Item")

        min_items = schema.get("minItems")
        max_items = schema.get("maxItems")

        if min_items is not None and max_items is not None:
            return f"(List {item_type} {min_items} .. {max_items})"
        elif min_items is not None:
            return f"(List {item_type} {min_items} ..)"
        elif max_items is not None:
            return f"(List {item_type} .. {max_items})"
        else:
            return f"(List {item_type})"

    def _convert_string(self, schema: dict) -> str:
        """Convert string schema with constraints"""
        min_len = schema.get("minLength")
        max_len = schema.get("maxLength")
        pattern = schema.get("pattern")
        format_ = schema.get("format")

        # Handle common formats
        if format_ == "email":
            return "(String 5 .. 255)"  # Email type
        elif format_ == "date-time":
            return "DateTime"
        elif format_ == "date":
            return "Date"
        elif format_ == "uri":
            return "(String 1 .. 2048)"
        elif format_ == "uuid":
            return "(String 36 .. 36)"

        # Handle length constraints
        if min_len is not None and max_len is not None:
            return f"(String {min_len} .. {max_len})"
        elif min_len is not None:
            return f"(String {min_len} ..)"
        elif max_len is not None:
            return f"(String .. {max_len})"
        else:
            return "String"

    def _convert_integer(self, schema: dict) -> str:
        """Convert integer schema with constraints"""
        minimum = schema.get("minimum")
        maximum = schema.get("maximum")
        exclusive_min = schema.get("exclusiveMinimum")
        exclusive_max = schema.get("exclusiveMaximum")

        # Handle exclusive bounds
        if exclusive_min is not None:
            minimum = exclusive_min + 1
        if exclusive_max is not None:
            maximum = exclusive_max - 1

        if minimum is not None and maximum is not None:
            return f"(Int {minimum} .. {maximum})"
        elif minimum is not None:
            return f"(Int {minimum} ..)"
        elif maximum is not None:
            return f"(Int .. {maximum})"
        else:
            return "Int"

    def _convert_number(self, schema: dict) -> str:
        """Convert number schema"""
        minimum = schema.get("minimum")
        maximum = schema.get("maximum")

        if minimum is not None and maximum is not None:
            return f"(Float {minimum} .. {maximum})"
        elif minimum is not None:
            return f"(Float {minimum} ..)"
        elif maximum is not None:
            return f"(Float .. {maximum})"
        else:
            return "Float"

    def _convert_enum(self, schema: dict, name: str) -> str:
        """Convert enum schema"""
        values = schema.get("enum", [])

        if all(isinstance(v, str) for v in values):
            enum_vals = ' '.join(self._to_field_name(v) for v in values)
            definition = f"(enum {enum_vals})"
            self.types.append(SlopType(name, definition))
            return name
        else:
            # Mixed types - use union
            return "Any"

    def _convert_union(self, schema: dict, name: str) -> str:
        """Convert oneOf/anyOf to union"""
        variants = schema.get("oneOf") or schema.get("anyOf", [])

        if len(variants) == 2:
            # Check for nullable pattern
            types = [v.get("type") for v in variants]
            if "null" in types:
                non_null = [v for v in variants if v.get("type") != "null"][0]
                inner = self._convert_schema(non_null, f"{name}Value")
                return f"(Option {inner})"

        # General union
        union_variants = []
        for i, variant in enumerate(variants):
            variant_name = f"{name}V{i}"
            variant_type = self._convert_schema(variant, variant_name)
            tag = f"v{i}"
            union_variants.append(f"({tag} {variant_type})")

        definition = "(union\n    " + "\n    ".join(union_variants) + ")"
        self.types.append(SlopType(name, definition))
        return name

    def _to_type_name(self, s: str) -> str:
        """Convert string to PascalCase type name"""
        words = re.split(r'[-_\s]+', s)
        return ''.join(w.capitalize() for w in words)

    def _to_field_name(self, s: str) -> str:
        """Convert string to kebab-case field name"""
        s = re.sub(r'([a-z])([A-Z])', r'\1-\2', s)
        return s.lower().replace('_', '-').replace(' ', '-')


class SqlSchemaConverter:
    """Convert SQL DDL to SLOP types"""

    def convert(self, sql: str) -> str:
        """Convert SQL CREATE TABLE statements to SLOP types"""
        types = []

        # Find CREATE TABLE statements
        pattern = r'CREATE\s+TABLE\s+(\w+)\s*\((.*?)\);'
        matches = re.findall(pattern, sql, re.IGNORECASE | re.DOTALL)

        for table_name, columns_str in matches:
            type_name = self._to_type_name(table_name)
            fields = self._parse_columns(columns_str)

            field_strs = [f"({f['name']} {f['type']})" for f in fields]
            definition = "(record\n    " + "\n    ".join(field_strs) + ")"

            types.append(SlopType(type_name, definition, f"From table: {table_name}"))

        lines = [";; Generated from SQL DDL", ""]
        for t in types:
            lines.append(t.to_slop())
            lines.append("")

        return '\n'.join(lines)

    def _parse_columns(self, columns_str: str) -> List[dict]:
        """Parse column definitions"""
        fields = []

        # Split by comma, but not within parentheses
        depth = 0
        current = ""
        parts = []

        for char in columns_str:
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
            elif char == ',' and depth == 0:
                parts.append(current.strip())
                current = ""
                continue
            current += char
        if current.strip():
            parts.append(current.strip())

        for part in parts:
            # Skip constraints
            if any(kw in part.upper() for kw in ['PRIMARY KEY', 'FOREIGN KEY', 'UNIQUE', 'CHECK', 'INDEX']):
                continue

            tokens = part.split()
            if len(tokens) < 2:
                continue

            col_name = tokens[0].strip('`"[]')
            col_type = tokens[1].upper()

            is_nullable = 'NOT NULL' not in part.upper()

            slop_type = self._sql_type_to_slop(col_type, part)

            if is_nullable:
                slop_type = f"(Option {slop_type})"

            fields.append({
                'name': self._to_field_name(col_name),
                'type': slop_type
            })

        return fields

    def _sql_type_to_slop(self, sql_type: str, full_def: str) -> str:
        """Convert SQL type to SLOP type"""
        sql_type = sql_type.upper()

        # Extract length/precision
        length_match = re.search(r'\((\d+)(?:,\s*(\d+))?\)', full_def)
        length = int(length_match.group(1)) if length_match else None

        if sql_type.startswith('VARCHAR') or sql_type.startswith('CHAR'):
            if length:
                return f"(String .. {length})"
            return "String"
        elif sql_type in ('TEXT', 'CLOB'):
            return "String"
        elif sql_type in ('INT', 'INTEGER'):
            return "Int"
        elif sql_type == 'BIGINT':
            return "I64"
        elif sql_type == 'SMALLINT':
            return "I16"
        elif sql_type == 'TINYINT':
            return "I8"
        elif sql_type in ('FLOAT', 'REAL'):
            return "F32"
        elif sql_type in ('DOUBLE', 'DECIMAL', 'NUMERIC'):
            return "Float"
        elif sql_type in ('BOOLEAN', 'BOOL'):
            return "Bool"
        elif sql_type in ('BLOB', 'BYTEA', 'BINARY', 'VARBINARY'):
            if length:
                return f"(Bytes .. {length})"
            return "Bytes"
        elif sql_type in ('DATE',):
            return "Date"
        elif sql_type in ('DATETIME', 'TIMESTAMP'):
            return "DateTime"
        elif sql_type == 'UUID':
            return "(String 36 .. 36)"
        else:
            return "Any"

    def _to_type_name(self, s: str) -> str:
        """Convert to PascalCase"""
        words = re.split(r'[-_\s]+', s)
        return ''.join(w.capitalize() for w in words)

    def _to_field_name(self, s: str) -> str:
        """Convert to kebab-case"""
        s = re.sub(r'([a-z])([A-Z])', r'\1-\2', s)
        return s.lower().replace('_', '-')


def convert_json_schema(schema_path: str) -> str:
    """Convert JSON Schema file to SLOP"""
    with open(schema_path) as f:
        schema = json.load(f)

    name = schema.get("title", "Root")
    return JsonSchemaConverter().convert(schema, name)


def convert_sql(sql_path: str) -> str:
    """Convert SQL DDL file to SLOP"""
    with open(sql_path) as f:
        sql = f.read()

    return SqlSchemaConverter().convert(sql)


if __name__ == '__main__':
    # Test JSON Schema conversion
    test_schema = {
        "title": "User",
        "type": "object",
        "properties": {
            "id": {"type": "integer", "minimum": 1},
            "name": {"type": "string", "minLength": 1, "maxLength": 100},
            "email": {"type": "string", "format": "email"},
            "age": {"type": "integer", "minimum": 0, "maximum": 150},
            "status": {"type": "string", "enum": ["active", "inactive", "deleted"]}
        },
        "required": ["id", "name", "email"]
    }

    print("=== JSON Schema → SLOP ===")
    print(JsonSchemaConverter().convert(test_schema, "User"))

    # Test SQL conversion
    test_sql = """
    CREATE TABLE users (
        id INTEGER PRIMARY KEY NOT NULL,
        name VARCHAR(100) NOT NULL,
        email VARCHAR(255) NOT NULL,
        age INTEGER,
        created_at TIMESTAMP NOT NULL
    );
    """

    print("\n=== SQL DDL → SLOP ===")
    print(SqlSchemaConverter().convert(test_sql))
