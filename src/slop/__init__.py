"""
SLOP - Symbolic LLM-Optimized Programming

A language designed for hybrid human-machine code generation where:
- Humans specify intent via contracts and types
- Machines generate implementation
- Machines verify correctness
- Machines compile to efficient native code via C
"""

__version__ = "0.4.3"

import sys

# Say so plainly, rather than fail on the first newer syntax the import meets
if sys.version_info < (3, 11):
    sys.exit(f"slop needs Python 3.11 or newer; {sys.executable} is "
             f"Python {sys.version.split()[0]}")

from slop.parser import parse, parse_file
from slop.hole_filler import check_hole_impl, CheckResult
# Re-export type classes and constants from types module for backwards compatibility
from slop.types import (
    Type, PrimitiveType, RangeType, ListType, ArrayType, MapType,
    RecordType, EnumType, UnionType, OptionType, ResultType, PtrType,
    FnType, TypeVar, UnknownType, UNKNOWN,
    STRING, INT, BOOL, UNIT, ARENA, BUILTIN_FUNCTIONS,
    RangeBounds, Constraint,
)
