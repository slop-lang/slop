"""
SLOP - Symbolic LLM-Optimized Programming

A language designed for hybrid human-machine code generation where:
- Humans specify intent via contracts and types
- Machines generate implementation
- Machines verify correctness
- Machines compile to efficient native code via C
"""

__version__ = "0.1.0"

from slop.parser import parse, parse_file
from slop.transpiler import transpile
from slop.type_checker import TypeChecker, check_file, check_source
