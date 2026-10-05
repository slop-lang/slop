"""
SLOP Parser - S-expression parser for SLOP language

Intentionally simple - S-expressions are trivially parseable.
"""

from dataclasses import dataclass, field
from typing import NamedTuple, Union, List, Optional, Any, Tuple
import math
import re


# AST Node Types
#
# Every node carries its source span as character offsets: start is the
# offset of its first character, end is one past its last. The spans, the
# raw token text of strings and numbers, and infix_source (the exact {...}
# text a contract was written in, on the node that infix produced) are
# compare=False, so two trees are equal whatever text they were parsed from.
# Nodes built in code rather than parsed have them all None.

def _span(**kw):
    return field(default=None, compare=False, repr=False, **kw)


@dataclass
class Symbol:
    name: str
    line: int = 0
    col: int = 0
    resolved_type: Optional[Any] = None  # Set by type checker
    start: Optional[int] = _span()
    end: Optional[int] = _span()
    infix_source: Optional[str] = _span()
    def __repr__(self): return self.name

@dataclass
class String:
    value: str
    line: int = 0
    col: int = 0
    resolved_type: Optional[Any] = None  # Set by type checker
    start: Optional[int] = _span()
    end: Optional[int] = _span()
    infix_source: Optional[str] = _span()
    # The text between the quotes as written, escapes and all
    raw: Optional[str] = _span()
    def __repr__(self):
        if self.raw is not None and _unescape_string(self.raw) == self.value:
            return f'"{self.raw}"'
        return f'"{_escape_string(self.value)}"'

@dataclass
class Number:
    value: Union[int, float]
    line: int = 0
    col: int = 0
    resolved_type: Optional[Any] = None  # Set by type checker
    start: Optional[int] = _span()
    end: Optional[int] = _span()
    infix_source: Optional[str] = _span()
    # The literal as written: 1e+307 stays 1e+307, not 1e+307's float repr
    raw: Optional[str] = _span()
    def __repr__(self):
        if isinstance(self.value, float) and not math.isfinite(self.value):
            # A float literal that overflows (1e400) would print as inf,
            # which reads back as a symbol
            what = self.raw if self.raw is not None else repr(self.value)
            raise ValueError(f"float literal {what} is out of range")
        if self.raw is not None:
            return self.raw
        return repr(self.value)

@dataclass
class SList:
    items: List['SExpr']
    line: int = 0
    col: int = 0
    resolved_type: Optional[Any] = None  # Set by type checker
    start: Optional[int] = _span()
    end: Optional[int] = _span()
    infix_source: Optional[str] = _span()

    def __repr__(self):
        return f"({' '.join(repr(x) for x in self.items)})"

    def __getitem__(self, idx): return self.items[idx]
    def __len__(self): return len(self.items)
    def __iter__(self): return iter(self.items)

SExpr = Union[Symbol, String, Number, SList]


class Token(NamedTuple):
    kind: str
    value: str
    line: int
    col: int
    start: int
    end: int


class Comment(NamedTuple):
    """A ; comment: text runs from the ; to the end of the line, without
    the line ending. start/end are character offsets into the source."""
    text: str
    start: int
    end: int
    line: int
    col: int


def _copy_span(dst: SExpr, src: SExpr) -> SExpr:
    """Give a rebuilt node the span of the node it replaces."""
    dst.start = src.start
    dst.end = src.end
    dst.infix_source = src.infix_source
    return dst


def _unescape_string(s: str) -> str:
    """Unescape a string value, handling \\, \", \n, \t, \r"""
    result = []
    i = 0
    while i < len(s):
        if s[i] == '\\' and i + 1 < len(s):
            next_char = s[i + 1]
            if next_char == 'n':
                result.append('\n')
            elif next_char == 't':
                result.append('\t')
            elif next_char == 'r':
                result.append('\r')
            elif next_char == '"':
                result.append('"')
            elif next_char == '\\':
                result.append('\\')
            else:
                # Unknown escape, keep as-is
                result.append(s[i])
                result.append(next_char)
            i += 2
        else:
            result.append(s[i])
            i += 1
    return ''.join(result)


def _escape_string(s: str) -> str:
    """Escape a string value for a SLOP literal: the inverse of
    _unescape_string. SLOP has escapes for \\, \", newline, tab and
    carriage return only; any other control character is written as is."""
    return (s.replace('\\', '\\\\').replace('"', '\\"')
             .replace('\n', '\\n').replace('\t', '\\t').replace('\r', '\\r'))


# Contract annotations whose body may use {infix} syntax. The native parser
# accepts infix anywhere; @invariant and @property were missing here, so
# format/doc/fill rejected files the compiler builds (#305).
INFIX_ANNOTATIONS = ('@pre', '@post', '@assume', '@loop-invariant', '@invariant', '@property')


class ParseError(Exception):
    def __init__(self, message: str, line: int = 0, col: int = 0, path: str = ""):
        self.message = message
        self.line = line
        self.col = col
        self.path = path
        if path:
            # The file:line:col: error: form the native tools print
            super().__init__(f"{path}:{line}:{col}: error: {message}")
        else:
            super().__init__(f"Parse error at {line}:{col}: {message}")


class Lexer:
    TOKEN_PATTERNS = [
        ('COMMENT', r';[^\n]*'),
        ('WHITESPACE', r'\s+'),
        ('LPAREN', r'\('),
        ('RPAREN', r'\)'),
        ('LBRACE', r'\{'),
        ('RBRACE', r'\}'),
        ('STRING', r'"(?:[^"\\]|\\.)*"'),
        ('NUMBER', r'-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?'),
        ('QUOTE', r"'"),
        ('SYMBOL', r'[a-zA-Z_@$][a-zA-Z0-9_\-/*<>=!?.]*'),
        ('RANGE', r'\.\.'),
        ('OPERATOR', r'[+\-*/!<>=&|^%?]+|\.'),
        ('COLON', r':'),
    ]

    # A character that may continue a symbol, so may not follow a number
    NUMBER_SUFFIX = re.compile(r'[a-zA-Z0-9_\-/*<>=!?.@$]')

    def __init__(self, source: str):
        self.source = source
        self.pattern = '|'.join(f'(?P<{name}>{pattern})'
                                for name, pattern in self.TOKEN_PATTERNS)
        self.regex = re.compile(self.pattern)
        # Filled by tokenize(): every ; comment, in source order
        self.comments: List[Comment] = []

    def tokenize(self) -> List[Token]:
        tokens = []
        self.comments = []
        line, col = 1, 1
        pos = 0  # Track current position for gap detection

        for match in self.regex.finditer(self.source):
            # Check for gap (unrecognized characters)
            if match.start() > pos:
                bad_char = self.source[pos]
                raise ParseError(f"Unexpected character: '{bad_char}'", line, col)

            kind = match.lastgroup
            value = match.group()

            # 3.14f used to lex as 3.14 and the symbol f, so the suffix
            # silently meant nothing (#100). The native lexer rejects it too.
            if kind == 'NUMBER' and match.end() < len(self.source) \
                    and self.NUMBER_SUFFIX.match(self.source[match.end()]) \
                    and not self.source.startswith('..', match.end()):
                raise ParseError(
                    f"invalid number literal: '{value}' is followed by "
                    f"'{self.source[match.end()]}'; put a space or a delimiter after a number",
                    line, col)

            if kind == 'COMMENT':
                # The pattern stops at \n, so a CRLF file leaves the \r on
                text = value.rstrip('\r')
                self.comments.append(Comment(text, match.start(),
                                             match.start() + len(text), line, col))
            elif kind != 'WHITESPACE':
                tokens.append(Token(kind, value, line, col, match.start(), match.end()))

            newlines = value.count('\n')
            if newlines:
                line += newlines
                col = len(value) - value.rfind('\n')
            else:
                col += len(value)

            pos = match.end()

        # Check for trailing unrecognized content
        if pos < len(self.source):
            bad_char = self.source[pos]
            raise ParseError(f"Unexpected character: '{bad_char}'", line, col)

        return tokens


# Operator precedence for infix expressions (higher = binds tighter)
INFIX_PRECEDENCE = {
    'or': 1,
    'and': 2,
    '==': 3, '!=': 3,
    '<': 4, '<=': 4, '>': 4, '>=': 4,
    '+': 5, '-': 5,
    '*': 6, '/': 6, '%': 6,
}


def _number(tok: Token) -> Number:
    value = tok.value
    n = float(value) if any(c in value for c in '.eE') else int(value)
    return Number(n, tok.line, tok.col, start=tok.start, end=tok.end, raw=value)


def _string(tok: Token) -> String:
    raw = tok.value[1:-1]
    return String(_unescape_string(raw), tok.line, tok.col,
                  start=tok.start, end=tok.end, raw=raw)


def _symbol(tok: Token) -> Symbol:
    return Symbol(tok.value, tok.line, tok.col, start=tok.start, end=tok.end)


class Parser:
    def __init__(self, source: str):
        self.source = source
        lexer = Lexer(source)
        self.tokens = lexer.tokenize()
        self.comments = lexer.comments
        self.pos = 0
        self.in_contract = False  # Track if inside @pre/@post/@assume

    def parse(self) -> List[SExpr]:
        forms = []
        while self.pos < len(self.tokens):
            forms.append(self.parse_expr())
        return forms

    def parse_expr(self) -> SExpr:
        if self.pos >= len(self.tokens):
            raise ParseError("Unexpected end of input")

        tok = self.tokens[self.pos]
        kind, value, line, col = tok.kind, tok.value, tok.line, tok.col

        if kind == 'LBRACE':
            return self.parse_infix_expr()
        elif kind == 'LPAREN':
            return self.parse_list()
        elif kind == 'NUMBER':
            self.pos += 1
            return _number(tok)
        elif kind == 'STRING':
            self.pos += 1
            return _string(tok)
        elif kind == 'QUOTE':
            self.pos += 1
            quoted = self.parse_expr()
            # The quote symbol shares the list's start: that is how the
            # formatter tells 'x from a written-out (quote x)
            return SList([Symbol('quote', line, col, start=tok.start, end=tok.end), quoted],
                         line, col, start=tok.start, end=quoted.end)
        elif kind in ('SYMBOL', 'OPERATOR'):
            self.pos += 1
            return _symbol(tok)
        elif kind == 'COLON':
            self.pos += 1
            if self.pos < len(self.tokens):
                nxt = self.tokens[self.pos]
                self.pos += 1
                return Symbol(':' + nxt.value, line, col, start=tok.start, end=nxt.end)
            raise ParseError("Expected symbol after ':'", line, col)
        elif kind == 'RANGE':
            self.pos += 1
            return Symbol('..', line, col, start=tok.start, end=tok.end)
        else:
            raise ParseError(f"Unexpected token: {value}", line, col)

    def parse_list(self) -> SList:
        open_tok = self.tokens[self.pos]
        line, col = open_tok.line, open_tok.col
        if open_tok.kind != 'LPAREN':
            raise ParseError("Expected '('", line, col)

        self.pos += 1
        items = []

        # Track if this is a contract form for infix support
        is_contract_form = False

        while self.pos < len(self.tokens):
            tok = self.tokens[self.pos]
            kind, value = tok.kind, tok.value
            if kind == 'RPAREN':
                self.pos += 1
                return SList(items, line, col, start=open_tok.start, end=tok.end)

            # Detect contract annotations after parsing first item
            if len(items) == 0 and kind == 'SYMBOL' and value in INFIX_ANNOTATIONS:
                is_contract_form = True

            # Set in_contract context when parsing the argument of a contract
            if is_contract_form and len(items) == 1:
                old_in_contract = self.in_contract
                self.in_contract = True
                try:
                    items.append(self.parse_expr())
                finally:
                    self.in_contract = old_in_contract
            else:
                items.append(self.parse_expr())

        raise ParseError("Unclosed list", line, col)

    def parse_infix_expr(self) -> SExpr:
        """Parse {infix expression} and convert to prefix AST.

        Only allowed inside the contract annotations in INFIX_ANNOTATIONS.
        The node returned spans the braces and keeps their exact text in
        infix_source, so the formatter can write the contract as written.
        """
        lbrace = self.tokens[self.pos]
        line, col = lbrace.line, lbrace.col

        if not self.in_contract:
            raise ParseError(
                "Infix syntax {expr} is only allowed inside @pre, @post, @assume, @loop-invariant, @invariant or @property",
                line, col
            )

        self.pos += 1  # consume LBRACE

        if self.pos >= len(self.tokens):
            raise ParseError("Unexpected end of input in infix expression", line, col)

        # Check for empty braces
        if self.tokens[self.pos].kind == 'RBRACE':
            raise ParseError("Empty infix expression", line, col)

        ast = self._parse_infix_precedence(0)

        # Expect RBRACE
        if self.pos >= len(self.tokens):
            raise ParseError("Expected '}' to close infix expression", line, col)
        rbrace = self.tokens[self.pos]
        if rbrace.kind != 'RBRACE':
            raise ParseError(f"Expected '}}', got '{rbrace.value}'", rbrace.line, rbrace.col)
        self.pos += 1

        ast.start = lbrace.start
        ast.end = rbrace.end
        ast.infix_source = self.source[lbrace.start:rbrace.end]
        return ast

    def _parse_infix_precedence(self, min_prec: int) -> SExpr:
        """Precedence climbing algorithm for infix expressions."""
        left = self._parse_infix_atom()

        while True:
            op = self._peek_binary_op()
            if op is None:
                break
            op_prec = INFIX_PRECEDENCE.get(op)
            if op_prec is None or op_prec < min_prec:
                break

            # Consume operator
            op_tok = self.tokens[self.pos]
            self.pos += 1

            # Left associative: use op_prec + 1 for right operand
            right = self._parse_infix_precedence(op_prec + 1)

            # Convert to prefix form: a + b -> (+ a b)
            left = SList([_symbol(op_tok), left, right], left.line, left.col,
                         start=left.start, end=right.end)

        return left

    def _peek_binary_op(self) -> str | None:
        """Peek at current token and return operator name if it's a binary operator."""
        if self.pos >= len(self.tokens):
            return None

        kind, value = self.tokens[self.pos].kind, self.tokens[self.pos].value

        # Check for RBRACE or RPAREN - end of expression
        if kind in ('RBRACE', 'RPAREN'):
            return None

        # 'and' and 'or' are symbols, not operators
        if kind == 'SYMBOL' and value in ('and', 'or'):
            return value

        # Standard operators
        if kind == 'OPERATOR' and value in INFIX_PRECEDENCE:
            return value

        return None

    def _parse_infix_atom(self) -> SExpr:
        """Parse atomic element in infix expression."""
        if self.pos >= len(self.tokens):
            raise ParseError("Unexpected end of input in infix expression")

        tok = self.tokens[self.pos]
        kind, value, line, col = tok.kind, tok.value, tok.line, tok.col

        # Unary 'not'
        if kind == 'SYMBOL' and value == 'not':
            self.pos += 1
            operand = self._parse_infix_atom()
            return SList([_symbol(tok), operand], line, col,
                         start=tok.start, end=operand.end)

        # Unary minus (only at start or after operator, handled by context)
        if kind == 'OPERATOR' and value == '-':
            self.pos += 1
            operand = self._parse_infix_atom()
            # Convert to (- 0 x) for unary negation
            return SList([_symbol(tok), Number(0, line, col), operand], line, col,
                         start=tok.start, end=operand.end)

        # Parenthesized expression - could be grouping OR prefix S-expression
        if kind == 'LPAREN':
            return self._parse_infix_paren()

        # Number
        if kind == 'NUMBER':
            self.pos += 1
            return _number(tok)

        # String
        if kind == 'STRING':
            self.pos += 1
            return _string(tok)

        # Symbol (variable, $result, etc.)
        if kind == 'SYMBOL':
            self.pos += 1
            return _symbol(tok)

        # Quote
        if kind == 'QUOTE':
            self.pos += 1
            quoted = self._parse_infix_atom()
            return SList([Symbol('quote', line, col, start=tok.start, end=tok.end), quoted],
                         line, col, start=tok.start, end=quoted.end)

        raise ParseError(f"Unexpected token in infix expression: {value}", line, col)

    def _parse_infix_paren(self) -> SExpr:
        """Parse parenthesized expression in infix context.

        Distinguishes between:
        - Grouping: (a + b) -> recurse infix
        - Prefix form: (len arr) or (. ptr field) -> parse as S-expression
        """
        line, col = self.tokens[self.pos].line, self.tokens[self.pos].col

        # Look ahead to determine if this is a function call or grouping
        # Save position for potential backtracking
        save_pos = self.pos
        self.pos += 1  # consume LPAREN

        if self.pos >= len(self.tokens):
            raise ParseError("Unexpected end of input after '('", line, col)

        tok = self.tokens[self.pos]
        kind, value = tok.kind, tok.value

        # If first element is a symbol, check if it's followed by an operator
        # If not followed by an operator, it's likely a function call
        if kind == 'SYMBOL':
            # Check next token
            if self.pos + 1 < len(self.tokens):
                nxt = self.tokens[self.pos + 1]
                # If next is RPAREN, it could be (x) grouping or (x) single element
                # If next is not an operator, treat as prefix call
                if nxt.kind == 'RPAREN':
                    # Single element in parens, treat as grouping
                    self.pos += 1  # consume symbol
                    result = _symbol(tok)
                    self.pos += 1  # consume RPAREN
                    return result
                elif nxt.kind not in ('OPERATOR',) and nxt.value not in ('and', 'or'):
                    # This is a function call like (len arr) - parse as prefix
                    self.pos = save_pos
                    # Temporarily exit contract mode to parse the S-expression normally
                    return self.parse_list()

        # Special case: if first element is an operator like '.', '-', '+', etc.
        # These are prefix function calls like (. obj field) or (- 0 n)
        if kind == 'OPERATOR':
            self.pos = save_pos
            return self.parse_list()

        # Otherwise treat as grouping - parse as infix
        expr = self._parse_infix_precedence(0)

        # Expect RPAREN
        if self.pos >= len(self.tokens):
            raise ParseError("Expected ')' in infix grouping", line, col)
        if self.tokens[self.pos].kind != 'RPAREN':
            bad = self.tokens[self.pos]
            raise ParseError(f"Expected ')', got '{bad.value}'", bad.line, bad.col)
        self.pos += 1

        return expr


def _normalize_quotes(expr: SExpr) -> SExpr:
    """Normalize (quote symbol) to 'symbol.

    This handles Lisp-style quote forms, converting them to SLOP's 'symbol syntax.
    Applied post-parse to ensure consistent AST regardless of input style.
    """
    if isinstance(expr, SList) and len(expr) == 2:
        if isinstance(expr[0], Symbol) and expr[0].name == 'quote':
            inner = expr[1]
            if isinstance(inner, Symbol):
                # (quote foo) -> 'foo
                return _copy_span(Symbol(f"'{inner.name}", expr.line, expr.col), expr)
    # Recursively normalize children
    if isinstance(expr, SList):
        normalized = [_normalize_quotes(item) for item in expr.items]
        return _copy_span(SList(normalized, expr.line, expr.col), expr)
    return expr


def _normalize_bare_forms(ast: List[SExpr]) -> List[SExpr]:
    """Normalize bare record/enum forms to wrapped (type Name ...) form.

    Converts:
        (record Name (field Type) ...) → (type Name (record (field Type) ...))
        (enum Name variant ...)        → (type Name (enum variant ...))

    This allows the transpiler to handle a single form instead of both.
    The rebuilt lists take the span of the form they replace.
    """
    result = []
    for form in ast:
        if is_form(form, 'record') and len(form) >= 2 and isinstance(form[1], Symbol):
            # (record Name fields...) → (type Name (record fields...))
            name = form[1]
            record_body = _copy_span(SList([Symbol('record')] + list(form.items[2:]), form.line), form)
            wrapped = _copy_span(SList([Symbol('type'), name, record_body], form.line), form)
            result.append(wrapped)
        elif is_form(form, 'enum') and len(form) >= 2 and isinstance(form[1], Symbol):
            # (enum Name variants...) → (type Name (enum variants...))
            name = form[1]
            enum_body = _copy_span(SList([Symbol('enum')] + list(form.items[2:]), form.line), form)
            wrapped = _copy_span(SList([Symbol('type'), name, enum_body], form.line), form)
            result.append(wrapped)
        elif is_form(form, 'module'):
            # Recursively normalize inside module
            # Keep module keyword and name, normalize the rest
            normalized_items = list(form.items[:2])  # 'module' and name
            normalized_items.extend(_normalize_bare_forms(list(form.items[2:])))
            result.append(_copy_span(SList(normalized_items, form.line), form))
        else:
            result.append(form)
    return result


def parse_with_comments(source: str) -> Tuple[List[SExpr], List[Comment]]:
    """Parse source, returning its forms and its ; comments in source order.

    The forms are what parse() returns; every parsed node carries its
    start/end offsets into source.
    """
    parser = Parser(source)
    forms = parser.parse()
    forms = [_normalize_quotes(form) for form in forms]
    forms = _normalize_bare_forms(forms)
    return forms, parser.comments


def parse(source: str) -> List[SExpr]:
    return parse_with_comments(source)[0]


def read_source(path) -> str:
    """Read a SLOP file as written: newline='' keeps a \\r in a string
    literal (and CRLF line endings) instead of translating them to \\n."""
    with open(path, newline='') as f:
        return f.read()


def parse_file(path: str) -> List[SExpr]:
    source = read_source(path)
    try:
        return parse(source)
    except ParseError as e:
        if e.path:
            raise
        raise ParseError(e.message, e.line, e.col, str(path)) from None


# AST utilities

def is_form(expr: SExpr, keyword: str) -> bool:
    return (isinstance(expr, SList) and
            len(expr) > 0 and
            isinstance(expr[0], Symbol) and
            expr[0].name == keyword)

def get_forms(ast: List[SExpr], keyword: str) -> List[SList]:
    return [e for e in ast if is_form(e, keyword)]

def get_imports(ast: List[SExpr]) -> List[SList]:
    """Get all import declarations from AST.

    Import form: (import module-name name*)
    """
    return get_forms(ast, 'import')

def get_exports(ast: List[SExpr]) -> List[SList]:
    """Get all export declarations from AST.

    Export form: (export name*)
    """
    return get_forms(ast, 'export')

@dataclass
class ImportSpec:
    """Parsed import specification."""
    module_name: str
    symbols: List[str]
    line: int = 0
    col: int = 0

def parse_import(form: SList) -> ImportSpec:
    """Parse an import form into ImportSpec.

    (import module-name sym1 sym2 ...)
    (import module-name (sym1 sym2 ...))  -- grouped in list
    """
    if len(form) < 2:
        raise ParseError("import requires module name", form.line, form.col)

    module_name = form[1].name if isinstance(form[1], Symbol) else str(form[1])
    symbols = []

    for item in form.items[2:]:
        if isinstance(item, Symbol):
            symbols.append(item.name)
        elif isinstance(item, SList):
            # Grouped list of symbols: (sym1 sym2 ...)
            for sub_item in item.items:
                if isinstance(sub_item, Symbol):
                    symbols.append(sub_item.name)

    return ImportSpec(module_name, symbols, form.line, form.col)

@dataclass
class ExportSpec:
    """Parsed export specification."""
    symbols: List[str]
    line: int = 0
    col: int = 0

def parse_export(form: SList) -> ExportSpec:
    """Parse an export form into ExportSpec.

    (export sym1 sym2 ...)
    """
    symbols = []

    for item in form.items[1:]:
        if isinstance(item, Symbol):
            symbols.append(item.name)

    return ExportSpec(symbols, form.line, form.col)

def find_all(expr: SExpr, predicate) -> List[SExpr]:
    results = []
    def walk(e):
        if predicate(e):
            results.append(e)
        if isinstance(e, SList):
            for item in e.items:
                walk(item)
    walk(expr)
    return results

def find_holes(expr: SExpr) -> List[SList]:
    return find_all(expr, lambda e: is_form(e, 'hole'))


# Pretty printing

def pretty_print(expr: SExpr, indent: int = 0) -> str:
    if isinstance(expr, SList):
        if len(expr) == 0:
            return "()"

        simple = all(not isinstance(x, SList) for x in expr.items)
        if simple and len(str(expr)) < 60:
            return str(expr)

        prefix = "  " * indent
        lines = [f"({expr[0]}"]
        for item in expr.items[1:]:
            lines.append(pretty_print(item, indent + 1))

        result = lines[0]
        for line in lines[1:]:
            result += f"\n{prefix}  {line}"
        result += ")"
        return result

    return str(expr)


if __name__ == '__main__':
    test = '''
    (module example
      (export (foo 1))
      (type Age (Int 0 .. 150))
      (fn greet ((name String))
        (@intent "Say hello")
        (@spec ((String) -> String))
        (concat "Hello, " name)))
    '''
    for form in parse(test):
        print(pretty_print(form))
