"""
SLOP Code Formatter - Idiomatic formatting for SLOP source.

Formats SLOP code with proper indentation and line wrapping based on
the semantic structure of the language.

Comments are kept. Each ; comment is attached by its source offsets to a
node: a comment on the line a node ends on trails that node, any other
comment leads the next node in the same list, and a comment after a list's
last child is left dangling before the list's ')'. A list that holds a
comment anywhere inside it is never put on one line. Infix contracts
({x > 0}) are written exactly as they were.

format_source re-parses what it produces and refuses (FormatError) if the
forms or the comments differ from the input, so a formatter bug cannot
silently change a program.
"""

import math
import re
from collections import Counter
from contextlib import contextmanager
from typing import Dict, List, Optional

from slop.parser import (SExpr, SList, Symbol, String, Number, Comment,
                         parse_with_comments, read_source, is_form)

# Max line length before wrapping
MAX_LINE = 80

# Indent size
INDENT = 2


class FormatError(ValueError):
    """The formatter cannot produce output equivalent to its input."""


def format_source(source: str) -> str:
    """Format SLOP source code.

    Args:
        source: Raw SLOP source code

    Returns:
        Formatted source code, ending in a newline. A file whose lines end
        in CRLF keeps CRLF.

    Raises:
        ParseError: the source does not parse
        FormatError: the source cannot be formatted without changing it,
            such as a float literal out of range (1e400)
    """
    forms, comments = parse_with_comments(source)
    ctx = _Context(source, forms, comments)
    with _using(ctx):
        try:
            text = _format_top(forms)
        except ValueError as e:
            # Number.__repr__ refuses a float literal that overflowed
            raise FormatError(str(e)) from None
    if not text:
        return ''
    text += '\n'
    _verify(forms, comments, text)
    if _uses_crlf(source):
        text = re.sub(r'(?<!\r)\n', '\r\n', text)
    return text


def format_file(path: str) -> str:
    """Format a SLOP file.

    Args:
        path: Path to SLOP file

    Returns:
        Formatted source code
    """
    return format_source(read_source(path))


def _uses_crlf(source: str) -> bool:
    crlf = source.count('\r\n')
    return crlf > 0 and crlf == source.count('\n')


# =============================================================================
# Comment attachment
# =============================================================================

_TOP = 'top'


class _Context:
    """Where each comment of a source goes, keyed by id() of AST nodes."""

    def __init__(self, source: str = '', forms=(), comments=()):
        self.source = source
        self.leading: Dict[int, List[Comment]] = {}
        self.trailing: Dict[int, Comment] = {}
        self.dangling: Dict[object, List[Comment]] = {}
        # ids of lists that must not be put on one line
        self.breaks = set()
        if comments:
            self._attach(list(forms), list(comments), _TOP)
        if source:
            for form in forms:
                self._mark_breaks(form)

    def _attach(self, children: List[SExpr], comments: List[Comment], owner) -> None:
        """Attach comments that lie inside owner (a list, or the file) to
        owner's children, or leave them dangling on owner."""
        src = self.source
        spanned = [ch for ch in children if ch.start is not None]
        inner: Dict[int, List[Comment]] = {}
        by_id = {}
        for c in comments:
            container = next((ch for ch in spanned if ch.start <= c.start < ch.end), None)
            if container is not None:
                if container.infix_source is not None:
                    # Part of the {...} text, which is written as is
                    continue
                if isinstance(container, SList):
                    inner.setdefault(id(container), []).append(c)
                    by_id[id(container)] = container
                else:
                    # Inside an atom (between ':' and its name): before it
                    self.leading.setdefault(id(container), []).append(c)
                continue
            before = [ch for ch in spanned if ch.end <= c.start]
            prev = max(before, key=lambda ch: ch.end) if before else None
            if prev is not None and '\n' not in src[prev.end:c.start] \
                    and id(prev) not in self.trailing:
                self.trailing[id(prev)] = c
                continue
            after = [ch for ch in spanned if ch.start >= c.end]
            if after:
                nxt = min(after, key=lambda ch: ch.start)
                self.leading.setdefault(id(nxt), []).append(c)
            else:
                self.dangling.setdefault(owner, []).append(c)
        for key, cs in inner.items():
            lst = by_id[key]
            self._attach(lst.items, cs, key)

    def _mark_breaks(self, node: SExpr) -> bool:
        """Record the lists that cannot go on one line; return whether node
        forces its parent onto several lines."""
        if node.infix_source is not None:
            return '\n' in node.infix_source
        if not isinstance(node, SList):
            return False
        broken = id(node) in self.dangling
        for child in node.items:
            if self._mark_breaks(child):
                broken = True
            if id(child) in self.leading or id(child) in self.trailing:
                broken = True
        if broken:
            self.breaks.add(id(node))
        return broken

    def blank_before(self, offset: Optional[int]) -> bool:
        """Whether a blank line separates offset from the text before it."""
        if offset is None:
            return False
        src = self.source
        i = offset - 1
        newlines = 0
        while i >= 0 and src[i] in ' \t\r\n':
            if src[i] == '\n':
                newlines += 1
            i -= 1
        return i >= 0 and newlines >= 2


_CTX = _Context()


@contextmanager
def _using(ctx: _Context):
    global _CTX
    saved = _CTX
    _CTX = ctx
    try:
        yield
    finally:
        _CTX = saved


def _emit_leading(lines: List[str], node: SExpr, prefix: str) -> None:
    """Append node's leading comments, keeping a blank line where the
    source had one (never two in a row)."""
    cs = _CTX.leading.get(id(node))
    if not cs:
        return
    for c in cs:
        if _CTX.blank_before(c.start) and lines and lines[-1] != '':
            lines.append('')
        lines.append(prefix + c.text)
    if _CTX.blank_before(node.start):
        lines.append('')


def _emit_dangling(lines: List[str], key, prefix: str) -> bool:
    cs = _CTX.dangling.get(key)
    if not cs:
        return False
    for c in cs:
        if _CTX.blank_before(c.start) and lines and lines[-1] != '':
            lines.append('')
        lines.append(prefix + c.text)
    return True


def _emit_node(lines: List[str], node: SExpr, prefix: str, text: str) -> bool:
    """Append prefix + text (which may span lines) and node's trailing
    comment; return whether the last line now ends in a comment."""
    text_lines = (prefix + text).split('\n')
    tc = _CTX.trailing.get(id(node))
    if tc is not None:
        text_lines[-1] += ' ' + tc.text
    lines.extend(text_lines)
    return tc is not None


def _format_top(forms: List[SExpr]) -> str:
    lines: List[str] = []
    for i, form in enumerate(forms):
        if i > 0:
            lines.append('')
        _emit_leading(lines, form, '')
        _emit_node(lines, form, '', format_expr(form, 0))
    _emit_dangling(lines, _TOP, '')
    while lines and lines[-1] == '':
        lines.pop()
    return '\n'.join(lines)


# =============================================================================
# Verification
# =============================================================================

def _canon(expr: SExpr):
    """A comparable rendering of expr, ignoring layout, in the order the
    formatter writes forms (module imports/exports first, fn annotations
    before the body)."""
    if isinstance(expr, Symbol):
        return ('S', expr.name)
    if isinstance(expr, String):
        return ('T', expr.value)
    if isinstance(expr, Number):
        return ('N', type(expr.value).__name__, expr.value)
    items = list(expr.items)
    if is_form(expr, 'module') and len(items) >= 2:
        rest = items[2:]
        items = (items[:2]
                 + [x for x in rest if is_form(x, 'export') or is_form(x, 'import')]
                 + [x for x in rest if not (is_form(x, 'export') or is_form(x, 'import'))])
    elif (is_form(expr, 'fn') or is_form(expr, 'impl')) and len(items) >= 3:
        rest = items[3:]
        items = (items[:3]
                 + [x for x in rest if _is_annotation(x)]
                 + [x for x in rest if not _is_annotation(x)])
    return ('L', tuple(_canon(x) for x in items))


def _verify(forms: List[SExpr], comments: List[Comment], text: str) -> None:
    try:
        new_forms, new_comments = parse_with_comments(text)
    except Exception as e:
        raise FormatError(f"formatter produced code that does not parse ({e}); "
                          "refusing to format this file") from None
    if [_canon(f) for f in forms] != [_canon(f) for f in new_forms]:
        raise FormatError("formatter would change the code; refusing to format this file")
    if Counter(c.text for c in comments) != Counter(c.text for c in new_comments):
        raise FormatError("formatter would lose or duplicate a comment; "
                          "refusing to format this file")


# =============================================================================
# Rendering
# =============================================================================

def _is_quote_sugar(expr: SExpr) -> bool:
    """A list that was written 'x (rather than (quote x))."""
    return (isinstance(expr, SList) and len(expr) == 2
            and isinstance(expr[0], Symbol) and expr[0].name == 'quote'
            and expr.start is not None and expr[0].start == expr.start)


def _is_annotation(item: SExpr) -> bool:
    return (isinstance(item, SList) and len(item) > 0
            and isinstance(item[0], Symbol) and item[0].name.startswith('@'))


def inline(expr: SExpr) -> str:
    """Render expression on a single line."""
    if expr.infix_source is not None:
        return expr.infix_source
    if isinstance(expr, SList):
        if len(expr) == 0:
            return "()"
        if _is_quote_sugar(expr):
            return "'" + inline(expr[1])
        parts = [inline(item) for item in expr.items]
        return "(" + " ".join(parts) + ")"
    return str(expr)


def fits_inline(expr: SExpr, max_len: int = MAX_LINE) -> bool:
    """Check if expression fits on one line."""
    if id(expr) in _CTX.breaks:
        return False
    return len(inline(expr)) <= max_len


def format_expr(expr: SExpr, indent: int) -> str:
    """Format a single expression."""
    if isinstance(expr, SList) and expr.infix_source is None:
        return format_list(expr, indent)
    return inline(expr)


def format_list(expr: SList, indent: int) -> str:
    """Format an SList based on its head form."""
    if expr.infix_source is not None:
        return expr.infix_source
    if len(expr) == 0:
        if _CTX.dangling.get(id(expr)):
            return _format_broken(expr, indent, 0)
        return "()"

    head = expr[0].name if isinstance(expr[0], Symbol) else ""

    if _is_quote_sugar(expr):
        quote_sym, quoted = expr.items
        if not any(id(x) in _CTX.leading or id(x) in _CTX.trailing for x in expr.items) \
                and id(expr) not in _CTX.dangling:
            return "'" + format_expr(quoted, indent)

    if id(expr) in _CTX.breaks:
        return _format_with_comments(expr, head, indent)

    # Dispatch to specialized formatters
    formatters = {
        'module': format_module,
        'fn': format_fn,
        'impl': format_fn,
        'type': format_type,
        'const': format_const,
        'let': format_let,
        'let*': format_let,
        'if': format_if,
        'when': format_when,
        'cond': format_cond,
        'match': format_match,
        'do': format_do,
        'ffi': format_ffi,
        'ffi-struct': format_ffi_struct,
        'import': format_import,
        'export': format_export,
        'hole': format_hole,
        'with-arena': format_with_arena,
        'while': format_while,
        'for': format_for,
        'for-each': format_for_each,
    }

    # Annotations stay inline if short
    if head.startswith('@'):
        return format_annotation(expr, indent)

    formatter = formatters.get(head, format_generic)
    return formatter(expr, indent)


def pad(indent: int) -> str:
    """Create indentation padding."""
    return " " * (indent * INDENT)


# =============================================================================
# Lists that hold comments
# =============================================================================

# How many items after the head stay on a commented list's first line
_HEAD_ITEMS = {
    'fn': 2, 'impl': 2, 'type': 2, 'const': 3, 'ffi-struct': 2,
    'if': 1, 'when': 1, 'while': 1, 'for': 1, 'for-each': 1, 'match': 1,
    'with-arena': 1, 'hole': 1, 'ffi': 1, 'import': 1,
    'let': 1, 'let*': 1,
}


def _is_keyword(item: SExpr) -> bool:
    return isinstance(item, Symbol) and item.name.startswith(':') and len(item.name) > 1


def _format_with_comments(expr: SList, head: str, indent: int) -> str:
    if head == 'module':
        return format_module(expr, indent)
    if head in ('let', 'let*'):
        return _format_let_with_comments(expr, head, indent)
    if head.startswith('@'):
        return _format_broken(expr, indent, 1)
    head_n = _HEAD_ITEMS.get(head, 0)
    if head == 'with-arena' and len(expr) > 1 and isinstance(expr[1], Symbol) \
            and expr[1].name == ':as':
        head_n = 3
    return _format_broken(expr, indent, head_n)


def _same_line_atoms(a: SExpr, b: SExpr) -> bool:
    """b is an atom with no comment before it, on the line a ends on."""
    return (not isinstance(b, SList) and b.infix_source is None
            and not _is_keyword(b)  # a keyword starts its own line
            and a.end is not None and b.start is not None and a.end <= b.start
            and not _CTX.leading.get(id(b))
            and '\n' not in _CTX.source[a.end:b.start])


def _format_broken(expr: SList, indent: int, head_n: int,
                   cont: Optional[str] = None, close: Optional[str] = None,
                   head_text=None) -> str:
    """Lay out a list that holds comments: the head and up to head_n items
    on the first line, then one item (or :keyword value pair) per line at
    cont (default: one indent deeper). A comment ends the first line early.
    If the last line ends in a comment, ')' goes on a line of its own at
    close (default: the list's indent)."""
    p = cont if cont is not None else pad(indent + 1)
    child_indent = len(p) // INDENT
    close = close if close is not None else pad(indent)
    items = expr.items

    first = "("
    k = 0
    ended = False
    for i in range(min(head_n + 1, len(items))):
        item = items[i]
        if _CTX.leading.get(id(item)):
            break
        if head_text is not None and head_text(i) is not None:
            text = head_text(i)
        else:
            text = format_expr(item, indent + 1)
        first += ("" if i == 0 else " ") + text
        k = i + 1
        tc = _CTX.trailing.get(id(item))
        if tc is not None:
            first += " " + tc.text
            ended = True
            break
    lines = first.split('\n')
    last_comment = ended

    i = k
    while i < len(items):
        item = items[i]
        _emit_leading(lines, item, p)
        text = format_expr(item, child_indent)
        node = item
        # Keep :keyword value together when nothing comes between them
        if _is_keyword(item) and id(item) not in _CTX.trailing and i + 1 < len(items) \
                and not _is_keyword(items[i + 1]) and not _CTX.leading.get(id(items[i + 1])):
            node = items[i + 1]
            text += " " + format_expr(node, child_indent)
            i += 1
        # Keep a run of atoms that shared a source line (a group of
        # exported names, say) on one line
        while not isinstance(node, SList) and id(node) not in _CTX.trailing \
                and i + 1 < len(items) and _same_line_atoms(node, items[i + 1]):
            node = items[i + 1]
            text += " " + inline(node)
            i += 1
        last_comment = _emit_node(lines, node, p, text)
        i += 1

    if _emit_dangling(lines, id(expr), p):
        last_comment = True
    if last_comment:
        lines.append(close + ")")
    else:
        lines[-1] += ")"
    return '\n'.join(lines)


def _format_let_with_comments(expr: SList, head: str, indent: int) -> str:
    """let with comments: bindings stay aligned under the first one."""
    bindings = expr[1] if len(expr) > 1 else None
    if isinstance(bindings, SList) and len(bindings) > 0 \
            and bindings.infix_source is None and not _is_quote_sugar(bindings):
        col = indent * INDENT + len(head) + 3  # after "(let ("
        text = _format_broken(bindings, col // INDENT - 1, 0,
                              cont=" " * col, close=" " * (col - 1))
        return _format_broken(expr, indent, 1,
                              head_text=lambda i: text if i == 1 else None)
    return _format_broken(expr, indent, 1)


# =============================================================================
# Specialized Formatters
# =============================================================================

def format_module(expr: SList, indent: int) -> str:
    """Format module: (module name (export ...) (import ...) body...)

    Exports and imports move to the top, each with its comments."""
    if len(expr) < 2:
        if id(expr) in _CTX.breaks:
            return _format_broken(expr, indent, 1)
        return inline(expr)
    keyword, name = expr[0], expr[1]
    if _CTX.leading.get(id(keyword)) or _CTX.trailing.get(id(keyword)) \
            or _CTX.leading.get(id(name)):
        return _format_broken(expr, indent, 1)

    first = f"(module {format_expr(name, indent + 1)}"
    tc = _CTX.trailing.get(id(name))
    if tc is not None:
        first += " " + tc.text
    lines = [first]
    last_comment = tc is not None
    p = pad(indent + 1)

    # Separate exports/imports from body
    exports_imports = []
    body = []

    for item in expr.items[2:]:
        if is_form(item, 'export') or is_form(item, 'import'):
            exports_imports.append(item)
        else:
            body.append(item)

    # Format exports/imports
    for item in exports_imports:
        _emit_leading(lines, item, p)
        last_comment = _emit_node(lines, item, p, format_expr(item, indent + 1))

    # Format body with blank lines between top-level forms, and before
    # the body if we have both sections
    for i, item in enumerate(body):
        if i > 0 or exports_imports:
            lines.append("")
        _emit_leading(lines, item, p)
        last_comment = _emit_node(lines, item, p, format_expr(item, indent + 1))

    if _emit_dangling(lines, id(expr), p):
        last_comment = True
    if last_comment:
        lines.append(pad(indent) + ")")
    else:
        lines[-1] += ")"
    return '\n'.join(lines)


def format_fn(expr: SList, indent: int) -> str:
    """Format function: (fn name ((param Type) ...) @annotations... body)

    Also impl, which has the same shape."""
    if len(expr) < 3:
        return inline(expr)

    keyword = expr[0]
    name = expr[1]
    params = expr[2]
    rest = expr.items[3:]

    # Build first line: (fn name params
    params_str = inline(params)
    first_line = f"({keyword} {inline(name)} {params_str}"

    p = pad(indent + 1)
    lines = [first_line]

    # Separate annotations from body
    annotations = [item for item in rest if _is_annotation(item)]
    body = [item for item in rest if not _is_annotation(item)]

    # Format annotations
    for ann in annotations:
        lines.append(p + format_annotation(ann, indent + 1))

    # Format body
    for item in body:
        lines.append(p + format_expr(item, indent + 1))

    lines[-1] += ")"
    return '\n'.join(lines)


def format_annotation(expr: SList, indent: int) -> str:
    """Format annotation: (@intent "..."), (@spec ...), etc."""
    if id(expr) in _CTX.breaks:
        return _format_broken(expr, indent, 1)
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    # Multi-line annotation
    head = expr[0]
    p = pad(indent + 1)
    lines = [f"({head}"]
    for item in expr.items[1:]:
        lines.append(p + format_expr(item, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_type(expr: SList, indent: int) -> str:
    """Format type definition: (type Name definition)"""
    if len(expr) < 3:
        return inline(expr)

    name = expr[1]
    defn = expr[2]

    # Short types stay inline
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    # Check what kind of type definition
    if is_form(defn, 'record') and len(expr) == 3:
        return format_type_record(name, defn, indent)
    else:
        # Enums, range types, etc.
        return inline(expr)


def format_type_record(name, defn: SList, indent: int) -> str:
    """Format record type with fields on separate lines."""
    pf = pad(indent + 2)

    lines = [f"(type {inline(name)} (record"]
    for field in defn.items[1:]:
        lines.append(pf + inline(field))
    lines[-1] += "))"
    return '\n'.join(lines)


def format_const(expr: SList, indent: int) -> str:
    """Format const: (const NAME Type value)"""
    return inline(expr)


def format_let(expr: SList, indent: int) -> str:
    """Format let: (let ((x val) (y val)) body...), and let*"""
    if len(expr) < 3:
        return inline(expr)

    head = expr[0].name
    bindings = expr[1]
    body = expr.items[2:]

    # Calculate alignment for bindings
    p = pad(indent + 1)
    pb = " " * (indent * INDENT + len(head) + 3)  # Align after "(let (("

    # First binding
    lines = []
    if isinstance(bindings, SList) and len(bindings) > 0 and not _is_quote_sugar(bindings):
        first_binding = inline(bindings[0])
        lines.append(f"({head} ({first_binding}")

        # Remaining bindings aligned
        for binding in bindings.items[1:]:
            lines.append(pb + inline(binding))

        lines[-1] += ")"
    else:
        lines.append(f"({head} {inline(bindings)}")

    # Body
    for item in body:
        lines.append(p + format_expr(item, indent + 1))

    lines[-1] += ")"
    return '\n'.join(lines)


def format_if(expr: SList, indent: int) -> str:
    """Format if: (if cond then else)"""
    if len(expr) < 3:
        return inline(expr)

    # Short if can be inline
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    p = pad(indent + 1)
    cond = expr[1]

    # Condition inline if short
    cond_str = inline(cond) if fits_inline(cond, 40) else format_expr(cond, indent + 1)

    lines = [f"(if {cond_str}"]
    for branch in expr.items[2:]:
        lines.append(p + format_expr(branch, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_when(expr: SList, indent: int) -> str:
    """Format when: (when cond body...)"""
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    p = pad(indent + 1)
    cond = inline(expr[1]) if len(expr) > 1 else ""
    body = expr.items[2:]

    lines = [f"(when {cond}"]
    for item in body:
        lines.append(p + format_expr(item, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_cond(expr: SList, indent: int) -> str:
    """Format cond: (cond (test1 result1) (test2 result2) ...)"""
    p = pad(indent + 1)
    p2 = pad(indent + 2)
    lines = ["(cond"]
    for clause in expr.items[1:]:
        if isinstance(clause, SList) and len(clause) >= 2 and not _is_quote_sugar(clause):
            # Format clause with test and body on separate lines
            test = clause[0]
            body = clause.items[1:]
            test_str = format_expr(test, indent + 2) if isinstance(test, SList) else inline(test)
            # Short clause: ((test) body) on one line if simple
            if len(body) == 1 and fits_inline(clause, 60):
                lines.append(p + f"({test_str} {format_expr(body[0], indent + 2)})")
            else:
                # Multi-line clause
                lines.append(p + f"({test_str}")
                for item in body:
                    lines.append(p2 + format_expr(item, indent + 2))
                lines[-1] += ")"
        else:
            lines.append(p + format_expr(clause, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_match(expr: SList, indent: int) -> str:
    """Format match: (match value (pattern1 result1) ...)"""
    if len(expr) < 2:
        return inline(expr)

    p = pad(indent + 1)
    value = inline(expr[1])
    clauses = expr.items[2:]

    lines = [f"(match {value}"]
    for clause in clauses:
        lines.append(p + format_expr(clause, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_do(expr: SList, indent: int) -> str:
    """Format do: (do expr1 expr2 ...)"""
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    p = pad(indent + 1)
    lines = ["(do"]
    for item in expr.items[1:]:
        lines.append(p + format_expr(item, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_while(expr: SList, indent: int) -> str:
    """Format while: (while cond body...)"""
    if len(expr) < 2:
        return inline(expr)

    p = pad(indent + 1)
    cond = inline(expr[1])
    body = expr.items[2:]

    lines = [f"(while {cond}"]
    for item in body:
        lines.append(p + format_expr(item, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_for(expr: SList, indent: int) -> str:
    """Format for: (for (init cond step) body...)"""
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    p = pad(indent + 1)
    control = inline(expr[1]) if len(expr) > 1 else "()"
    body = expr.items[2:]

    lines = [f"(for {control}"]
    for item in body:
        lines.append(p + format_expr(item, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_for_each(expr: SList, indent: int) -> str:
    """Format for-each: (for-each (var collection) body...)"""
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    p = pad(indent + 1)
    binding = inline(expr[1]) if len(expr) > 1 else "()"
    body = expr.items[2:]

    lines = [f"(for-each {binding}"]
    for item in body:
        lines.append(p + format_expr(item, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_with_arena(expr: SList, indent: int) -> str:
    """Format with-arena: (with-arena size body...) or
    (with-arena :as name size body...)"""
    if len(expr) < 2:
        return inline(expr)

    p = pad(indent + 1)
    if isinstance(expr[1], Symbol) and expr[1].name == ':as':
        header = expr.items[1:4]
        body = expr.items[4:]
    else:
        header = expr.items[1:2]
        body = expr.items[2:]

    lines = ["(with-arena " + " ".join(inline(x) for x in header)]
    for item in body:
        lines.append(p + format_expr(item, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_ffi(expr: SList, indent: int) -> str:
    """Format ffi: (ffi "header.h" (func ...) ...)"""
    if len(expr) < 2:
        return inline(expr)

    p = pad(indent + 1)
    header = expr[1]
    funcs = expr.items[2:]

    lines = [f'(ffi {inline(header)}']
    for func in funcs:
        lines.append(p + format_ffi_func(func, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_ffi_func(expr: SExpr, indent: int) -> str:
    """Format FFI function: (name ((param Type) ...) ReturnType)"""
    if not isinstance(expr, SList) or _is_quote_sugar(expr):
        return format_expr(expr, indent)
    if fits_inline(expr, MAX_LINE - indent * INDENT - 4):
        return inline(expr)

    if len(expr) < 3:
        return inline(expr)

    name = expr[0]
    params = expr[1]
    rest = expr.items[2:]

    p = pad(indent + 1)

    # Try to fit params inline
    params_inline = inline(params)
    if len(params_inline) < 50:
        return "(" + " ".join([inline(name), params_inline] + [inline(x) for x in rest]) + ")"

    # Multi-line params
    lines = [f"({inline(name)}"]
    lines.append(p + format_expr(params, indent + 1))
    for item in rest:
        lines.append(p + format_expr(item, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_ffi_struct(expr: SList, indent: int) -> str:
    """Format ffi-struct: (ffi-struct "header" name (field Type) ...)"""
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    p = pad(indent + 1)
    lines = [f"({expr[0]}"]
    for item in expr.items[1:]:
        lines.append(p + format_expr(item, indent + 1))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_import(expr: SList, indent: int) -> str:
    """Format import: (import module (fn arity) Type ...)"""
    if fits_inline(expr, MAX_LINE - indent * INDENT) or len(expr) < 2:
        return inline(expr)

    p = pad(indent + 1)
    lines = [f"(import {inline(expr[1])}"]
    for item in expr.items[2:]:
        lines.append(p + inline(item))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_export(expr: SList, indent: int) -> str:
    """Format export: (export (fn1 arity) (fn2 arity) ...)"""
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    p = pad(indent + 1)
    lines = ["(export"]
    for item in expr.items[1:]:
        lines.append(p + inline(item))
    lines[-1] += ")"
    return '\n'.join(lines)


def format_hole(expr: SList, indent: int) -> str:
    """Format hole: (hole Type "prompt" :complexity tier :context (...) :required (...))"""
    if len(expr) < 3:
        return inline(expr)

    p = pad(indent + 1)
    type_expr = expr[1]
    prompt = expr[2]
    rest = expr.items[3:]

    lines = [f"(hole {inline(type_expr)}"]
    lines.append(p + inline(prompt))

    # Format keyword args
    i = 0
    while i < len(rest):
        item = rest[i]
        if isinstance(item, Symbol) and item.name.startswith(':'):
            # Keyword with value
            if i + 1 < len(rest):
                lines.append(p + f"{item} {inline(rest[i+1])}")
                i += 2
                continue
        lines.append(p + inline(item))
        i += 1

    lines[-1] += ")"
    return '\n'.join(lines)


def format_generic(expr: SList, indent: int) -> str:
    """Generic formatter for other forms - smart wrapping."""
    # Short expressions stay inline
    if fits_inline(expr, MAX_LINE - indent * INDENT):
        return inline(expr)

    # Check if all args are simple (no nested lists)
    all_simple = all(not isinstance(x, SList) for x in expr.items[1:])
    if all_simple and len(expr) < 6:
        return inline(expr)

    # Multi-line format
    p = pad(indent + 1)
    head = format_expr(expr[0], indent + 1)
    lines = [f"({head}"]

    for item in expr.items[1:]:
        formatted = format_expr(item, indent + 1)
        lines.append(p + formatted)

    lines[-1] += ")"
    return '\n'.join(lines)
