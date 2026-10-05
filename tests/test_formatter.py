"""Tests for SLOP formatter."""
import pytest
from slop.formatter import format_source, format_expr, inline
from slop.parser import parse


class TestInline:
    """Test inline rendering."""

    def test_simple_expr(self):
        ast = parse("(+ x y)")
        assert inline(ast[0]) == "(+ x y)"

    def test_nested_expr(self):
        ast = parse("(+ (* a b) c)")
        assert inline(ast[0]) == "(+ (* a b) c)"

    def test_string(self):
        ast = parse('(print "hello")')
        assert inline(ast[0]) == '(print "hello")'


class TestFormatFn:
    """Test function formatting."""

    def test_simple_fn(self):
        source = '(fn foo ((x Int)) (@intent "test") body)'
        result = format_source(source)
        assert "(fn foo ((x Int))" in result
        assert '(@intent "test")' in result

    def test_fn_multiline(self):
        source = '(fn foo ((x Int) (y String)) (@intent "test") (@spec ((Int String) -> Bool)) (some-body x y))'
        result = format_source(source)
        lines = result.strip().split('\n')
        assert lines[0] == "(fn foo ((x Int) (y String))"
        assert any('@intent' in line for line in lines)
        assert any('@spec' in line for line in lines)


class TestFormatModule:
    """Test module formatting."""

    def test_module_structure(self):
        source = '''
        (module test
          (export (foo 1))
          (type Bar Int)
          (fn foo ((x Int)) x))
        '''
        result = format_source(source)
        lines = result.strip().split('\n')
        assert lines[0] == "(module test"
        assert any("(export" in line for line in lines)
        assert any("(type" in line for line in lines)
        assert any("(fn foo" in line for line in lines)


class TestFormatType:
    """Test type definition formatting."""

    def test_inline_enum(self):
        source = "(type Status (enum pending active done))"
        result = format_source(source)
        assert "(type Status (enum pending active done))" in result

    def test_record_multiline(self):
        source = "(type User (record (name String) (age Int) (email String)))"
        result = format_source(source)
        lines = result.strip().split('\n')
        # Record should be multi-line if fields are complex
        assert any("(name String)" in line for line in lines)


class TestFormatLet:
    """Test let binding formatting."""

    def test_simple_let(self):
        source = "(let ((x 1)) x)"
        result = format_source(source)
        assert "(let ((x 1))" in result

    def test_multiple_bindings(self):
        source = "(let ((x 1) (y 2) (z 3)) (+ x y z))"
        result = format_source(source)
        # Multiple bindings should be aligned
        assert "(let ((" in result


class TestFormatControlFlow:
    """Test control flow formatting."""

    def test_short_if_inline(self):
        source = "(if cond a b)"
        result = format_source(source)
        assert result.strip() == "(if cond a b)"

    def test_long_if_multiline(self):
        source = "(if (some-long-condition x y z) (then-expression with many args) (else-expression also long))"
        result = format_source(source)
        lines = result.strip().split('\n')
        assert len(lines) > 1  # Should be multi-line

    def test_match(self):
        source = "(match x (Foo a) (Bar b))"
        result = format_source(source)
        assert "(match x" in result


class TestFormatGeneric:
    """Test generic expression formatting."""

    def test_short_inline(self):
        source = "(+ 1 2)"
        result = format_source(source)
        assert result.strip() == "(+ 1 2)"

    def test_long_wraps(self):
        source = "(some-func arg1 arg2 arg3 (nested-call with args) (another-nested-call with more args))"
        result = format_source(source)
        # Long expressions should wrap
        assert result.strip().startswith("(some-func")


class TestFormatFfi:
    """Test FFI formatting."""

    def test_ffi_block(self):
        source = '''(ffi "stdio.h" (printf ((fmt String)) Int) (puts ((s String)) Int))'''
        result = format_source(source)
        lines = result.strip().split('\n')
        assert '(ffi "stdio.h"' in lines[0]

    def test_ffi_struct(self):
        source = "(ffi-struct header.h Point (x Int) (y Int))"
        result = format_source(source)
        assert "ffi-struct" in result


class TestFormatHole:
    """Test hole expression formatting."""

    def test_hole_multiline(self):
        source = '(hole Int "compute something" :complexity tier-2 :required (x y))'
        result = format_source(source)
        lines = result.strip().split('\n')
        assert lines[0] == "(hole Int"
        assert any(":complexity" in line for line in lines)
        assert any(":required" in line for line in lines)


class TestRoundTrip:
    """Test that formatting is idempotent."""

    def test_idempotent(self):
        source = '''
        (module test
          (export (main 0))
          (fn main ()
            (@intent "entry point")
            (@spec (() -> Int))
            0))
        '''
        first = format_source(source)
        second = format_source(first)
        assert first == second


def fmt(source):
    """Format, and check that formatting the result changes nothing."""
    out = format_source(source)
    assert format_source(out) == out, "formatting is not idempotent"
    return out


def same_code(a, b):
    from slop.formatter import _canon
    return [_canon(f) for f in parse(a)] == [_canon(f) for f in parse(b)]


def comment_lines(text):
    return [line.strip() for line in text.split('\n') if line.strip().startswith(';')]


class TestComments:
    """Comments survive formatting, attached where they were written."""

    def test_file_header(self):
        source = ";; Header line 1\n;; Header line 2\n\n(fn f ()\n  0)\n"
        assert fmt(source) == source

    def test_header_without_blank_line(self):
        source = ";; About f\n(fn f ()\n  0)\n"
        assert fmt(source) == source

    def test_comment_only_file(self):
        assert fmt(";; nothing here\n") == ";; nothing here\n"

    def test_trailing_comment_on_form(self):
        out = fmt("(const X Int 1) ; one\n(const Y Int 2)\n")
        assert out == "(const X Int 1) ; one\n\n(const Y Int 2)\n"

    def test_leading_and_trailing_in_fn(self):
        source = """
(fn f ((x Int)) ; params
  (@intent "f")
  (@spec ((Int) -> Int))
  ;; the body
  (+ x 1)) ; after
"""
        out = fmt(source)
        lines = out.split('\n')
        assert lines[0] == "(fn f ((x Int)) ; params"
        assert "  ;; the body" in lines
        assert lines[lines.index("  ;; the body") + 1] == "  (+ x 1)) ; after"

    def test_dangling_comment(self):
        out = fmt("(fn f ()\n  (do-it)\n  ;; nothing after\n  )\n")
        assert out == "(fn f ()\n  (do-it)\n  ;; nothing after\n)\n"

    def test_trailing_comment_on_last_child_moves_paren(self):
        assert fmt("(do (a)\n  (b)) ; b\n") == "(do (a) (b)) ; b\n"
        out = fmt("(do\n  (a)\n  (b) ; b\n)\n")
        assert out == "(do\n  (a)\n  (b) ; b\n)\n"

    def test_in_let(self):
        source = """
(fn f ()
  (let ((a 1) ; first
        ;; second binding
        (b 2))
    ;; body
    (+ a b)))
"""
        out = fmt(source)
        assert "  (let ((a 1) ; first" in out
        assert "        ;; second binding\n        (b 2))" in out
        assert "    ;; body\n    (+ a b)))" in out

    def test_in_let_star(self):
        out = fmt("(let* ((a 1) ; one\n       (b a))\n  b)\n")
        assert out == "(let* ((a 1) ; one\n       (b a))\n  b)\n"

    def test_in_match(self):
        source = """
(match x
  ;; the some case
  ((some v) v) ; got one
  ((none) 0))
"""
        out = fmt(source)
        assert out == "(match x\n  ;; the some case\n  ((some v) v) ; got one\n  ((none) 0))\n"

    def test_in_cond(self):
        source = "(cond\n  ((> x 0) 1) ; positive\n  ;; otherwise\n  (else 0))\n"
        assert fmt(source) == source

    def test_module_level(self):
        source = """;; Module header

(module m ; the module
  (export f)

  ;; Section: functions

  ;; f does nothing
  (fn f ()
    0)
  ;; last word
  )
"""
        out = fmt(source)
        assert comment_lines(out) == comment_lines(source)
        assert out.startswith(";; Module header\n\n(module m ; the module\n  (export f)\n")
        assert "  ;; Section: functions\n\n  ;; f does nothing\n  (fn f ()\n    0)\n" in out
        assert out.endswith("  ;; last word\n)\n")

    def test_comments_travel_with_reordered_imports(self):
        source = """(module m
  ;; the code
  (fn f ()
    0)
  ;; strings
  (import strlib (concat 2)) ; for concat
  (export f))
"""
        out = fmt(source)
        assert out == """(module m
  ;; strings
  (import strlib (concat 2)) ; for concat
  (export f)

  ;; the code
  (fn f ()
    0))
"""

    def test_after_imports(self):
        source = "(module m\n  (import a (x 1)) ; a\n  (import b (y 1))\n  ;; after imports\n\n  (fn f () 0))\n"
        out = fmt(source)
        assert "  (import a (x 1)) ; a\n  (import b (y 1))\n\n  ;; after imports\n\n  (fn f ()\n    0))" in out

    def test_comment_forces_multiline(self):
        out = fmt("(+ 1 ; one\n   2)\n")
        assert out == "(+\n  1 ; one\n  2)\n"

    def test_comment_inside_type_record(self):
        source = "(type P (record\n    (x Int) ; x\n    (y Int)))\n"
        out = fmt(source)
        assert "(x Int) ; x" in out
        assert same_code(out, source)

    def test_comment_count_preserved_on_examples(self, examples_dir):
        from slop.parser import Lexer
        for path in sorted(examples_dir.glob('*.slop')):
            source = path.read_text()
            out = fmt(source)
            counts = []
            for text in (source, out):
                lexer = Lexer(text)
                lexer.tokenize()
                counts.append(len(lexer.comments))
            assert counts[0] == counts[1], path.name

    def test_blank_lines_between_top_level_forms_collapse(self):
        out = fmt("(const A Int 1)\n\n\n\n(const B Int 2)\n")
        assert out == "(const A Int 1)\n\n(const B Int 2)\n"


class TestLiterals:
    """Strings and numbers are written as they were read."""

    def test_carriage_return_escape(self):
        source = '(print "a\\r\\nb")\n'
        assert fmt(source) == source

    def test_raw_carriage_return_kept(self):
        source = '(print "a\rb")\n'
        assert fmt(source) == source

    def test_unknown_escape_round_trips(self):
        source = '(print "a\\qb \\e")\n'
        assert fmt(source) == source

    def test_string_built_in_code_escapes_cr(self):
        from slop.parser import String
        assert repr(String("a\rb\n\"")) == '"a\\rb\\n\\""'

    def test_float_kept_as_written(self):
        source = "(const BIG Float 1e+307)\n\n(const X Float 1.50)\n\n(const E Float 1e5)\n"
        assert fmt(source) == source

    def test_float_out_of_range_refused(self):
        from slop.formatter import FormatError
        with pytest.raises(FormatError, match="out of range"):
            format_source("(const BIG Float 1e400)\n")

    def test_float_repr_without_source(self):
        from slop.parser import Number
        assert repr(Number(1e+307)) == "1e+307"
        assert repr(Number(2.5)) == "2.5"
        with pytest.raises(ValueError):
            repr(Number(float('inf')))


class TestInfix:
    def test_infix_kept(self):
        source = '(fn f ((x Int))\n  (@pre {x > 0 and x < 10})\n  x)\n'
        assert fmt(source) == source

    def test_multiline_infix_kept(self):
        source = '(fn f ((x Int))\n  (@pre {x > 0\n         and x < 10})\n  x)\n'
        assert fmt(source) == source


class TestFormBugs:
    def test_impl_keeps_its_name(self):
        out = fmt("(impl foo ((x Int)) (@spec ((Int) -> Int)) (+ x 1))")
        assert out.startswith("(impl foo ((x Int))")

    def test_let_star_keeps_its_name(self):
        out = fmt("(let* ((a 1) (b (+ a 1))) (+ a b))")
        assert out.startswith("(let* ((a 1)")
        assert "\n       (b (+ a 1)))" in out

    def test_with_arena_as(self):
        source = "(with-arena :as scratch 4096 (do-something scratch) (do-something-else scratch with more args))"
        out = fmt(source)
        assert out.split('\n')[0] == "(with-arena :as scratch 4096"
        assert same_code(out, source)

    def test_if_with_empty_list_branch(self):
        source = "(if (some-long-condition-function x y z) (then-expression with many args) ())"
        out = fmt(source)
        assert out.rstrip().endswith("())")

    def test_quote_sugar_kept(self):
        assert fmt("(f '(a b) 'c)\n") == "(f '(a b) 'c)\n"

    def test_crlf_kept(self):
        source = ";; c\r\n(fn f ()\r\n  ; x\r\n  0)\r\n"
        out = fmt(source)
        assert out == source


class TestIdempotence:
    def test_examples_idempotent(self, examples_dir):
        for path in sorted(examples_dir.glob('*.slop')):
            fmt(path.read_text())
