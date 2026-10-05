"""slop fill writes each fill over its hole and leaves the rest of the file as it was."""
import sys

import pytest

from slop import cli
from slop.providers import MockProvider
from slop.parser import parse, find_holes, Symbol, SList


SCAFFOLD = """\
;; Header comment: keep me
(module adder
  (export add)

  ;; Adds two numbers
  (fn add ((x Int) (y Int))   ; odd   spacing kept
    (@intent "Add x and y")
    (@spec ((Int Int) -> Int))
    (hole Int "add x and y" :complexity tier-1 :required (x y)))  ; trailing

  (fn main ()
    (@spec (() -> Int))
    0))
"""

# Too long for one line, so the formatter breaks it
LONG_FILL = ('(if (> x 0) (some-long-function-name x y z)'
             ' (another-long-function-name y x z))')

HOLE = '(hole Int "add x and y" :complexity tier-1 :required (x y))'


def _run_fill(monkeypatch, tmp_path, answer, *args):
    # No slop.toml next to the file or in the cwd: fill uses the mock
    # provider, here made to give one answer to every prompt
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(MockProvider, 'complete', lambda self, prompt, config: answer)
    monkeypatch.setattr(sys, 'argv', ['slop', 'fill', *args])
    return cli.main()


needs_native = pytest.mark.skipif(
    cli.find_native_component('parser') is None,
    reason="fill validates through the native parser; run make install")


@needs_native
def test_fill_splices_into_original_text(monkeypatch, tmp_path):
    src = tmp_path / "add.slop"
    src.write_text(SCAFFOLD)

    code = _run_fill(monkeypatch, tmp_path, '(+ x y)', str(src))
    assert code == 0

    out = src.read_text()
    start = SCAFFOLD.index(HOLE)
    end = start + len(HOLE)
    # Every byte outside the hole is unchanged, comments included
    assert out.startswith(SCAFFOLD[:start])
    assert out.endswith(SCAFFOLD[end:])
    fill = out[start:len(out) - len(SCAFFOLD) + end]
    assert fill == "(+ x y)"
    assert not find_holes(SList(parse(out)))


@needs_native
def test_no_write_when_nothing_filled(monkeypatch, tmp_path, capsys):
    scaffold = SCAFFOLD
    src = tmp_path / "add.slop"
    src.write_text(scaffold)
    before = src.stat().st_mtime_ns

    # An answer that fails validation every time: nothing is filled
    code = _run_fill(monkeypatch, tmp_path, '(undefined-function q)', str(src))
    assert code == 1
    assert src.read_text() == scaffold
    assert src.stat().st_mtime_ns == before
    assert "not written" in capsys.readouterr().err


class TestSplice:
    """_splice_fills on its own, with fills given directly."""

    def _holes(self, text):
        forms = parse(text)
        return [(None, h) for f in forms for h in find_holes(f)]

    def test_multiline_fill_indented_to_hole_column(self):
        text = (
            "(fn f ((x Int))\n"
            "  ; before\n"
            "  (let ((y 1))\n"
            "   (hole Int \"h\")))  ; after\n"
        )
        holes = self._holes(text)
        fill = parse(LONG_FILL)[0]
        out = cli._splice_fills(text, holes, {id(holes[0][1]): fill})
        start = text.index('(hole')
        end = text.index(')))  ; after') + 1
        assert out.startswith(text[:start])
        assert out.endswith(text[end:])
        lines = out[start:].split('\n')
        assert lines[0] == '(if (> x 0)'
        # Continuation lines sit one indent inside the hole's column (3)
        assert lines[1].startswith(' ' * 5 + '(some-long')
        assert parse(out)

    def test_nothing_to_splice(self):
        text = '(fn f () (hole Int "h"))\n'
        assert cli._splice_fills(text, self._holes(text), {}) is None

    def test_crlf_kept(self):
        text = '(fn f ()\r\n  ; c\r\n  (hole Int "h"))\r\n'
        holes = self._holes(text)
        fill = parse(LONG_FILL)[0]
        out = cli._splice_fills(text, holes, {id(holes[0][1]): fill})
        assert out.count('\n') == out.count('\r\n')
        assert out.startswith('(fn f ()\r\n  ; c\r\n  (if')

    def test_two_holes(self):
        text = '(fn f () (do (hole Int "a") ; one\n  (hole Int "b")))\n'
        holes = self._holes(text)
        out = cli._splice_fills(text, holes, {
            id(holes[0][1]): Symbol('x'),
            id(holes[1][1]): Symbol('y'),
        })
        assert out == '(fn f () (do x ; one\n  y))\n'
