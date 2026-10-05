"""Native parser JSON output: float literals and string escapes.

The JSON printer used to format floats with %.15f, which zeroed 1e-20 and
overran its buffer for 1e300, and it wrote control bytes other than \\n \\r
\\t raw, which json.loads rejects. _json_to_ast ignored is_float.
"""

import json
import subprocess
from pathlib import Path

import pytest

from slop.cli import _json_to_ast, find_native_component
from slop.parser import Number, String

REPO_ROOT = Path(__file__).resolve().parent.parent


def _native_parser():
    # Prefer this checkout's build over SLOP_HOME, which may name another tree
    local = REPO_ROOT / "bin" / "slop-parser"
    if local.exists():
        return local
    return find_native_component("parser")


def _parse_json(tmp_path, source: bytes):
    parser = _native_parser()
    if not parser:
        pytest.skip("native parser not built (make build-native)")
    src = tmp_path / "input.slop"
    src.write_bytes(source)
    result = subprocess.run(
        [str(parser), "--format", "json", str(src)],
        capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout.decode("utf-8"))


def _items(tmp_path, source: bytes):
    return _json_to_ast(_parse_json(tmp_path, source))[0].items


class TestJsonToAstNumbers:
    def test_float_flag_makes_float(self):
        node = _json_to_ast({"type": "Number", "value": 2, "is_float": True,
                             "line": 1, "col": 1})
        assert isinstance(node, Number)
        assert isinstance(node.value, float)
        assert node.value == 2.0

    def test_int_stays_int(self):
        node = _json_to_ast({"type": "Number", "value": 42, "is_float": False,
                             "line": 1, "col": 1})
        assert isinstance(node.value, int) and node.value == 42

    def test_raw_kept(self):
        node = _json_to_ast({"type": "Number", "value": 1e307, "is_float": True,
                             "raw": "1.0e+307", "line": 1, "col": 1})
        assert node.value == 1e307
        assert node.raw == "1.0e+307"

    def test_missing_is_float_reads_int(self):
        node = _json_to_ast({"type": "Number", "value": 3})
        assert node.value == 3 and isinstance(node.value, int)


class TestNativeJsonFloats:
    def test_float_literals_keep_value_and_text(self, tmp_path):
        items = _items(tmp_path, b"(a 1.0e+307 2E-3 1e-20 1e300 007.5 -00.5 1e3 0042)\n")
        nums = items[1:]
        assert [n.value for n in nums] == [1e307, 2e-3, 1e-20, 1e300, 7.5, -0.5, 1000.0, 42]
        assert [type(n.value) for n in nums] == [float] * 7 + [int]
        assert [getattr(n, "raw", None) for n in nums] == [
            "1.0e+307", "2E-3", "1e-20", "1e300", "007.5", "-00.5", "1e3", "0042"]

    def test_number_literals_file(self):
        parser = _native_parser()
        if not parser:
            pytest.skip("native parser not built (make build-native)")
        result = subprocess.run(
            [str(parser), "--format", "json",
             str(REPO_ROOT / "tests" / "test_number_literals.slop")],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, result.stderr
        json.loads(result.stdout)
        assert '"raw":"1.0e+307"' in result.stdout


class TestNativeJsonStrings:
    def test_carriage_return_escape(self, tmp_path):
        items = _items(tmp_path, b'(a "x\\ry" "tab\\tnl\\n")\n')
        assert [s.value for s in items[1:]] == ["x\ry", "tab\tnl\n"]

    def test_raw_control_bytes(self, tmp_path):
        # Control bytes written literally in the source must come out as
        # \\u00XX, which json.loads accepts, and keep their value
        items = _items(tmp_path, b'(a "c\x01d\x1fe\rf\x7f")\n')
        assert isinstance(items[1], String)
        assert items[1].value == "c\x01d\x1fe\rf\x7f"

    def test_unknown_escape_and_backslash(self, tmp_path):
        # The lexer keeps an unknown escape as backslash + char, the same
        # value an escaped backslash gives
        items = _items(tmp_path, b'(a "q\\xz" "q\\\\xz")\n')
        assert [s.value for s in items[1:]] == ["q\\xz", "q\\xz"]
