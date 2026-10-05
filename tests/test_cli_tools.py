"""
Tests for the CLI's tooling commands: doc, paths, parse --holes, transpile
error reporting and ref help.

Commands that need the native toolchain run against this checkout's bin/
(built by `make install`) and are skipped when it is missing.
"""

import json
import sys

import pytest
from pathlib import Path

from slop import cli

REPO_ROOT = Path(__file__).parent.parent
BIN_DIR = REPO_ROOT / "bin"


def _have(name: str) -> bool:
    return (BIN_DIR / f"slop-{name}").exists()


needs_parser = pytest.mark.skipif(not _have("parser"), reason="bin/slop-parser not built (make install)")
needs_compiler = pytest.mark.skipif(not _have("compiler"), reason="bin/slop-compiler not built (make install)")


@pytest.fixture(autouse=True)
def repo_slop_home(monkeypatch):
    """Resolve native binaries from this checkout, whatever SLOP_HOME says."""
    monkeypatch.setenv("SLOP_HOME", str(REPO_ROOT))


def run_cli(monkeypatch, capsys, *argv):
    monkeypatch.setattr(sys, "argv", ["slop", *argv])
    rc = cli.main()
    out, err = capsys.readouterr()
    return rc, out, err


DOC_MODULE = """\
(module docmod
  (@intent "A small module for doc extraction")
  (@doc "Longer module documentation.")
  (export Shape Config Scores Percent f MAX_ITEMS)

  (ffi "math.h"
    (sqrt ((x Float)) Float)
    (HUGE_VAL Float))

  (type Shape (union
    (circle Float)
    (rect Float Float)
    (empty)))

  (type Config (record
    (name String)
    (handlers (Map String (List (Ptr Config))))
    (port (Int 1 .. 65535))
    (timeout (Option (Int 0 .. 1000)))))

  (type Scores (Map String Int))

  (type Percent (Int 0 .. 100))

  (type Color (enum red green blue))

  (const MAX_ITEMS Int 128)

  (fn f ((x Int))
    (@intent "Add one")
    (@spec ((Int) -> Int))
    (@pre {x >= 0})
    (@example (1) -> 2)
    (@example :eq int-eq (41) -> 42)
    (+ x 1))

  (fn first-of ((xs (List T)) (mut n (Map String (List (Ptr Config)))))
    (@intent "Pick the first element")
    (@generic (T))
    (@spec (((List T) (Map String (List (Ptr Config)))) -> (Option T)))
    (@property (forall (x Int) (== x x)))
    (@assume {(list-len xs) >= 0})
    (list-get xs 0)))
"""


@pytest.fixture
def doc_module(tmp_path):
    path = tmp_path / "docmod.slop"
    path.write_text(DOC_MODULE)
    return path


def extract(path):
    from slop.parser import parse_file
    return cli.extract_documentation(parse_file(str(path)))


class TestDoc:
    def test_type_kinds(self, doc_module):
        doc = extract(doc_module)
        kinds = {t["name"]: t["kind"] for t in doc["types"]}
        assert kinds == {
            "Shape": "union",
            "Config": "record",
            "Scores": "alias",
            "Percent": "range",
            "Color": "enum",
        }

    def test_union_variants(self, doc_module):
        shape = next(t for t in extract(doc_module)["types"] if t["name"] == "Shape")
        assert shape["variants"] == [
            {"name": "circle", "types": ["Float"]},
            {"name": "rect", "types": ["Float", "Float"]},
            {"name": "empty", "types": []},
        ]

    def test_range_and_alias_details(self, doc_module):
        types = {t["name"]: t for t in extract(doc_module)["types"]}
        assert (types["Percent"]["base"], types["Percent"]["min"], types["Percent"]["max"]) == ("Int", "0", "100")
        assert types["Scores"]["target"] == "(Map String Int)"

    def test_field_and_param_types_are_single_line(self, doc_module):
        doc = extract(doc_module)
        config = next(t for t in doc["types"] if t["name"] == "Config")
        fields = {f["name"]: f["type"] for f in config["fields"]}
        assert fields["handlers"] == "(Map String (List (Ptr Config)))"
        assert fields["timeout"] == "(Option (Int 0 .. 1000))"
        first_of = next(f for f in doc["functions"] if f["name"] == "first-of")
        assert first_of["params"][1] == {
            "name": "n", "type": "(Map String (List (Ptr Config)))", "direction": "mut"}

        md = cli.render_markdown(doc)
        assert "- `handlers` — `(Map String (List (Ptr Config)))`" in md
        assert "- `n` *(mut)* — `(Map String (List (Ptr Config)))`" in md

    def test_example_rendering(self, doc_module):
        doc = extract(doc_module)
        f = next(fn for fn in doc["functions"] if fn["name"] == "f")
        assert f["examples"] == ["(f 1) ;=> 2", "(f 41) ;=> 42 (:eq int-eq)"]
        assert f["example_cases"][0] == {"args": "1", "expected": "2"}
        assert f["example_cases"][1] == {"args": "41", "expected": "42", "eq": "int-eq"}
        md = cli.render_markdown(doc)
        assert "(f 1) ;=> 2" in md
        assert "((1) -> 2)" not in md

    def test_module_annotations_exports_and_ffi(self, doc_module):
        doc = extract(doc_module)
        assert doc["intent"] == "A small module for doc extraction"
        assert doc["doc"] == "Longer module documentation."
        exported = {t["name"]: t["exported"] for t in doc["types"]}
        assert exported["Shape"] and not exported["Color"]
        assert doc["constants"][0]["exported"]
        fns = {fn["name"]: fn for fn in doc["functions"]}
        assert fns["f"]["exported"] and not fns["first-of"]["exported"]
        assert fns["first-of"]["generic"] == ["T"]
        assert fns["first-of"]["properties"] == ["(forall (x Int) (== x x))"]
        assert fns["first-of"]["assume"] == ["(>= (list-len xs) 0)"]
        [ffi] = doc["ffi"]
        assert ffi["header"] == "math.h"
        assert ffi["functions"][0]["signature"] == "(sqrt ((x Float)) Float)"
        assert ffi["constants"] == [{"name": "HUGE_VAL", "type": "Float"}]

        md = cli.render_markdown(doc)
        assert "> A small module for doc extraction" in md
        assert "### Color *(internal)*" in md
        assert "**Type parameters:** `T`" in md
        assert "- `rect` — `Float`, `Float`" in md
        assert "### `math.h`" in md

    def test_doc_command_json(self, monkeypatch, capsys, doc_module):
        rc, out, _ = run_cli(monkeypatch, capsys, "doc", str(doc_module), "-f", "json")
        assert rc == 0
        doc = json.loads(out)
        assert doc["module"] == "docmod"
        assert [t["kind"] for t in doc["types"]] == ["union", "record", "alias", "range", "enum"]


class TestPaths:
    def test_lists_the_four_native_binaries(self, monkeypatch, capsys):
        rc, out, _ = run_cli(monkeypatch, capsys, "paths")
        assert rc == 0
        for name in ("parser", "checker", "compiler", "tester"):
            assert f"slop-{name}" in out
        assert "slop-transpiler" not in out


HOLES_MODULE = """\
(module holes
  (fn double ((x Int))
    (@intent "Double a number")
    (@spec ((Int) -> Int))
    (hole Int "double x" :complexity tier-1 :required (x))))
"""


class TestParseHoles:
    @needs_parser
    def test_holes_with_native_parser(self, monkeypatch, capsys, tmp_path):
        path = tmp_path / "holes.slop"
        path.write_text(HOLES_MODULE)
        rc, out, err = run_cli(monkeypatch, capsys, "parse", "--holes", str(path))
        assert rc == 0
        assert "Using native parser" in err
        assert out.startswith("Hole: double x\n")
        assert "Required: x" in out
        assert "(fn" not in out and "module" not in out
        assert "Found 1 holes" in err

    def test_holes_with_python_parser(self, monkeypatch, capsys, tmp_path):
        monkeypatch.setattr(cli, "find_native_component", lambda name: None)
        path = tmp_path / "holes.slop"
        path.write_text(HOLES_MODULE)
        rc, out, err = run_cli(monkeypatch, capsys, "parse", "--holes", str(path))
        assert rc == 0
        assert out.startswith("Hole: double x\n")
        assert "(fn" not in out


BROKEN_MODULE = """\
(module broken
  (fn f ((x Int))
    (@spec ((Int) -> Int))
    (+ x 1)
"""


class TestNativeErrors:
    @needs_compiler
    def test_transpile_parse_error_is_reported(self, monkeypatch, capsys, tmp_path):
        path = tmp_path / "broken.slop"
        path.write_text(BROKEN_MODULE)
        rc, out, err = run_cli(monkeypatch, capsys, "transpile", str(path))
        assert rc != 0
        assert f"{path}:2:3: error:" in err
        assert "not found" not in err

    @needs_compiler
    def test_transpile_missing_file_is_reported(self, monkeypatch, capsys, tmp_path):
        path = tmp_path / "missing.slop"
        rc, out, err = run_cli(monkeypatch, capsys, "transpile", str(path))
        assert rc != 0
        assert f"Error: Could not open file: {path}" in err
        assert "not found" not in err

    def test_transpile_without_compiler_says_not_found(self, monkeypatch, capsys, tmp_path):
        monkeypatch.setattr(cli, "find_native_component", lambda name: None)
        path = tmp_path / "broken.slop"
        path.write_text(BROKEN_MODULE)
        rc, out, err = run_cli(monkeypatch, capsys, "transpile", str(path))
        assert rc == 1
        assert "Native SLOP compiler not found" in err

    @needs_compiler
    def test_transpile_to_cache_reports_errors(self, capsys, tmp_path):
        path = tmp_path / "broken.slop"
        path.write_text(BROKEN_MODULE)
        assert not cli.transpile_to_cache(path, tmp_path, [])
        err = capsys.readouterr().err
        assert f"{path}:2:3: error:" in err
        assert "not found" not in err

    @needs_parser
    def test_parse_native_json_error_includes_parser_message(self, tmp_path):
        path = tmp_path / "broken.slop"
        path.write_text(BROKEN_MODULE)
        message, ok = cli.parse_native_json(str(path))
        assert not ok
        assert "Parse error at line" in message


class TestRefHelp:
    def test_help_lists_every_topic(self, monkeypatch, capsys):
        from slop.reference import TOPICS
        monkeypatch.setattr(sys, "argv", ["slop", "ref", "--help"])
        with pytest.raises(SystemExit):
            cli.main()
        out = " ".join(capsys.readouterr().out.split())
        for topic in TOPICS:
            assert topic in out
        assert "stdlib module" in out
