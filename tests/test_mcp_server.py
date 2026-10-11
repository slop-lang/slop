"""
Tests for `slop mcp`, the MCP server in src/slop/mcp_server.py.

The protocol tests drive a real server process over its stdio, as an MCP
client does. The tool tests call handle_message in-process, which runs the
same validation and dispatch. check runs this checkout's bin/slop-compiler
and is skipped when it is missing.
"""

import json
import os
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

from slop import __version__, cli, mcp_server
from slop.formatter import format_source
from slop.reference import TOPICS, TOPIC_ORDER

REPO_ROOT = Path(__file__).parent.parent

needs_compiler = pytest.mark.skipif(
    not (REPO_ROOT / "bin" / "slop-compiler").exists(),
    reason="bin/slop-compiler not built (make install)")


@pytest.fixture(autouse=True)
def repo_slop_home(monkeypatch):
    """Resolve native binaries and the stdlib from this checkout."""
    monkeypatch.setenv("SLOP_HOME", str(REPO_ROOT))


def request(id_, method, params=None):
    msg = {"jsonrpc": "2.0", "id": id_, "method": method}
    if params is not None:
        msg["params"] = params
    return msg


def session(*messages, raw_lines=(), code=None):
    """Run a server, send it `messages` (and any `raw_lines`), close its
    input, and return its replies. Every line it writes to stdout must be a
    JSON-RPC message."""
    lines = [json.dumps(m) for m in messages] + list(raw_lines)
    argv = ([sys.executable, "-c", code] if code
            else [sys.executable, "-m", "slop.cli", "mcp"])
    proc = subprocess.run(argv, input=("\n".join(lines) + "\n").encode("utf-8"),
                          capture_output=True, cwd=REPO_ROOT, timeout=120,
                          env=dict(os.environ, SLOP_HOME=str(REPO_ROOT)))
    assert proc.returncode == 0, proc.stderr.decode()
    replies = [json.loads(line) for line in proc.stdout.decode("utf-8").splitlines()]
    return replies, proc.stderr.decode("utf-8")


def call(name, **arguments):
    """Call a tool in-process; returns (text, isError)."""
    reply = mcp_server.handle_message(
        request(1, "tools/call", {"name": name, "arguments": arguments}))
    result = reply["result"]
    [content] = result["content"]
    assert content["type"] == "text"
    return content["text"], result["isError"]


INITIALIZE = {"protocolVersion": "2025-06-18", "capabilities": {},
              "clientInfo": {"name": "test", "version": "0"}}


class TestProtocol:
    def test_initialize_and_list_tools(self):
        replies, _ = session(
            request(1, "initialize", INITIALIZE),
            {"jsonrpc": "2.0", "method": "notifications/initialized"},
            request(2, "tools/list"))
        assert [r["id"] for r in replies] == [1, 2]
        init = replies[0]["result"]
        assert init["protocolVersion"] == "2025-06-18"
        assert init["serverInfo"]["version"] == __version__
        assert init["capabilities"] == {"tools": {"listChanged": False}}
        assert "`check`" in init["instructions"]

        tools = replies[1]["result"]["tools"]
        assert [t["name"] for t in tools] == ["ref", "doc", "check", "format"]
        for tool in tools:
            assert isinstance(tool["description"], str) and tool["description"]
            assert tool["inputSchema"]["type"] == "object"
            assert "handler" not in tool
        # The ref description names every topic
        assert all(t in tools[0]["description"] for t in TOPIC_ORDER)

    def test_unknown_protocol_version_gets_the_newest(self):
        replies, _ = session(request(1, "initialize", dict(INITIALIZE, protocolVersion="1999-01-01")))
        assert replies[0]["result"]["protocolVersion"] == mcp_server.PROTOCOL_VERSIONS[0]

    def test_notifications_and_responses_get_no_reply(self):
        replies, _ = session(
            {"jsonrpc": "2.0", "method": "notifications/cancelled", "params": {"requestId": 9}},
            {"jsonrpc": "2.0", "id": 7, "result": {}},
            request(2, "ping"))
        assert replies == [{"jsonrpc": "2.0", "id": 2, "result": {}}]

    def test_errors(self):
        replies, _ = session(
            request(1, "resources/list"),
            request(2, "tools/call", {"name": "lint", "arguments": {}}),
            {"jsonrpc": "1.0", "id": 3, "method": "ping"},
            request(4, "initialize", dict(INITIALIZE, protocolVersion=20250618)),
            {"jsonrpc": "2.0", "method": 42},
            {"jsonrpc": "2.0", "id": {}, "method": "ping"},
            {"jsonrpc": "2.0", "id": True, "method": "ping"},
            request(5, "initialize", dict(INITIALIZE, capabilities=42)),
            request(6, "initialize", {"protocolVersion": "2025-06-18", "capabilities": {}}),
            raw_lines=["not json", '{"jsonrpc":"2.0","id":7,"method":"ping","params":{"x":NaN}}'])
        assert [(r["id"], r["error"]["code"]) for r in replies] == [
            (1, -32601), (2, -32602), (3, -32600), (4, -32602),
            (None, -32600), (None, -32600), (None, -32600), (5, -32602), (6, -32602),
            (None, -32700), (None, -32700)]

    def test_batch(self):
        replies, _ = session([request(1, "ping"),
                              {"jsonrpc": "2.0", "method": "notifications/initialized"},
                              request(2, "ping")])
        assert replies == [[{"jsonrpc": "2.0", "id": 1, "result": {}},
                            {"jsonrpc": "2.0", "id": 2, "result": {}}]]

    def test_stdout_carries_only_protocol_messages(self):
        # A tool that prints, and runs a child that writes to fd 1: both must
        # land on stderr, not in the protocol stream
        code = textwrap.dedent("""\
            import subprocess, sys
            from slop import mcp_server

            def noisy(args):
                print("print noise")
                subprocess.run([sys.executable, "-c", "print('child noise')"],
                               stdin=subprocess.DEVNULL)
                return "done"

            mcp_server._TOOLS_BY_NAME["noisy"] = {
                "name": "noisy", "inputSchema": {"type": "object", "properties": {}},
                "handler": noisy}
            sys.exit(mcp_server.main())
            """)
        replies, stderr = session(request(1, "tools/call", {"name": "noisy", "arguments": {}}),
                                  code=code)
        assert replies[0]["result"]["content"][0]["text"] == "done"
        assert "print noise" in stderr and "child noise" in stderr


class TestRef:
    def test_no_topic_lists_topics_and_modules(self):
        text, is_error = call("ref")
        assert not is_error
        for topic in TOPIC_ORDER:
            assert f"  {topic} " in text
        assert "strlib" in text and "mathlib" in text

    def test_topic(self):
        assert call("ref", topic="mistakes") == (TOPICS["mistakes"], False)

    def test_stdlib_module_by_name_or_directory(self):
        text, is_error = call("ref", topic="strlib")
        assert not is_error and text.startswith("# strlib")
        text, is_error = call("ref", topic="math")
        assert not is_error and text.startswith("# mathlib")

    def test_unknown_topic(self):
        text, is_error = call("ref", topic="generics")
        assert is_error
        assert text.startswith("Unknown topic: generics")
        assert "mistakes" in text


DOC_MODULE = """\
(module docmod
  (export shout)

  (fn shout ((s String))
    (@intent "Upper-case a string")
    (@spec ((String) -> String))
    (@pre (> (string-len s) 0))
    s)

  (fn helper ((x Int))
    (@intent "Internal")
    (@spec ((Int) -> Int))
    x))
"""


class TestDoc:
    def test_one_symbol(self):
        text, is_error = call("doc", module="strlib", symbol="trim")
        assert not is_error
        assert "### trim" in text
        assert "### to-upper" not in text

    def test_directory_name_resolves(self):
        text, is_error = call("doc", module="math", symbol="sqrt")
        assert not is_error and "### sqrt" in text

    def test_unknown_symbol_lists_the_exports(self):
        text, is_error = call("doc", module="strlib", symbol="string-trim")
        assert is_error
        assert "strlib has no 'string-trim'" in text
        assert "trim" in text.split("It defines:")[1]

    def test_json(self):
        text, is_error = call("doc", module="strlib", format="json")
        assert not is_error and json.loads(text)["module"] == "strlib"

    def test_path_relative_to_cwd(self, tmp_path, monkeypatch):
        (tmp_path / "docmod.slop").write_text(DOC_MODULE)
        monkeypatch.chdir(tmp_path)
        text, is_error = call("doc", module="docmod.slop", symbol="shout")
        assert not is_error
        assert "(> (string-len s) 0)" in text and "### helper" not in text
        # helper is not exported, so the unknown-symbol hint leaves it out
        text, is_error = call("doc", module="docmod.slop", symbol="nope")
        assert is_error and text.endswith("It defines: shout")

    def test_file_that_does_not_parse(self, tmp_path, monkeypatch):
        (tmp_path / "m.slop").write_text("(module m (fn f")
        monkeypatch.chdir(tmp_path)
        assert call("doc", module="m.slop") == ("m.slop:1:11: error: Unclosed list", True)

    def test_bad_arguments(self):
        text, is_error = call("doc", module="no-such-module")
        assert is_error and "no standard library module" in text
        text, is_error = call("doc")
        assert is_error and "Missing required argument: module" in text
        text, is_error = call("doc", module="strlib", colour="red")
        assert is_error and text.startswith("Unknown argument: colour.")
        text, is_error = call("doc", module="strlib", format="html")
        assert is_error and "must be one of: markdown, json" in text


GOOD = """\
(module good
  (fn f ((x Int))
    (@intent "Add one")
    (@spec ((Int) -> Int))
    (+ x 1)))
"""

BAD = """\
(module bad
  (fn f ((x Int))
    (@intent "Mixed types")
    (@spec ((Int) -> String))
    (+ x "a")))
"""

UNCLOSED = """\
(module unclosed
  (fn f ((x Int))
    (@intent "Add one")
    (@spec ((Int) -> Int))
    (+ x 1)
"""

STRAY = """\
(module stray
  (fn f ((x Int))
    (@intent "Identity")
    (@spec ((Int) -> Int))
    x)))
"""

APP = """\
(module app
  (import helper (twice))
  (fn main ()
    (@intent "Entry")
    (@spec (() -> Int))
    (twice 2)))
"""

HELPER = """\
(module helper
  (export twice)
  (fn twice ((x Int))
    (@intent "Double")
    (@spec ((Int) -> String))
    (* x 2)))
"""

BROKEN_HELPER = """\
(module helper
  (export twice)
  (fn twice ((x Int))
    (@intent "Double")
    (@spec ((Int) -> Int))
    (* x 2.0f)))
"""

NO_MODULE = """\
(fn f ((x Int))
  (@intent "Mixed types")
  (@spec ((Int) -> String))
  (+ x "a"))
"""

FIRST_FORM_NOT_A_MODULE = """\
(@generation-mode deterministic)
(module nested
  (fn f ((x Int))
    (@intent "Mixed types")
    (@spec ((Int) -> String))
    (+ x "a")))
"""

LOOSE_APP = """\
(import loose-helper (g))
(fn f ((x Int))
  (@intent "Mixed types")
  (@spec ((Int) -> String))
  (+ x "a"))
"""

LOOSE_HELPER = """\
(fn g ((x Int))
  (@intent "Wrong result type")
  (@spec ((Int) -> String))
  x)
"""

USES_XML = """\
(module uses-xml
  (import xml (xml-parse))
  (fn f ((x Int))
    (@intent "Identity")
    (@spec ((Int) -> Int))
    x))
"""


@pytest.fixture
def project(tmp_path, monkeypatch):
    for name, text in (("good", GOOD), ("bad", BAD), ("unclosed", UNCLOSED),
                       ("stray", STRAY), ("app", APP), ("helper", HELPER)):
        (tmp_path / f"{name}.slop").write_text(text)
    monkeypatch.chdir(tmp_path)
    return tmp_path


@needs_compiler
class TestCheck:
    def test_clean(self, project):
        assert call("check", path="good.slop") == ("OK: no errors or warnings", False)

    def test_errors_are_sorted_with_relative_paths(self, project):
        text, is_error = call("check", path="bad.slop")
        assert not is_error
        lines = text.splitlines()
        assert lines[0].startswith("bad.slop:2:3: error: return value of 'f'")
        assert lines[1].startswith("bad.slop:5:10: error: '+' needs a numeric operand")
        assert lines[2] == "2 errors, 0 warnings"

    def test_unclosed_list_is_reported_at_the_form_left_open(self, project):
        text, is_error = call("check", path="unclosed.slop")
        assert not is_error
        assert text.startswith("unclosed.slop:2:3: error: Unterminated list")
        assert "did not parse" in text

    def test_stray_close_paren(self, project):
        text, _ = call("check", path="stray.slop")
        assert text.startswith("stray.slop:5:8: error: Unexpected token")

    def test_imported_module_errors_name_their_file(self, project):
        text, _ = call("check", path="app.slop")
        lines = text.splitlines()
        # The file asked about comes first
        assert lines[0].startswith("app.slop:3:3: error:")
        assert lines[1].startswith("helper.slop:3:3: error: return value of 'twice'")

    def test_imported_module_that_does_not_parse(self, project):
        # The import resolution stops at it, and the checker sees app alone;
        # the parse error has to be reported, not just what follows from it
        (project / "helper.slop").write_text(BROKEN_HELPER)
        text, _ = call("check", path="app.slop")
        assert "helper.slop:6:10: error: invalid number literal" in text
        assert "A file did not parse" in text.splitlines()[-1]

    def test_file_without_a_module_form(self, project):
        # The checker keys its diagnostics `unknown`
        (project / "loose.slop").write_text(NO_MODULE)
        text, _ = call("check", path="loose.slop")
        assert "loose.slop:4:8: error: '+' needs a numeric operand" in text
        assert "unknown" not in text

    def test_first_form_not_a_module(self, project):
        # The checker keys it `unknown` too, though a module form follows
        (project / "nested.slop").write_text(FIRST_FORM_NOT_A_MODULE)
        text, _ = call("check", path="nested.slop")
        assert "nested.slop:6:10: error: '+' needs a numeric operand" in text
        assert "unknown" not in text

    def test_two_files_without_a_module_form(self, project):
        # Both are keyed `unknown`; each diagnostic still names its own file
        (project / "loose-app.slop").write_text(LOOSE_APP)
        (project / "loose-helper.slop").write_text(LOOSE_HELPER)
        text, _ = call("check", path="loose-app.slop")
        assert "loose-app.slop:5:8: error: '+' needs a numeric operand" in text
        assert "loose-helper.slop:" in text and "return value of 'g'" in text
        for line in text.splitlines()[:-1]:
            assert ("return value of 'g'" in line) == line.startswith("loose-helper.slop:")

    @pytest.mark.skipif(os.name == "nt" or os.geteuid() == 0,
                        reason="POSIX permissions, and root reads anything")
    def test_file_the_checker_cannot_open(self, project):
        (project / "good.slop").chmod(0)
        try:
            text, is_error = call("check", path="good.slop")
        finally:
            (project / "good.slop").chmod(0o644)
        assert not is_error
        assert text.splitlines()[0].startswith("good.slop: error: Could not open file: ")
        assert "A file could not be read" in text.splitlines()[-1]

    def test_source(self, project):
        text, is_error = call("check", source=BAD)
        assert not is_error
        assert text.splitlines()[0].startswith("<source>:2:3: error:")
        assert call("check", source=GOOD) == ("OK: no errors or warnings", False)

    def test_stdlib_warnings_are_not_shown(self, project):
        text, is_error = call("check", source=USES_XML)
        assert not is_error
        assert text.startswith("OK: no errors or warnings")
        assert "warning:" not in text

    def test_bad_arguments(self, project):
        text, is_error = call("check", path="good.slop", source=GOOD)
        assert is_error and text == "Pass exactly one of: path, source."
        text, is_error = call("check", path="missing.slop")
        assert is_error and text.startswith("No such file: missing.slop")


def test_check_output_has_one_item_per_file_in_order():
    # What `slop-compiler check --json a.slop b.slop c.slop` prints when b
    # does not parse: b's error line replaces its entry, mid-object
    out = ('{"a":{"diagnostics":[{"level":"error","line":8,"col":10,"message":"m1"}]}'
           'b.slop:7:15: error: invalid number literal\n'
           ',"unknown":{"diagnostics":[]}}\n')
    items = mcp_server.read_check_output(out)
    assert [kind for kind, _ in items] == ["entry", "error", "entry"]
    assert items[0][1][0] == "a" and items[0][1][1]["diagnostics"][0]["message"] == "m1"
    assert items[1][1] == "b.slop:7:15: error: invalid number literal"
    assert items[2][1][0] == "unknown"
    # The last file failing, and a file that cannot be opened
    assert mcp_server.read_check_output('{x.slop:1:1: error: Unterminated list\n}\n') == [
        ("error", "x.slop:1:1: error: Unterminated list")]
    assert mcp_server.read_check_output('{Error: Could not open file: y.slop\n}') == [
        ("error", "Error: Could not open file: y.slop")]
    assert mcp_server.read_check_output("Usage: slop-compiler check ...") is None


def test_check_without_a_native_compiler(monkeypatch, tmp_path):
    monkeypatch.setattr(cli, "find_native_component", lambda name: None)
    text, is_error = call("check", source=GOOD)
    assert is_error and text.startswith("Native SLOP compiler not found")


MESSY = '(module m (fn f ((x Int)) (@intent "i") (@spec ((Int) -> Int)) x))\n'


class TestFormat:
    def test_source(self):
        assert call("format", source=MESSY) == (format_source(MESSY), False)
        assert call("format", source=MESSY, check=True) == ("needs formatting", False)
        tidy = format_source(MESSY)
        assert call("format", source=tidy, check=True) == ("already formatted", False)

    def test_path(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        (tmp_path / "m.slop").write_text(MESSY)
        assert call("format", path="m.slop", check=True) == ("m.slop: needs formatting", False)
        assert (tmp_path / "m.slop").read_text() == MESSY
        assert call("format", path="m.slop") == ("m.slop: formatted", False)
        assert (tmp_path / "m.slop").read_text() == format_source(MESSY)
        assert call("format", path="m.slop") == ("m.slop: already formatted", False)

    def test_crlf_is_kept(self, tmp_path):
        path = tmp_path / "crlf.slop"
        path.write_bytes(MESSY.replace("\n", "\r\n").encode())
        assert not call("format", path=str(path))[1]
        assert b"\r\n" in path.read_bytes() and b"\n" not in path.read_bytes().replace(b"\r\n", b"")

    def test_parse_error(self, tmp_path, monkeypatch):
        # Located as check locates one: the file, or <source>, then line:col
        assert call("format", source="(module m (fn f") == (
            "<source>:1:11: error: Unclosed list", True)
        assert call("format", source="'") == (
            "<source>: error: Unexpected end of input", True)
        monkeypatch.chdir(tmp_path)
        (tmp_path / "m.slop").write_text("(module m (fn f")
        assert call("format", path="m.slop") == ("m.slop:1:11: error: Unclosed list", True)
        assert (tmp_path / "m.slop").read_text() == "(module m (fn f"

    def test_read_and_written_as_utf8(self, tmp_path):
        path = tmp_path / "u.slop"
        path.write_bytes(MESSY.replace('"i"', '"café"').encode("utf-8"))
        assert not call("format", path=str(path))[1]
        assert '"café"' in path.read_bytes().decode("utf-8")
        latin1 = tmp_path / "l.slop"
        latin1.write_bytes(MESSY.replace('"i"', '"café"').encode("latin-1"))
        text, is_error = call("format", path=str(latin1))
        assert is_error and "is not UTF-8" in text
        assert latin1.read_bytes() == MESSY.replace('"i"', '"café"').encode("latin-1")

    def test_failed_write_restores_the_original(self, tmp_path, monkeypatch):
        path = tmp_path / "m.slop"
        path.write_text(MESSY)
        write = mcp_server._write_text
        calls = []

        def fail_first(p, text):
            calls.append(text)
            if len(calls) == 1:
                with open(p, "w") as f:      # stops part way
                    f.write(text[:5])
                raise OSError(28, "No space left on device")
            write(p, text)
        monkeypatch.setattr(mcp_server, "_write_text", fail_first)
        text, is_error = call("format", path=str(path))
        assert is_error
        assert text.endswith("No space left on device; the original was restored.")
        assert path.read_text() == MESSY

    @pytest.mark.skipif(os.name == "nt", reason="POSIX hard links and modes")
    def test_written_in_place(self, tmp_path):
        # The file keeps its inode: a hard link sees the change, and the
        # mode is the file's own
        path, link = tmp_path / "a.slop", tmp_path / "b.slop"
        path.write_text(MESSY)
        path.chmod(0o640)
        os.link(path, link)
        assert not call("format", path=str(path))[1]
        assert link.read_text() == format_source(MESSY)
        assert path.stat().st_mode & 0o777 == 0o640
