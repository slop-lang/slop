"""
SLOP MCP server: `slop mcp`.

Serves the Model Context Protocol on stdio (newline-delimited JSON-RPC 2.0,
UTF-8), so a coding agent can call SLOP's tools directly:

  ref     the language reference, by topic, or a stdlib module's API
  doc     a module's API: types, functions and their contracts
  check   the native checker's diagnostics for a file or unsaved source
  format  the canonical layout, for source text or a file in place

Each tool runs the code its CLI command runs, so the two cannot drift. Only
the standard library is used: the server ships wherever the CLI does, and the
Homebrew formula installs no other Python package.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import traceback
from pathlib import Path
from typing import Callable, Dict, List, Optional, Tuple

from slop import __version__, paths

# Newest first; an unknown requested version is answered with the newest
PROTOCOL_VERSIONS = ("2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05")

# Sent to the client at initialize; clients add it to the agent's context
INSTRUCTIONS = (
    "Tools for the SLOP language (.slop files). Before writing a SLOP form you "
    "are unsure of, call `ref` (with no topic it lists the topics; `mistakes` "
    "lists forms that do not exist in SLOP and what to use instead). Before "
    "calling a standard-library function, call `doc` with its module. After "
    "editing a .slop file, call `check` on it and fix every error before moving "
    "on. `format` rewrites a file in the canonical layout."
)

PARSE_ERROR = -32700
INVALID_REQUEST = -32600
METHOD_NOT_FOUND = -32601
INVALID_PARAMS = -32602


class ToolError(Exception):
    """The tool could not do what it was asked. Reported to the agent as a
    tool result with isError, so it can correct the call."""


# ---------------------------------------------------------------------------
# Tools
# ---------------------------------------------------------------------------

def _topic_heading(topic: str) -> str:
    from slop.reference import TOPICS
    first = TOPICS[topic].splitlines()[0]
    return first.lstrip('#').strip()


def _ref_index() -> str:
    from slop.reference import TOPIC_ORDER
    width = max(len(t) for t in TOPIC_ORDER)
    lines = ["SLOP language reference. Call `ref` with a topic:", ""]
    for topic in TOPIC_ORDER:
        lines.append(f"  {topic:<{width}}  {_topic_heading(topic)}")
    lines.append(f"  {'all':<{width}}  Every topic above, in one document (long)")
    modules = sorted(p.stem for p in paths.list_stdlib_modules())
    if modules:
        lines += [
            "",
            "Standard library modules (call `ref` or `doc` with one for its API; "
            "the `stdlib` topic describes each):",
            "",
            "  " + ", ".join(modules),
        ]
    return "\n".join(lines)


def _module_doc(path: Path) -> dict:
    from slop.cli import extract_documentation
    from slop.parser import parse_file, ParseError
    try:
        return extract_documentation(parse_file(str(path)))
    except ParseError as e:
        raise ToolError(f"{path}: {e}")
    except OSError as e:
        raise ToolError(f"Cannot read {path}: {e.strerror or e}")


def tool_ref(args: dict) -> str:
    from slop.cli import render_markdown
    from slop.reference import TOPICS, get_reference
    topic = args.get("topic") or ""
    if not topic:
        return _ref_index()
    if topic == "all":
        return get_reference("all")
    if topic in TOPICS:
        return TOPICS[topic]
    module = paths.find_stdlib_module(topic)
    if module:
        return render_markdown(_module_doc(module))
    raise ToolError(f"Unknown topic: {topic}\n\n{_ref_index()}")


def _only_symbol(doc: dict, symbol: str) -> dict:
    """The doc with only the entries named `symbol`; ToolError if none are."""
    kept = dict(doc)
    found = False
    for key in ('types', 'functions', 'constants', 'ffi_structs'):
        kept[key] = [e for e in doc[key] if e['name'] == symbol]
        found = found or bool(kept[key])
    kept['ffi'] = []
    for block in doc['ffi']:
        functions = [f for f in block['functions'] if f['name'] == symbol]
        constants = [c for c in block['constants'] if c['name'] == symbol]
        if functions or constants:
            kept['ffi'].append(dict(block, functions=functions, constants=constants))
            found = True
    if not found:
        names = sorted({e['name'] for key in ('types', 'functions', 'constants', 'ffi_structs')
                        for e in doc[key] if e.get('exported', True)}
                       | {e['name'] for block in doc['ffi']
                          for e in block['functions'] + block['constants']
                          if e.get('exported', True)})
        raise ToolError(f"{doc['module'] or 'The module'} has no {symbol!r}. "
                        f"It defines: {', '.join(names) or '(nothing exported)'}")
    return kept


def tool_doc(args: dict) -> str:
    from slop.cli import render_markdown
    module = args["module"]
    path = Path(module).expanduser()
    if not path.is_file():
        found = paths.find_stdlib_module(module)
        if not found:
            modules = ", ".join(sorted(p.stem for p in paths.list_stdlib_modules()))
            raise ToolError(f"No file {module!r} (relative to {Path.cwd()}) and no "
                            f"standard library module of that name. Modules: {modules}")
        path = found
    doc = _module_doc(path)
    if args.get("symbol"):
        doc = _only_symbol(doc, args["symbol"])
    if args.get("format") == "json":
        return json.dumps(doc, indent=2)
    return render_markdown(doc)


_MODULE_RE = re.compile(r'^\s*\(module\s+([^\s()]+)', re.MULTILINE)
_DIAGNOSTIC_RE = re.compile(r'^(.*):(\d+):(\d+): (error|warning): (.*)$')


def _module_name(text: str) -> Optional[str]:
    m = _MODULE_RE.search(text)
    return m.group(1) if m else None


def _read_text(path) -> str:
    try:
        return Path(path).read_text(encoding='utf-8', errors='replace')
    except OSError:
        return ''


def _under(path: Path, root: Optional[Path]) -> bool:
    if root is None:
        return False
    try:
        path.resolve().relative_to(root.resolve())
        return True
    except ValueError:
        return False


def _shown(path_str: str, aliases: Dict[str, str]) -> str:
    """A path as the agent should see it: an alias, else relative to the cwd
    when it is under it."""
    if path_str in aliases:
        return aliases[path_str]
    path = Path(path_str)
    try:
        return str(path.resolve().relative_to(Path.cwd().resolve()))
    except (ValueError, OSError):
        return path_str


def read_check_output(text: str):
    """Read `check --json` output as ([(module, entry)], [error lines]).

    The output is one JSON object keyed by module name, but a file that
    cannot be read or parsed gets a line of text (`file:line:col: error: ...`
    or `Error: ...`) in place of its entry, in the middle of the object, and
    the entries around it are still written. Returns None if the output is
    not that object.
    """
    decoder = json.JSONDecoder(strict=False)
    entries: List[Tuple[str, object]] = []
    errors: List[str] = []
    i = len(text) - len(text.lstrip())
    if text[i:i + 1] != '{':
        return None
    i += 1
    n = len(text)
    while i < n:
        c = text[i]
        if c in ' \t\r\n,':
            i += 1
        elif c == '}':
            i += 1
            break
        elif c == '"':
            try:
                module, i = decoder.raw_decode(text, i)
                while i < n and text[i] in ' \t\r\n':
                    i += 1
                if text[i:i + 1] != ':':
                    return None
                i += 1
                while i < n and text[i] in ' \t\r\n':
                    i += 1
                entry, i = decoder.raw_decode(text, i)
            except ValueError:
                return None
            entries.append((module, entry))
        else:
            end = text.find('\n', i)
            end = n if end < 0 else end
            errors.append(text[i:end].strip())
            i = end + 1
    errors += [line.strip() for line in text[i:].splitlines() if line.strip()]
    return entries, errors


def _run_check(target: Path, include: List[str], aliases: Dict[str, str]) -> str:
    from slop.cli import find_native_component, resolve_check_files
    from slop.parser import ParseError
    compiler = find_native_component('compiler')
    checker = compiler or find_native_component('checker')
    if not checker:
        raise ToolError("Native SLOP compiler not found. Build it with "
                        "`make build-native`, or set SLOP_HOME to a SLOP install.")
    cmd = [str(checker)] + (['check'] if compiler else []) + ['--json']
    files, resolve_error = resolve_check_files(str(target), include)
    # stdin is the protocol stream: never let the tool read it
    result = subprocess.run(cmd + files, capture_output=True, text=True,
                            encoding='utf-8', errors='replace',
                            stdin=subprocess.DEVNULL)
    read = read_check_output(result.stdout)
    if read is None:
        raise ToolError(f"The checker exited with status {result.returncode} "
                        f"and its output was not understood.\n"
                        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}")
    entries, error_lines = read

    # The JSON is keyed by module name, `unknown` for a file without a
    # (module ...) form; map each back to its file
    file_of: Dict[str, str] = {}
    for f in files:
        file_of.setdefault(_module_name(_read_text(f)) or 'unknown', f)
    order = {f: i for i, f in enumerate(reversed(files))}   # the target first
    stdlib = paths.get_stdlib_dir()

    diagnostics: List[Tuple[str, int, int, str, str]] = []
    hidden = 0
    for module, entry in entries:
        file = file_of.get(module, module)
        for d in (entry.get('diagnostics', []) if isinstance(entry, dict) else []):
            level = d.get('level', 'error')
            if level == 'warning' and _under(Path(file), stdlib):
                hidden += 1
                continue
            diagnostics.append((file, d.get('line', 0), d.get('col', 0),
                                level, d.get('message', '')))
    parse_failed = bool(error_lines)
    for line in error_lines:
        d = _DIAGNOSTIC_RE.match(line)
        if d:
            diagnostics.append((d.group(1), int(d.group(2)), int(d.group(3)),
                                d.group(4), d.group(5)))
        else:
            diagnostics.append(('', 0, 0, 'error', line))
    # An imported module that does not parse stops the import resolution, and
    # the checker then sees the file alone; say why
    if resolve_error is not None:
        cause = resolve_error.__cause__
        if isinstance(cause, ParseError) and cause.path:
            diagnostics.append((cause.path, cause.line, cause.col, 'error', cause.message))
            parse_failed = True
        else:
            diagnostics.append(('', 0, 0, 'error', f"cannot resolve the imports: {resolve_error}"))

    errors = sum(1 for d in diagnostics if d[3] == 'error')
    warnings = len(diagnostics) - errors
    if result.returncode != 0 and errors == 0:
        raise ToolError(f"The checker exited with status {result.returncode} "
                        f"without reporting an error.\nstderr:\n{result.stderr}")

    diagnostics.sort(key=lambda d: (order.get(d[0], len(order)), d[1], d[2]))
    lines = []
    for file, line, col, level, message in diagnostics:
        where = f"{_shown(file, aliases)}:{line}:{col}: " if file else ""
        lines.append(f"{where}{level}: {message}")
    if not diagnostics:
        summary = "OK: no errors or warnings"
    else:
        summary = (f"{errors} error{'s' if errors != 1 else ''}, "
                   f"{warnings} warning{'s' if warnings != 1 else ''}")
    if parse_failed:
        summary += (". A file did not parse, so the type check is incomplete; "
                    "fix the parse error and check again")
    if hidden:
        summary += f" ({hidden} warning{'s' if hidden != 1 else ''} in standard library modules not shown)"
    lines.append(summary)
    return "\n".join(lines)


def _one_of(args: dict, *names: str) -> str:
    given = [n for n in names if args.get(n) is not None]
    if len(given) != 1:
        raise ToolError(f"Pass exactly one of: {', '.join(names)}.")
    return given[0]


def tool_check(args: dict) -> str:
    include = args.get("include") or []
    if _one_of(args, "path", "source") == "source":
        source = args["source"]
        name = re.sub(r'[^A-Za-z0-9_.-]', '_', _module_name(source) or 'snippet')
        with tempfile.TemporaryDirectory(prefix='slop-mcp-') as tmp:
            target = (Path(tmp) / f"{name}.slop").resolve()
            with open(target, 'w', encoding='utf-8', newline='') as f:
                f.write(source)
            from slop.cli import _native_path
            aliases = {str(target): '<source>', _native_path(target): '<source>'}
            return _run_check(target, include, aliases)
    target = Path(args["path"]).expanduser()
    if not target.is_file():
        raise ToolError(f"No such file: {args['path']} (relative to {Path.cwd()})")
    return _run_check(target, include, {})


def _replace_file(path: Path, text: str) -> None:
    """Write `text` to `path` as UTF-8, all or nothing: into a temporary file
    beside it, then renamed over it, keeping its permissions."""
    real = path.resolve()
    fd, tmp = tempfile.mkstemp(dir=real.parent, prefix=f".{real.name}.", suffix=".tmp")
    try:
        with os.fdopen(fd, 'w', encoding='utf-8', newline='') as f:
            f.write(text)
        shutil.copymode(real, tmp)
        os.replace(tmp, real)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def tool_format(args: dict) -> str:
    from slop.formatter import format_source, FormatError
    from slop.parser import ParseError
    check = bool(args.get("check"))
    try:
        if _one_of(args, "path", "source") == "source":
            formatted = format_source(args["source"])
            if check:
                return ("already formatted" if formatted == args["source"]
                        else "needs formatting")
            return formatted
        path = Path(args["path"]).expanduser()
        if not path.is_file():
            raise ToolError(f"No such file: {args['path']} (relative to {Path.cwd()})")
        # SLOP source is UTF-8, whatever the locale. newline='' both ways, as
        # `slop format` does, so CRLF and a \r in a string literal are
        # written back as they were read.
        with open(path, encoding='utf-8', newline='') as f:
            source = f.read()
        formatted = format_source(source)
    except (ParseError, FormatError) as e:
        raise ToolError(str(e))
    except UnicodeDecodeError:
        raise ToolError(f"{args['path']} is not UTF-8 text, so it was left as it is.")
    except OSError as e:
        raise ToolError(f"Cannot read {args.get('path')}: {e.strerror or e}")
    if source == formatted:
        return f"{args['path']}: already formatted"
    if check:
        return f"{args['path']}: needs formatting"
    try:
        _replace_file(path, formatted)
    except OSError as e:
        raise ToolError(f"Cannot write {args['path']}: {e.strerror or e}; it was left as it was.")
    return f"{args['path']}: formatted"


def _ref_description() -> str:
    from slop.reference import TOPIC_ORDER
    return (
        "SLOP language reference. With no topic, lists the topics and the "
        "standard library modules. A topic (" + ", ".join(TOPIC_ORDER) + ") "
        "returns that section; `mistakes` lists forms that do not exist in SLOP "
        "and what to use instead. A standard library module name (e.g. strlib) "
        "returns that module's API. `all` returns every topic (long)."
    )


TOOLS = [
    {
        "name": "ref",
        "title": "SLOP language reference",
        "description": _ref_description,
        "inputSchema": {
            "type": "object",
            "properties": {
                "topic": {"type": "string",
                          "description": "A topic, a standard library module, or `all`. "
                                         "Omit it to list them."},
            },
            "additionalProperties": False,
        },
        "annotations": {"readOnlyHint": True, "openWorldHint": False},
        "handler": tool_ref,
    },
    {
        "name": "doc",
        "title": "SLOP module documentation",
        "description": (
            "API documentation for a SLOP module: its types, functions (parameters, "
            "@spec, @pre/@post, examples) and constants. `module` is a standard "
            "library module name (strlib, json, mathlib, ...) or the path of a .slop "
            "file, relative to the project directory. Give `symbol` to get one "
            "function or type rather than the whole module."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "module": {"type": "string",
                           "description": "Standard library module name, or path to a .slop file."},
                "symbol": {"type": "string",
                           "description": "Only this function, type or constant."},
                "format": {"type": "string", "enum": ["markdown", "json"],
                           "description": "Output format (default markdown)."},
            },
            "required": ["module"],
            "additionalProperties": False,
        },
        "annotations": {"readOnlyHint": True, "openWorldHint": False},
        "handler": tool_doc,
    },
    {
        "name": "check",
        "title": "Type-check SLOP",
        "description": (
            "Type-check SLOP with the native checker and return its diagnostics, one "
            "`file:line:col: level: message` line each, then a summary. Modules the "
            "file imports are checked too. Pass `path` for a file (relative to the "
            "project directory), or `source` for unsaved code, which can import "
            "standard library modules but not other project modules. A parse error, "
            "such as an unbalanced parenthesis, is reported at the list that never "
            "closed, and stops the check."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string", "description": "A .slop file to check."},
                "source": {"type": "string", "description": "SLOP source to check instead of a file."},
                "include": {"type": "array", "items": {"type": "string"},
                            "description": "Extra directories to search for imported modules."},
            },
            "additionalProperties": False,
        },
        "annotations": {"readOnlyHint": True, "openWorldHint": False},
        "handler": tool_check,
    },
    {
        "name": "format",
        "title": "Format SLOP",
        "description": (
            "Format SLOP in the canonical layout; comments are kept. `source` returns "
            "the formatted text. `path` rewrites that file in place; with `check: "
            "true` it only reports whether the file needs formatting."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string", "description": "A .slop file to format in place."},
                "source": {"type": "string", "description": "SLOP source to format."},
                "check": {"type": "boolean",
                          "description": "Only report whether formatting would change anything."},
            },
            "additionalProperties": False,
        },
        "annotations": {"readOnlyHint": False, "destructiveHint": False,
                        "idempotentHint": True, "openWorldHint": False},
        "handler": tool_format,
    },
]

_TOOLS_BY_NAME = {t["name"]: t for t in TOOLS}

_JSON_TYPES = {"string": str, "boolean": bool, "object": dict}


def _validate(tool: dict, args) -> dict:
    """Check arguments against the tool's input schema (the subset it uses)."""
    if args is None:
        args = {}
    if not isinstance(args, dict):
        raise ToolError("Arguments must be an object.")
    schema = tool["inputSchema"]
    props = schema["properties"]
    unknown = sorted(set(args) - set(props))
    if unknown:
        raise ToolError(f"Unknown argument{'s' if len(unknown) > 1 else ''}: "
                        f"{', '.join(unknown)}. `{tool['name']}` takes: {', '.join(props)}.")
    for name in schema.get("required", []):
        if args.get(name) is None:
            raise ToolError(f"Missing required argument: {name}.")
    for name, value in args.items():
        if value is None:
            continue
        spec = props[name]
        if spec["type"] == "array":
            if not (isinstance(value, list) and all(isinstance(v, str) for v in value)):
                raise ToolError(f"`{name}` must be a list of strings.")
        elif not isinstance(value, _JSON_TYPES[spec["type"]]):
            raise ToolError(f"`{name}` must be a {spec['type']}.")
        if "enum" in spec and value not in spec["enum"]:
            raise ToolError(f"`{name}` must be one of: {', '.join(spec['enum'])}.")
    return args


def tool_list() -> List[dict]:
    listed = []
    for tool in TOOLS:
        entry = {k: v for k, v in tool.items() if k != "handler"}
        if callable(entry["description"]):
            entry["description"] = entry["description"]()
        listed.append(entry)
    return listed


# ---------------------------------------------------------------------------
# Protocol
# ---------------------------------------------------------------------------

class ProtocolError(Exception):
    def __init__(self, code: int, message: str):
        super().__init__(message)
        self.code = code


def _error(id_, code: int, message: str) -> dict:
    return {"jsonrpc": "2.0", "id": id_, "error": {"code": code, "message": message}}


def _initialize(params: dict) -> dict:
    requested = params.get("protocolVersion")
    if not isinstance(requested, str):
        raise ProtocolError(INVALID_PARAMS, "initialize needs a protocolVersion string")
    version = requested if requested in PROTOCOL_VERSIONS else PROTOCOL_VERSIONS[0]
    return {
        "protocolVersion": version,
        "capabilities": {"tools": {"listChanged": False}},
        "serverInfo": {"name": "slop", "title": "SLOP", "version": __version__},
        "instructions": INSTRUCTIONS,
    }


def _call_tool(params: dict) -> dict:
    name = params.get("name")
    tool = _TOOLS_BY_NAME.get(name) if isinstance(name, str) else None
    if tool is None:
        raise ProtocolError(INVALID_PARAMS, f"Unknown tool: {name}")
    try:
        text = tool["handler"](_validate(tool, params.get("arguments")))
        is_error = False
    except ToolError as e:
        text, is_error = str(e), True
    except Exception as e:
        traceback.print_exc(file=sys.stderr)
        text, is_error = f"Internal error in `{name}`: {type(e).__name__}: {e}", True
    return {"content": [{"type": "text", "text": text}], "isError": is_error}


_METHODS: Dict[str, Callable[[dict], dict]] = {
    "initialize": _initialize,
    "ping": lambda params: {},
    "tools/list": lambda params: {"tools": tool_list()},
    "tools/call": _call_tool,
}


def _valid_id(id_) -> bool:
    """MCP request ids are strings or integers."""
    return isinstance(id_, str) or (isinstance(id_, int) and not isinstance(id_, bool))


def handle_message(msg) -> Optional[dict]:
    """The reply to one JSON-RPC message, or None for a notification or a
    response (this server sends no requests)."""
    if not isinstance(msg, dict):
        return _error(None, INVALID_REQUEST, "Invalid Request")
    has_id = "id" in msg
    # An id that cannot be used is answered with null, as JSON-RPC asks
    id_ = msg["id"] if has_id and _valid_id(msg["id"]) else None
    if msg.get("jsonrpc") != "2.0":
        return _error(id_, INVALID_REQUEST, "Invalid Request")
    if "method" not in msg:
        if has_id and ("result" in msg or "error" in msg):
            return None                 # a response; this server sends no requests
        return _error(id_, INVALID_REQUEST, "Invalid Request")
    method = msg["method"]
    if not isinstance(method, str) or (has_id and id_ is None):
        return _error(id_, INVALID_REQUEST, "Invalid Request")
    if not has_id:
        return None                     # a notification
    handler = _METHODS.get(method)
    if handler is None:
        return _error(id_, METHOD_NOT_FOUND, f"Method not found: {method}")
    params = msg.get("params")
    if params is None:
        params = {}
    if not isinstance(params, dict):
        return _error(id_, INVALID_PARAMS, "params must be an object")
    try:
        return {"jsonrpc": "2.0", "id": id_, "result": handler(params)}
    except ProtocolError as e:
        return _error(id_, e.code, str(e))


def handle_line(line: bytes) -> Optional[object]:
    """The reply to one line of input, or None if nothing is owed."""
    try:
        msg = json.loads(line.decode('utf-8'))
    except (UnicodeDecodeError, ValueError):
        return _error(None, PARSE_ERROR, "Parse error")
    if isinstance(msg, list):
        if not msg:
            return _error(None, INVALID_REQUEST, "Invalid Request")
        replies = [r for r in (handle_message(m) for m in msg) if r is not None]
        return replies or None
    return handle_message(msg)


def serve(instream, outstream) -> int:
    """Answer messages from `instream` (binary, one JSON-RPC message per line)
    on `outstream` (binary) until end of input."""
    for raw in instream:
        line = raw.strip()
        if not line:
            continue
        reply = handle_line(line)
        if reply is not None:
            outstream.write(json.dumps(reply).encode('utf-8') + b'\n')
            outstream.flush()
    return 0


def main() -> int:
    # Keep fd 1 for protocol messages alone. Anything else that writes to it,
    # a print or a native tool, would corrupt the stream, so from here on
    # fd 1 and sys.stdout are stderr, and messages go to a private copy.
    sys.stdout.flush()
    protocol_fd = os.dup(1)
    os.dup2(2, 1)
    sys.stdout = sys.stderr
    with os.fdopen(protocol_fd, 'wb') as out:
        try:
            return serve(sys.stdin.buffer, out)
        except KeyboardInterrupt:
            return 0
