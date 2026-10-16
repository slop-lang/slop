#!/usr/bin/env python3
"""Smoke-test a packaged or installed SLOP.

    python scripts/smoke_dist.py <slop command> <a .slop file that checks clean>

Runs the `slop` command (bin/slop, or bin\\slop.cmd on Windows) the way a user
or a coding agent would: --version, `slop check` on the file, an MCP
session with `slop mcp` (initialize, tools/list, then ref, doc and check),
and a project from `slop init` built, run and tested.
SLOP_HOME is removed from the environment, so the command has to find the
native tools and the standard library of its own distribution.

Exits 1 at the first failure, saying what it ran and what came back.
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NoReturn

ENV = {k: v for k, v in os.environ.items() if k != "SLOP_HOME"}


def fail(what, result=None) -> NoReturn:
    print(f"FAIL: {what}", file=sys.stderr)
    if result is not None:
        print(f"  exit status: {result.returncode}", file=sys.stderr)
        print(f"  stdout:\n{result.stdout}", file=sys.stderr)
        print(f"  stderr:\n{result.stderr}", file=sys.stderr)
    sys.exit(1)


def run(cmd, stdin=None, cwd=None):
    return subprocess.run(cmd, input=stdin, capture_output=True, text=True,
                          encoding="utf-8", errors="replace", env=ENV, timeout=300,
                          cwd=cwd)


def smoke_init(slop):
    """slop init a project, then build, run and test it from its directory."""
    with tempfile.TemporaryDirectory() as tmp:
        project = Path(tmp) / "demo"
        result = run([slop, "init", str(project)])
        if result.returncode != 0:
            fail(f"{slop} init {project}", result)
        for rel in ("slop.toml", "src/main.slop", "AGENTS.md", "CLAUDE.md", ".mcp.json",
                    ".claude/skills/slop-review/SKILL.md", ".codex/config.toml"):
            if not (project / rel).is_file():
                fail(f"slop init did not write {rel}", result)
        server = json.loads((project / ".mcp.json").read_text())["mcpServers"]["slop"]
        expected = ["cmd", "/c", "slop", "mcp"] if os.name == "nt" else ["slop", "mcp"]
        if [server["command"], *server["args"]] != expected:
            fail(f"slop init: .mcp.json starts the server with {server}", result)
        print("ok: slop init")

        for args in (["check", "src/main.slop"], ["test"], ["build"]):
            result = run([slop, *args], cwd=project)
            if result.returncode != 0:
                fail(f"{slop} {' '.join(args)} in a new project", result)
        exe = project / "build" / ("demo.exe" if os.name == "nt" else "demo")
        result = run([str(exe)])
        if result.returncode != 0 or result.stdout.strip() != "37":
            fail(f"the new project's {exe.name}", result)
        print("ok: slop check, test, build and run in the new project")


def request(id_, method, params):
    return {"jsonrpc": "2.0", "id": id_, "method": method, "params": params}


def tool(id_, name, arguments):
    return request(id_, "tools/call", {"name": name, "arguments": arguments})


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    slop, example = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])

    result = run([slop, "--version"])
    if result.returncode != 0 or not result.stdout.startswith("slop "):
        fail(f"{slop} --version", result)
    print(f"ok: {result.stdout.strip()}")

    result = run([slop, "check", example])
    if result.returncode != 0:
        fail(f"{slop} check {example}", result)
    print(f"ok: slop check {example}")

    messages = [
        request(1, "initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                                  "clientInfo": {"name": "smoke_dist", "version": "0"}}),
        {"jsonrpc": "2.0", "method": "notifications/initialized"},
        request(2, "tools/list", {}),
        tool(3, "ref", {}),
        tool(4, "doc", {"module": "strlib", "symbol": "trim"}),
        tool(5, "check", {"path": example}),
    ]
    result = run([slop, "mcp"], "".join(json.dumps(m) + "\n" for m in messages))
    if result.returncode != 0:
        fail(f"{slop} mcp exited with an error", result)
    replies = {}
    for line in result.stdout.splitlines():
        try:
            reply = json.loads(line)
        except ValueError:
            fail(f"{slop} mcp wrote a line that is not JSON-RPC: {line!r}", result)
        replies[reply.get("id")] = reply

    def text_of(id_, what):
        reply = replies.get(id_)
        if not reply or "result" not in reply:
            fail(f"slop mcp: no result for {what}", result)
        content = reply["result"]["content"][0]["text"]
        if reply["result"].get("isError"):
            fail(f"slop mcp: {what} failed: {content}", result)
        return content

    if replies.get(1, {}).get("result", {}).get("serverInfo", {}).get("name") != "slop":
        fail("slop mcp: initialize", result)
    tools = [t["name"] for t in replies.get(2, {}).get("result", {}).get("tools", [])]
    if tools != ["ref", "doc", "check", "format"]:
        fail(f"slop mcp: tools/list returned {tools}", result)
    if "strlib" not in text_of(3, "ref"):
        fail("slop mcp: ref does not list the standard library modules", result)
    if "### trim" not in text_of(4, "doc strlib trim"):
        fail("slop mcp: doc strlib trim", result)
    if text_of(5, "check") != "OK: no errors or warnings":
        fail(f"slop mcp: check {example}: {text_of(5, 'check')}", result)
    print("ok: slop mcp (initialize, tools/list, ref, doc, check)")

    smoke_init(slop)


if __name__ == "__main__":
    main()
