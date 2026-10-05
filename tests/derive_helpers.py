"""Shared helpers for the `slop derive` tests.

Derived output is only useful if the compiler accepts it, so these helpers run
the real CLI and the native toolchain from this checkout (SLOP_HOME is pinned
to the repo, so bin/ here is what runs, not an installed slop).
"""

import json
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
FIXTURES = REPO / "tests" / "fixtures" / "derive"

requires_native = pytest.mark.skipif(
    not (REPO / "bin" / "slop-compiler").exists(),
    reason="native toolchain not built (run `make install`)",
)


def slop(*args, check=False):
    """Run the slop CLI from this checkout."""
    env = os.environ.copy()
    env["SLOP_HOME"] = str(REPO)
    result = subprocess.run(
        [sys.executable, "-m", "slop.cli", *[str(a) for a in args]],
        capture_output=True, text=True, env=env, cwd=REPO,
    )
    if check:
        assert result.returncode == 0, result.stdout + result.stderr
    return result


def derive(tmp_path, fixture, name, *extra):
    """`slop derive` a fixture to tmp_path/<name>.slop; returns (path, stderr)."""
    out = tmp_path / f"{name}.slop"
    result = slop("derive", FIXTURES / fixture, "-o", out, *extra, check=True)
    return out, result.stderr


def check_errors(path):
    """Error diagnostics `slop check` reports for path, as messages."""
    result = slop("check", "--json", path)
    try:
        # The JSON is the last line; the CLI may print progress before it.
        payload = json.loads(result.stdout.strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        raise AssertionError(f"slop check gave no JSON:\n{result.stdout}\n{result.stderr}")
    messages = []
    for module in payload.values():
        for diag in module.get("diagnostics", []):
            if diag.get("level") == "error":
                messages.append(diag["message"])
    return messages


def assert_checks(path, holes_allowed=False):
    """slop check reports nothing but (optionally) the unfilled holes."""
    errors = check_errors(path)
    if holes_allowed:
        errors = [e for e in errors if not e.startswith("Unfilled hole")]
    assert errors == [], f"{path.name}:\n" + "\n".join(errors) + "\n" + path.read_text()


_HOLE = re.compile(
    r'\(hole \(Result .+? ApiError\) "(?:[^"\\]|\\.)*"\s*'
    r':complexity tier-\d(?:\s*:context \([^()]*\))?\)',
    re.DOTALL,
)


def fill_holes(text, replacement="(error 'unknown-error)", only=None):
    """Replace each handler's hole (or the hole of fn `only`) with an expression."""
    if only is None:
        return _HOLE.sub(replacement, text)
    start = text.index(f"(fn {only} ")
    match = _HOLE.search(text, start)
    return text[:match.start()] + replacement + text[match.end():]


def add_main(text, body="0"):
    """Export and define a main in the derived module, so it links."""
    text = text.replace("(export ", "(export main ", 1)
    assert text.endswith(")\n")
    main = (
        "  (fn main ()\n"
        '    (@intent "Exercise the derived module")\n'
        "    (@spec (() -> Int))\n"
        f"    {body})\n"
    )
    return text[:-2] + main + ")\n"


def build_and_run(path, tmp_path):
    """slop build path and run the binary; returns the run's exit code."""
    binary = tmp_path / (path.stem + "-bin")
    result = slop("build", path, "-o", binary)
    assert result.returncode == 0, result.stdout + result.stderr + "\n" + path.read_text()
    return subprocess.run([str(binary)], capture_output=True, text=True).returncode
