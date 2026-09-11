"""BUILTIN_FUNCTIONS must not drift from what the compiler actually supports.

`src/slop/types.py` calls BUILTIN_FUNCTIONS the "single source of truth", and
`hole_filler.py` unions it into the allow-list that decides whether
LLM-generated code is accepted. It is a second, hand-maintained table, and it
had drifted badly (#83): it listed `map-empty`, which has never existed in the
checker, the transpiler or the runtime, while omitting `map-keys`,
`map-remove`, every `set-*` builtin, `list-pop` and `string-push-char`. A hole
that correctly wrote `(set-put s x)` was rejected; one that wrote `(map-empty)`
was waved through.

Comparing the table against the checker's own tables would not have caught it,
in either direction:

  * `char-at`, `string-copy` and `string-slice` are registered builtins in
    `lib/compiler/checker/env.slop` that the transpiler has no lowering for, so
    a hole using one gets `undefined function` at transpile time;
  * `min` and `max` are lowered fine with no checker dispatch behind them.

So the standard is that a call compiles and runs. These tests bind the table to
two conformance suites that do exactly that, and which `make test-native` runs.
"""

import re
from pathlib import Path

from slop.types import BUILTIN_FUNCTIONS

REPO_ROOT = Path(__file__).resolve().parent.parent
CONFORMANCE_FILES = (
    REPO_ROOT / "tests" / "test_builtin_functions.slop",
    REPO_ROOT / "tests" / "test_container_builtins.slop",
)


def _called_names() -> set[str]:
    """Every name appearing in head position in the conformance suites."""
    names: set[str] = set()
    for path in CONFORMANCE_FILES:
        source = path.read_text()
        # Strip comments so a name mentioned only in prose does not count.
        source = re.sub(r";;[^\n]*", "", source)
        names.update(re.findall(r"\(([a-z][a-z0-9!?*<>=+-]*)[\s)]", source))
    return names


class TestBuiltinFunctionTable:
    def test_every_builtin_is_exercised(self):
        """A name in the table that no suite calls is a claim nothing backs.

        This is the direction that catches a stale entry: `map-empty` sat in
        the table for as long as it did precisely because nothing ever tried to
        call it.
        """
        called = _called_names()
        unexercised = sorted(BUILTIN_FUNCTIONS - called)
        assert not unexercised, (
            "BUILTIN_FUNCTIONS names not called by any conformance suite: "
            f"{unexercised}. Add a call to tests/test_builtin_functions.slop "
            "(or tests/test_container_builtins.slop) proving it works, or drop "
            "the name from src/slop/types.py."
        )

    def test_checker_builtins_are_not_missing_from_the_table(self):
        """Every container/memory builtin the checker dispatches must be listed.

        This is the direction that catches an omission: `map-keys`, `map-remove`
        and the `set-*` family were all dispatched by the checker and absent
        from the table, so holes using them were rejected as undefined.

        Only the prefixed container and memory builtins are required here. The
        string builtins are deliberately not, because the checker registers
        three it cannot lower (see the module docstring) -- requiring those
        would force names into the table that do not work.
        """
        infer = (REPO_ROOT / "lib" / "compiler" / "checker" / "infer.slop").read_text()
        dispatched = {
            name
            for name in re.findall(r'\(string-eq op "([^"]+)"\)', infer)
            if name.split("-")[0] in ("list", "map", "set", "arena") and "-" in name
        }
        missing = sorted(dispatched - BUILTIN_FUNCTIONS)
        assert not missing, (
            f"builtins the checker dispatches but BUILTIN_FUNCTIONS omits: {missing}. "
            "A hole generating one of these would be rejected as undefined."
        )

    def test_the_names_that_do_not_work_stay_out(self):
        """Regression pins for the four entries #83 removed.

        Each was verified against the full pipeline rather than a table:
        `map-empty` exists nowhere; `is-ok` and `string-split` reach the
        transpiler as `undefined function`; `string-slice` is registered in the
        checker with no lowering behind it.
        """
        for name in ("map-empty", "is-ok", "string-split", "string-slice"):
            assert name not in BUILTIN_FUNCTIONS, (
                f"{name!r} does not survive transpilation; it must not be in "
                "BUILTIN_FUNCTIONS. See #83."
            )
