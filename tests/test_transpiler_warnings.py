"""
Tests for transpiler warning infrastructure.

Verifies that:
- Closures allocated with malloc (no arena in scope) emit a warning
- Closures allocated within an arena do NOT emit a warning
- Warnings are non-fatal (build succeeds, binary runs correctly)
"""

import re
import subprocess
import pytest
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
TESTS_DIR = REPO_ROOT / "tests"

# Matches a single comparison redundantly wrapped in a second paren layer,
# e.g. `if ((c == 10))` / `while ((i == 0))`. A legitimate compound condition
# like `if ((a) && (b))` contains an inner ')' so the [^()]* class won't span
# it, keeping this a precise detector of the double-wrap bug.
DOUBLE_WRAP_RE = re.compile(r"(?:if|while) \(\([^()]*[=<>!]=[^()]*\)\)")


def slop_build(test_file: str, output: str):
    """Build a .slop file and return (returncode, stdout, stderr)."""
    result = subprocess.run(
        ["uv", "run", "slop", "build", str(TESTS_DIR / test_file), "-o", output],
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    return result.returncode, result.stdout, result.stderr


def slop_transpile(test_file: str, output: str):
    """Transpile a .slop file to C and return (returncode, stdout, stderr)."""
    result = subprocess.run(
        ["uv", "run", "slop", "transpile", str(TESTS_DIR / test_file), "-o", output],
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    return result.returncode, result.stdout, result.stderr


class TestTranspilerWarnings:
    """Test that transpiler warnings are emitted correctly."""

    def test_closure_malloc_warning(self, tmp_path):
        """Closure outside arena should emit malloc warning."""
        output = str(tmp_path / "test_simple_closure")
        rc, stdout, stderr = slop_build("test_simple_closure.slop", output)

        assert rc == 0, f"Build failed: {stderr}"
        assert "warning:" in stderr, f"Expected warning in stderr, got: {stderr!r}"
        assert "malloc" in stderr, f"Expected 'malloc' in warning, got: {stderr!r}"
        assert "no arena in scope" in stderr, f"Expected 'no arena in scope' in warning, got: {stderr!r}"

        # Verify binary runs correctly
        run = subprocess.run([output], capture_output=True)
        assert run.returncode == 0, "Binary should exit 0"

    def test_arena_closure_no_warning(self, tmp_path):
        """Closure inside arena should NOT emit malloc warning."""
        output = str(tmp_path / "test_with_arena_lambda")
        rc, stdout, stderr = slop_build("test_with_arena_lambda.slop", output)

        assert rc == 0, f"Build failed: {stderr}"
        assert "malloc" not in stderr, f"Unexpected malloc warning in stderr: {stderr!r}"

        # Verify binary runs correctly
        run = subprocess.run([output], capture_output=True)
        assert run.returncode == 0, "Binary should exit 0"

    def test_warnings_are_nonfatal(self, tmp_path):
        """Warnings should not prevent successful compilation."""
        output = str(tmp_path / "test_simple_closure")
        rc, stdout, stderr = slop_build("test_simple_closure.slop", output)

        assert rc == 0, "Build should succeed despite warnings"
        assert Path(output).exists(), "Binary should be created"
        assert "warning:" in stderr, "Warning should be present"
        # Verify no errors
        assert "error:" not in stderr, f"Should have no errors, got: {stderr!r}"


class TestConditionParens:
    """Conditions must not double-wrap comparisons (-Wparentheses-equality)."""

    def test_no_double_wrapped_comparisons(self, tmp_path):
        """A comparison used directly as an if/while condition emits one paren layer."""
        output = str(tmp_path / "test_cond_parens.c")
        rc, stdout, stderr = slop_transpile("fixtures/test_cond_parens.slop", output)

        assert rc == 0, f"Transpile failed: {stderr}"
        c_src = Path(output).read_text()

        offenders = DOUBLE_WRAP_RE.findall(c_src)
        assert not offenders, f"Double-wrapped conditions emitted: {offenders}"

        # The clean single-paren forms must be present.
        assert "while (i < n) {" in c_src, c_src
        assert "if (c == 10) {" in c_src, c_src
        # A genuine compound condition keeps its inner parens.
        assert "(c > 32) && (c < 127)" in c_src, c_src

    def test_statement_expr_condition_keeps_required_parens(self, tmp_path):
        """A match-as-condition compiles to `({...})`; its parens must NOT be stripped.

        Stripping them yields `if ({...})`, which is a C syntax error. This case
        only surfaces on the second self-host pass (double bootstrap), so guard it
        directly here.
        """
        output = str(tmp_path / "test_cond_parens.c")
        rc, stdout, stderr = slop_transpile("fixtures/test_cond_parens.slop", output)

        assert rc == 0, f"Transpile failed: {stderr}"
        c_src = Path(output).read_text()

        # The statement-expression must stay wrapped: `if (({ ... }))`.
        assert "if (({ __auto_type" in c_src, c_src
        # The bare, syntactically-invalid form must never appear.
        assert "if ({ __auto_type" not in c_src, c_src


class TestCleanCodegen:
    """Codegen must not emit self-assignments or unused loop values."""

    # `name = name;` — a no-op self-assignment (-Wself-assign).
    SELF_ASSIGN_RE = re.compile(r"\b([A-Za-z_]\w*) = \1;")

    def test_no_self_assign_or_unused_loop_value(self, tmp_path):
        output = str(tmp_path / "test_clean_warnings.c")
        rc, stdout, stderr = slop_transpile("fixtures/test_clean_warnings.slop", output)

        assert rc == 0, f"Transpile failed: {stderr}"
        c_src = Path(output).read_text()

        offender = self.SELF_ASSIGN_RE.search(c_src)
        assert offender is None, f"Self-assignment emitted: {offender.group(0)!r}"

        # A loop used in expression position must be void-terminated so its
        # discarded value does not trip -Wunused-value.
        assert "(void)0; })" in c_src, c_src
        assert "} 0; })" not in c_src, c_src
