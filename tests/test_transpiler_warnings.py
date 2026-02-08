"""
Tests for transpiler warning infrastructure.

Verifies that:
- Closures allocated with malloc (no arena in scope) emit a warning
- Closures allocated within an arena do NOT emit a warning
- Warnings are non-fatal (build succeeds, binary runs correctly)
"""

import subprocess
import pytest
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
TESTS_DIR = REPO_ROOT / "tests"


def slop_build(test_file: str, output: str):
    """Build a .slop file and return (returncode, stdout, stderr)."""
    result = subprocess.run(
        ["uv", "run", "slop", "build", str(TESTS_DIR / test_file), "-o", output],
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
