"""
Tests for enum match expression code generation.

Verifies that:
- Enum match works in expression position (let bindings, function args)
- Enum match with else/default works correctly
- Nested enum match inside option match arms works (is-return gating fix)
"""

import subprocess
import pytest
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
TEST_FILE = REPO_ROOT / "lib" / "compiler" / "transpiler" / "tests" / "test_enum_match.slop"


def slop_build(test_file: Path, output: str):
    """Build a .slop file and return (returncode, stdout, stderr)."""
    result = subprocess.run(
        ["uv", "run", "slop", "build", str(test_file), "-o", output],
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    return result.returncode, result.stdout, result.stderr


class TestEnumMatchExpression:
    """Test enum match in expression position."""

    def test_enum_match_builds(self, tmp_path):
        """Enum match expression test should compile without errors."""
        output = str(tmp_path / "test_enum_match")
        rc, stdout, stderr = slop_build(TEST_FILE, output)

        assert rc == 0, f"Build failed: {stderr}"
        assert "error:" not in stderr, f"Unexpected error: {stderr}"

    def test_enum_match_runs(self, tmp_path):
        """Enum match expression test should run and pass all assertions."""
        output = str(tmp_path / "test_enum_match")
        rc, stdout, stderr = slop_build(TEST_FILE, output)

        assert rc == 0, f"Build failed: {stderr}"

        # Run the binary - exit code 0 means all tests passed
        run = subprocess.run([output], capture_output=True)
        assert run.returncode == 0, "Enum match tests failed (binary returned non-zero)"
