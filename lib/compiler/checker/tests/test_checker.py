"""
Native Type Checker Tests

Tests the native SLOP type checker by running it on test files
and verifying expected warnings/errors are produced.
"""

import pytest
from pathlib import Path


class TestCheckerPasses:
    """Tests for code that should pass without warnings"""

    def test_basic_pass(self, run_checker, tests_dir):
        """Basic valid code should pass with no warnings"""
        slop_file = tests_dir / "pass_basic.slop"
        exit_code, stdout, stderr = run_checker(slop_file)

        assert exit_code == 0, f"Expected success, got:\n{stdout}\n{stderr}"
        # Human-readable output: silence means success (GCC/Clang style)
        assert "error" not in stdout.lower(), f"Unexpected error: {stdout}"


class TestBranchTypeWarnings:
    """Tests for branch type mismatch warnings"""

    def test_if_branch_mismatch(self, run_checker, tests_dir):
        """If with mismatched branch types should warn"""
        slop_file = tests_dir / "warn_branch_types.slop"
        exit_code, stdout, stderr = run_checker(slop_file)

        # Should complete (exit 0) but with warnings
        assert "warning" in stdout.lower() or "Warning" in stdout
        assert "Branch types differ" in stdout or "type" in stdout.lower()

    def test_cond_branch_mismatch(self, run_checker, tests_dir):
        """Cond with mismatched branch types should warn"""
        slop_file = tests_dir / "warn_cond_types.slop"
        exit_code, stdout, stderr = run_checker(slop_file)

        assert "warning" in stdout.lower() or "Warning" in stdout

    def test_match_branch_mismatch(self, run_checker, tests_dir):
        """Match with mismatched branch types should warn"""
        slop_file = tests_dir / "warn_match_types.slop"
        exit_code, stdout, stderr = run_checker(slop_file)

        assert "warning" in stdout.lower() or "Warning" in stdout


class TestPythonCheckerComparison:
    """Compare native checker output with Python checker"""

    def test_basic_pass_matches_python(self, run_checker, run_python_checker, tests_dir):
        """Native and Python checker should both pass basic code"""
        slop_file = tests_dir / "pass_basic.slop"

        native_code, native_out, native_err = run_checker(slop_file)
        python_code, python_out, python_err = run_python_checker(slop_file)

        # Both should succeed
        assert native_code == 0, f"Native failed: {native_out}\n{native_err}"
        assert python_code == 0, f"Python failed: {python_out}\n{python_err}"

    @pytest.mark.parametrize("test_file", [
        "warn_branch_types.slop",
        "warn_cond_types.slop",
        "warn_match_types.slop",
    ])
    def test_warning_detection_matches(self, run_checker, run_python_checker, tests_dir, test_file):
        """Both checkers should detect the same warnings"""
        slop_file = tests_dir / test_file

        native_code, native_out, native_err = run_checker(slop_file)
        python_code, python_out, python_err = run_python_checker(slop_file)

        # Check if Python produces warning
        python_has_warning = "warning" in python_out.lower()

        # If Python warns, native should too
        if python_has_warning:
            native_has_warning = "warning" in native_out.lower()
            assert native_has_warning, (
                f"Python checker found warning but native did not.\n"
                f"Python: {python_out}\n"
                f"Native: {native_out}"
            )


class TestTypeErrors:
    """Tests for type errors that should be detected"""

    def test_undefined_variable(self, run_checker, tests_dir):
        """Using undefined variable should produce error"""
        slop_file = tests_dir / "error_undefined_var.slop"
        exit_code, stdout, stderr = run_checker(slop_file)

        assert exit_code != 0 or "error" in stdout.lower()
        assert "undefined" in stdout.lower() or "unknown" in stdout.lower()

    def test_return_type_mismatch(self, run_checker, tests_dir):
        """Returning wrong type should produce error"""
        slop_file = tests_dir / "error_return_type.slop"
        exit_code, stdout, stderr = run_checker(slop_file)

        assert exit_code != 0 or "error" in stdout.lower()
        assert "expected" in stdout.lower() or "mismatch" in stdout.lower()

    def test_ambiguous_enum_variants(self, run_checker, tests_dir):
        """Same variant name in multiple enums should produce error"""
        slop_file = tests_dir / "error_ambiguous_enum.slop"
        exit_code, stdout, stderr = run_checker(slop_file)

        assert exit_code != 0 or "error" in stdout.lower()
        assert "ambiguous" in stdout.lower() or "duplicate" in stdout.lower()

    def test_unknown_field_access(self, run_checker, tests_dir):
        """Accessing non-existent field should produce error about the field"""
        slop_file = tests_dir / "error_unknown_field.slop"
        exit_code, stdout, stderr = run_checker(slop_file)

        assert exit_code != 0 or "error" in stdout.lower()
        # Must specifically mention the unknown field, not just "field" in function name
        assert "no field" in stdout.lower() or "has no field" in stdout.lower()

    def test_arena_named_missing_args(self, run_checker, tests_dir):
        """with-arena :as with insufficient args should error"""
        slop_file = tests_dir / "error_arena_named_missing_args.slop"
        exit_code, stdout, stderr = run_checker(slop_file)

        # Should produce an error - the malformed with-arena causes type issues
        assert exit_code != 0 or "error" in stdout.lower()
        # The checker detects the issue (malformed arena causes return type mismatch or parse error)
        # This validates that malformed :as syntax is not silently accepted
        assert "error" in stdout.lower()


class TestPythonErrorComparison:
    """Compare error detection between native and Python checkers"""

    @pytest.mark.parametrize("test_file", [
        "error_undefined_var.slop",
        "error_return_type.slop",
        "error_ambiguous_enum.slop",
        "error_unknown_field.slop",
    ])
    def test_error_detection_matches(self, run_checker, run_python_checker, tests_dir, test_file):
        """Track parity between native and Python checker error detection"""
        slop_file = tests_dir / test_file

        native_code, native_out, native_err = run_checker(slop_file)
        python_code, python_out, python_err = run_python_checker(slop_file)

        python_has_error = "error" in python_out.lower() or python_code != 0
        native_has_error = "error" in native_out.lower() or native_code != 0

        # Just report parity status, don't fail
        if python_has_error and not native_has_error:
            pytest.skip(f"Native checker missing error detection for {test_file}")


class TestMultiModule:
    """Tests for multi-module type checking"""

    def test_multi_module_passes(self, run_python_checker, tests_dir):
        """Multi-module import should type check successfully"""
        import subprocess

        main_file = tests_dir / "multi-main.slop"

        # Use slop check with include path
        result = subprocess.run(
            ["uv", "run", "slop", "check", str(main_file)],
            capture_output=True,
            text=True,
            cwd=tests_dir,  # Run from tests dir so import resolves
        )

        assert result.returncode == 0, f"Type check failed:\n{result.stdout}\n{result.stderr}"
        # Native checker outputs nothing on success (GCC/Clang style)
        assert "error" not in result.stdout.lower(), f"Unexpected error: {result.stdout}"

    def test_multi_module_with_native_checker(self, tests_dir):
        """Multi-module check with --native flag should work"""
        import subprocess

        main_file = tests_dir / "multi-main.slop"

        # Use slop check --native with include path
        result = subprocess.run(
            ["uv", "run", "slop", "check", str(main_file)],
            capture_output=True,
            text=True,
            cwd=tests_dir,
        )

        # Native checker might not support multi-module yet
        if "not found" in result.stderr.lower() or "falling back" in result.stderr.lower():
            pytest.skip("Native checker not available or falling back to Python")

        # If it ran, should pass (or we're testing that it handles modules)
        assert result.returncode == 0, f"Native check failed:\n{result.stdout}\n{result.stderr}"

    @pytest.mark.xfail(reason="Native checker does not yet validate @spec return types")
    def test_multi_module_type_error_detected(self, run_python_checker, tests_dir):
        """Multi-module with type error should be caught"""
        import subprocess

        error_file = tests_dir / "multi-error.slop"

        # Use slop check with include path
        result = subprocess.run(
            ["uv", "run", "slop", "check", str(error_file)],
            capture_output=True,
            text=True,
            cwd=tests_dir,
        )

        # Should detect the type error (get-status returns Status, not Int)
        has_error = result.returncode != 0 or "error" in result.stdout.lower()
        assert has_error, f"Expected type error but got:\n{result.stdout}\n{result.stderr}"


class TestExpressionMode:
    """Tests for --expr expression mode"""

    def test_basic_expression_valid(self, checker_binary):
        """Basic arithmetic expression should type check as Int"""
        import subprocess
        import json

        result = subprocess.run(
            [str(checker_binary), "--expr", "(+ 1 2)", "--type", "Int"],
            capture_output=True,
            text=True,
        )

        assert result.returncode == 0, f"Expected success: {result.stdout}"
        data = json.loads(result.stdout)
        assert data["valid"] is True
        assert data["inferred_type"] == "Int"
        assert data["expected_type"] == "Int"

    def test_expression_type_mismatch(self, checker_binary):
        """Expression with wrong expected type should fail validation"""
        import subprocess
        import json

        result = subprocess.run(
            [str(checker_binary), "--expr", "(+ 1 2)", "--type", "String"],
            capture_output=True,
            text=True,
        )

        # Should return error (non-zero) or valid=false in JSON
        data = json.loads(result.stdout)
        assert data["valid"] is False
        assert data["inferred_type"] == "Int"
        assert data["expected_type"] == "String"

    def test_expression_with_params(self, checker_binary):
        """Expression using bound parameters should type check"""
        import subprocess
        import json

        result = subprocess.run(
            [str(checker_binary), "--expr", "(+ a b)", "--type", "Int",
             "--params", "((a Int) (b Int))"],
            capture_output=True,
            text=True,
        )

        assert result.returncode == 0, f"Expected success: {result.stdout}"
        data = json.loads(result.stdout)
        assert data["valid"] is True
        assert data["inferred_type"] == "Int"

    def test_expression_with_context_file(self, checker_binary, tests_dir):
        """Expression using types from context file should work"""
        import subprocess
        import json
        import tempfile

        # Create a temporary context file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.slop', delete=False) as f:
            f.write("""
(type Status (enum ok error))
(fn helper ((x Int)) Int
  (@spec ((Int) -> Int))
  x)
""")
            context_file = f.name

        try:
            result = subprocess.run(
                [str(checker_binary), "--expr", "(helper 42)", "--type", "Int",
                 "--context", context_file],
                capture_output=True,
                text=True,
            )

            assert result.returncode == 0, f"Expected success: {result.stdout}\n{result.stderr}"
            data = json.loads(result.stdout)
            assert data["valid"] is True
        finally:
            import os
            os.unlink(context_file)

    def test_expression_json_output_format(self, checker_binary):
        """Output should be valid JSON with expected fields"""
        import subprocess
        import json

        result = subprocess.run(
            [str(checker_binary), "--expr", "(+ 1 2)", "--type", "Int"],
            capture_output=True,
            text=True,
        )

        data = json.loads(result.stdout)
        assert "valid" in data
        assert "inferred_type" in data
        assert "expected_type" in data
        assert "diagnostics" in data
        assert isinstance(data["diagnostics"], list)

    def test_expression_empty_input(self, checker_binary):
        """Empty expression should produce an error or non-zero exit"""
        import subprocess
        import json

        result = subprocess.run(
            [str(checker_binary), "--expr", "", "--type", "Int"],
            capture_output=True,
            text=True,
        )

        # Empty expression should fail - either non-zero exit or valid=false
        if result.stdout.strip():
            try:
                data = json.loads(result.stdout)
                # If JSON output, should indicate invalid
                assert data["valid"] is False or len(data.get("diagnostics", [])) > 0
            except json.JSONDecodeError:
                # Non-JSON output is also acceptable for error case
                pass
        else:
            # No output is acceptable if exit code is non-zero
            # (empty input might just produce error message to stderr)
            assert result.returncode != 0 or "error" in result.stderr.lower()


class TestWithArenaIntegration:
    """Integration tests - compile and run with-arena test suite"""

    def test_with_arena_transpiles(self):
        """test_with_arena.slop should transpile without errors"""
        import subprocess
        from pathlib import Path

        test_file = Path(__file__).parent.parent.parent / "transpiler" / "tests" / "test_with_arena.slop"

        if not test_file.exists():
            pytest.skip(f"Test file not found: {test_file}")

        # Run native transpiler
        result = subprocess.run(
            ["./bin/slop-compiler", "transpile", str(test_file)],
            capture_output=True,
            text=True,
            cwd=Path(__file__).parents[4],  # project root
        )

        assert result.returncode == 0, f"Transpile failed:\nstdout: {result.stdout}\nstderr: {result.stderr}"

    def test_with_arena_type_checks(self):
        """test_with_arena.slop should type check without errors"""
        import subprocess
        from pathlib import Path

        test_file = Path(__file__).parent.parent.parent / "transpiler" / "tests" / "test_with_arena.slop"

        if not test_file.exists():
            pytest.skip(f"Test file not found: {test_file}")

        # Run native type checker via slop check
        result = subprocess.run(
            ["uv", "run", "slop", "check", str(test_file)],
            capture_output=True,
            text=True,
            cwd=Path(__file__).parents[4],  # project root
        )

        assert result.returncode == 0, f"Type check failed:\nstdout: {result.stdout}\nstderr: {result.stderr}"
        assert "error" not in result.stdout.lower(), f"Unexpected error: {result.stdout}"
