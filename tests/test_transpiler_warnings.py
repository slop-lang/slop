"""
Tests for transpiler warning infrastructure.

Verifies that:
- Closures allocated with malloc (no arena in scope) emit a warning
- Closures allocated within an arena do NOT emit a warning
- Warnings are non-fatal (build succeeds, binary runs correctly)
"""

import re
import subprocess
import tempfile
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


class TestAggregateEquality:
    """`==` on a record or union lowers to the generated structural eq (#89)."""

    def test_container_operand_is_a_transpiler_error(self, tmp_path):
        """`(== opt1 opt2)` must be diagnosed by the transpiler, not by cc.

        (Option T) is a C struct, so a bare `a == b` is invalid C. Before #89
        that reached the C compiler, and `slop build` discards cc output --
        so the failure surfaced with no line number and no mention of `==`.
        """
        output = str(tmp_path / "test_eq_container_operand.c")
        rc, stdout, stderr = slop_transpile("fixtures/test_eq_container_operand.slop", output)

        assert rc != 0, f"Expected a transpiler error, got rc=0. stdout={stdout!r}"
        combined = stdout + stderr
        assert "is not defined on 'slop_option_int'" in combined, combined
        # Positioned at the comparison, not at the module.
        assert re.search(r"test_eq_container_operand\.slop:\d+:\d+: error:", combined), combined

    def test_container_field_warns_but_compiles(self, tmp_path):
        """A record with a (List T) field is comparable, but by identity.

        emit-field-eq compares such a field with memcmp over {data, len, cap},
        so two lists with identical contents are unequal. That is unchanged
        map/set-key behaviour; the warning is what makes it visible now that
        `==` reaches it from ordinary code.
        """
        output = str(tmp_path / "test_eq_container_field.c")
        rc, stdout, stderr = slop_transpile("fixtures/test_eq_container_field.slop", output)

        assert rc == 0, f"Transpile failed: {stderr}"
        combined = stdout + stderr
        assert "by identity, not contents" in combined, combined
        # The offending field is named, so the warning is actionable.
        assert "'items'" in combined, combined

        c_src = Path(output).read_text()
        # The comparison went through the generated structural eq, and both
        # operands were bound first -- slop_eq_ takes const void*, so an
        # rvalue operand has no address to take.
        assert "slop_eq_eq_container_field_Bag(&" in c_src, c_src

    def test_container_union_payload_is_a_transpiler_error(self, tmp_path):
        """A union variant carrying a (List T) has no structural equality.

        The generated eq/hash fall through to slop_eq_slop_list_int, which does
        not exist. That predates #89 -- it broke for a Map/Set key too -- but ==
        makes it easy to reach, so it is diagnosed rather than emitted.
        """
        output = str(tmp_path / "test_eq_container_payload.c")
        rc, stdout, stderr = slop_transpile("fixtures/test_eq_container_payload.slop", output)

        assert rc != 0, f"Expected a transpiler error, got rc=0. stdout={stdout!r}"
        combined = stdout + stderr
        assert "has no structural equality" in combined, combined
        assert "'(List Int)'" in combined, combined
        # hash and eq are generated as a pair, so the transpiler must report the
        # payload once, not twice. The CLI echoes its whole diagnostic block a
        # second time under "Transpilation failed:", so count only the first copy.
        first_copy = combined.split("Transpilation failed:")[0]
        assert first_copy.count("has no structural equality") == 1, first_copy


def slop_check(test_file: str):
    """Type check a .slop file and return (returncode, stdout, stderr)."""
    result = subprocess.run(
        ["uv", "run", "slop", "check", str(TESTS_DIR / test_file)],
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    return result.returncode, result.stdout, result.stderr


class TestMatchExhaustiveness:
    """The checker reports a match that cannot be shown to cover every variant.

    Root cause of #86: the C compiler's -Wswitch was the only thing catching a
    missing arm, and only for enum/union matches. An Option match compiles to an
    if-chain, so a missing (none) arm was invisible at every stage.
    """

    def test_missing_variants_are_named(self):
        """The message must name what is missing, not just say 'non-exhaustive'."""
        rc, stdout, stderr = slop_check("fixtures/test_match_nonexhaustive.slop")
        combined = stdout + stderr

        assert "non-exhaustive match on Colour: missing blue" in combined, combined
        # Multi-payload variant, named by its SLOP name not its C name.
        assert "non-exhaustive match on Fault: missing parse-fault" in combined, combined
        # The case C cannot see: an Option match is an if-chain, never a switch.
        assert "non-exhaustive match on Option_Int: missing none" in combined, combined
        assert "non-exhaustive match on Result: missing error" in combined, combined

        # Positioned at the match, not at the module.
        assert re.search(r"test_match_nonexhaustive\.slop:\d+:\d+: warning:", combined), combined

    def test_exhaustive_forms_are_silent(self):
        """The check is conservative by design; this pins that it stays that way.

        A false positive on a new diagnostic is what gets it suppressed and then
        ignored -- exactly how the -Wreturn-type noise it replaces was ignored.
        Covers: all arms named, `_`, `else`, complete Option, complete Result,
        and a literal match (no finite variant set, so never reportable).
        """
        rc, stdout, stderr = slop_check("fixtures/test_match_exhaustive_ok.slop")
        combined = stdout + stderr
        assert "non-exhaustive" not in combined, combined


class TestMatchFallthroughTrap:
    """A return-position match emits SLOP_UNREACHABLE() after the construct (#86)."""

    def test_trap_after_chain_and_switch_preserves_wswitch(self, tmp_path):
        """The trap goes AFTER the closed construct, never as `else` / `default:`.

        A `default:` would silence -Wswitch, and a plain `else` would run the last
        arm's body for an unmatched value -- which the checker cannot yet rule out.
        -Wswitch is the only exhaustiveness signal C gives us, so it stays live.
        """
        output = str(tmp_path / "test_match_exhaustive_ok.c")
        rc, stdout, stderr = slop_transpile("fixtures/test_match_exhaustive_ok.slop", output)
        assert rc == 0, f"Transpile failed: {stderr}"
        c_src = Path(output).read_text()

        # all-arms is a return-position union match with no else: gets the trap.
        assert "SLOP_UNREACHABLE();" in c_src, c_src
        # The switch must NOT have grown a default: arm.
        switch_body = c_src[c_src.index("switch ("):]
        assert "default:" not in switch_body.split("SLOP_UNREACHABLE")[0], switch_body[:400]

    def test_no_trap_when_an_else_arm_exists(self, tmp_path):
        """`else` / `_` already makes the chain total; a trap there would be dead code."""
        output = str(tmp_path / "test_match_exhaustive_ok2.c")
        rc, stdout, stderr = slop_transpile("fixtures/test_match_exhaustive_ok.slop", output)
        assert rc == 0, f"Transpile failed: {stderr}"
        c_src = Path(output).read_text()

        # wildcard/else arms compile to `default:`; those functions end with a
        # closing brace and no trap.
        for fn in ("match_exhaustive_ok_wildcard", "match_exhaustive_ok_else_arm"):
            body = c_src.split(f"{fn}(")[-1]
            body = body[:body.index("\n}\n")]
            assert "SLOP_UNREACHABLE" not in body, f"{fn} should not be trapped:\n{body}"


class TestFloatLiteralTyping:
    """A float literal types as Float, not Int (#94).

    `Float` was the one primitive with no entry in `env-new`: the parameter side
    built it on demand via resolve-simple-type, but nothing cached it, so the
    literal side had nothing to be given and fell through to Int. Correct code
    that transpiles fine was reported as a type error.
    """

    def test_float_literals_check_clean(self):
        output = slop_check("fixtures/test_float_literal.slop")
        combined = output[1] + output[2]

        # The exact shape #94 reported.
        assert "expected Float, got Int" not in combined, combined
        # Nothing else should fire either -- every form in the fixture is valid.
        assert ": error:" not in combined, combined
        assert ": warning:" not in combined, combined


class TestNilPointerType:
    """`nil` is the null pointer, not Unit.

    infer-expr typed `nil` and `unit` identically, so every `((none) nil)` arm
    read as Unit and collided with the pointer the sibling arm produced. That
    was the bulk of the checker's warning volume, and it was noise rather than
    signal -- which matters, because a channel that cries wolf gets ignored.
    """

    def test_nil_in_pointer_position_checks_clean(self):
        rc, stdout, stderr = slop_check("fixtures/test_nil_pointer_type.slop")
        combined = stdout + stderr
        assert "Branch types differ" not in combined, combined
        assert ": error:" not in combined, combined
        assert ": warning:" not in combined, combined

    def test_a_real_branch_mismatch_still_warns(self, tmp_path):
        """A Unit arm in value position is a real bug and must keep warning.

        `(if flag 1 (println "x"))` in an Int-returning function emits
        `return printf(...)` as the result. Most `Branch types differ: * vs Unit`
        warnings are benign statement-position noise, so quieting the class by
        ignoring any Unit arm is tempting -- and would hide exactly this. Left
        as a guard against that shortcut.
        """
        src = tmp_path / "unitbranch.slop"
        src.write_text(
            "(module unitbranch\n"
            "  (fn bad ((flag Bool))\n"
            '    (@intent "value position with a Unit arm")\n'
            "    (@spec ((Bool) -> Int))\n"
            '    (if flag 1 (println "x")))\n'
            "  (fn main () (@spec (() -> Int)) :c-name \"main\" (bad true)))\n"
        )
        result = subprocess.run(
            ["uv", "run", "slop", "check", str(src)],
            capture_output=True, text=True, cwd=str(REPO_ROOT),
        )
        combined = result.stdout + result.stderr
        assert "Branch types differ" in combined, combined

    def test_nil_arm_first_keeps_the_pointee(self, tmp_path):
        """Unifying nil with a pointer must keep the pointer, whichever arm is first.

        Returning the NullPtr side erases the pointee, so a later `(. p field)`
        infers Unknown and passes unchecked -- an order-dependent blind spot.
        """
        src = tmp_path / "nilfirst.slop"
        src.write_text(
            "(module nilfirst\n"
            "  (type Node (record (value Int)))\n"
            "  (fn nil-first ((flag Bool) (n (Ptr Node)))\n"
            '    (@intent "nil arm first")\n'
            "    (@spec ((Bool (Ptr Node)) -> Int))\n"
            "    (let ((p (if flag nil n)))\n"
            "      (. p missing)))\n"
            "  (fn nil-second ((flag Bool) (n (Ptr Node)))\n"
            '    (@intent "nil arm second")\n'
            "    (@spec ((Bool (Ptr Node)) -> Int))\n"
            "    (let ((p (if flag n nil)))\n"
            "      (. p missing)))\n"
            "  (fn main () (@spec (() -> Int)) :c-name \"main\" 0))\n"
        )
        result = subprocess.run(
            ["uv", "run", "slop", "check", str(src)],
            capture_output=True, text=True, cwd=str(REPO_ROOT),
        )
        combined = result.stdout + result.stderr
        # Both orderings must report the bad field, not just one.
        assert combined.count("has no field 'missing'") == 2, combined

    def test_field_access_on_nil_is_rejected(self, tmp_path):
        """nil has no pointee, so it has no fields -- catch it before C does."""
        src = tmp_path / "nilfield.slop"
        src.write_text(
            "(module nilfield\n"
            "  (fn bad () (@intent \"field on nil\") (@spec (() -> Int)) (. nil value))\n"
            "  (fn main () (@spec (() -> Int)) :c-name \"main\" 0))\n"
        )
        result = subprocess.run(
            ["uv", "run", "slop", "check", str(src)],
            capture_output=True, text=True, cwd=str(REPO_ROOT),
        )
        combined = result.stdout + result.stderr
        assert "cannot access field 'value' on nil" in combined, combined

    def test_nil_against_a_non_pointer_still_warns(self, tmp_path):
        """nil only stands in for a pointer, never for an arbitrary type.

        `(if flag nil 1)` must not be silently inferred as Int -- the generated
        C would then fail on a pointer-to-integer conversion.
        """
        src = tmp_path / "nilint.slop"
        src.write_text(
            "(module nilint\n"
            "  (fn f ((flag Bool))\n"
            '    (@intent "nil against a non-pointer")\n'
            "    (@spec ((Bool) -> Int))\n"
            "    (if flag nil 1))\n"
            "  (fn main () (@spec (() -> Int)) :c-name \"main\" 0))\n"
        )
        result = subprocess.run(
            ["uv", "run", "slop", "check", str(src)],
            capture_output=True, text=True, cwd=str(REPO_ROOT),
        )
        combined = result.stdout + result.stderr
        assert "Branch types differ" in combined, combined

    def test_nil_body_against_a_non_pointer_return_is_rejected(self, tmp_path):
        """A `nil` body must not satisfy a non-pointer @spec.

        The null type is not a primitive, so the return check -- which fires only
        when both sides are -- skipped it entirely and let `return NULL;` reach
        Clang's pointer-to-integer error.
        """
        src = tmp_path / "nilret.slop"
        src.write_text(
            "(module nilret\n"
            "  (fn bad ()\n"
            '    (@intent "returns nil but declares Int")\n'
            "    (@spec (() -> Int))\n"
            "    nil)\n"
            "  (fn main () (@spec (() -> Int)) :c-name \"main\" 0))\n"
        )
        result = subprocess.run(
            ["uv", "run", "slop", "check", str(src)],
            capture_output=True, text=True, cwd=str(REPO_ROOT),
        )
        combined = result.stdout + result.stderr
        assert "expected Int, got <nil>" in combined, combined


class TestWithArenaAsClosure:
    """A closure inside a named arena allocates from it, not malloc (#75)."""

    def test_named_arena_closure_uses_the_arena(self, tmp_path):
        """`(with-arena :as myarena ...)` binds neither "arena" nor "_arena".

        The env fell back to malloc and was never freed -- a working program
        that leaks, announced only by a warning with no source location. Not
        observable from inside the program, so assert on the emitted C.
        """
        output = str(tmp_path / "with_arena_as_closure.c")
        rc, stdout, stderr = slop_transpile("fixtures/test_with_arena_as_closure.slop", output)
        assert rc == 0, f"Transpile failed: {stderr}"
        c_src = Path(output).read_text()

        assert "malloc(" not in c_src, c_src
        # The named form must allocate from that arena specifically, not merely
        # from whichever arena happened to be findable.
        assert "slop_arena_alloc(myarena" in c_src, c_src
        assert "slop_arena_alloc(arena" in c_src, c_src
        # And the warning that used to accompany the malloc must be gone.
        assert "no arena in scope" not in (stdout + stderr), stdout + stderr


class TestOptionPredicates:
    """`is-none` / `is-some` (#107).

    There was no way to ask whether an Option was empty without a full `match`.
    `==` is not that way: spec/LANGUAGE.md classes (Option T) as a container and
    rejects `==` on one, deliberately.

    These are tag predicates, so they never touch the payload -- which is the
    property that matters. They hold for a T whose payload has no structural
    equality at all, where any comparison-based test would be impossible rather
    than merely awkward.
    """

    def test_non_option_argument_is_named(self):
        rc, stdout, stderr = slop_check("fixtures/test_option_predicate_bad_arg.slop")
        combined = stdout + stderr

        assert rc != 0, combined
        # Each bad argument must be reported with its own type named, so the
        # message points at the mistake rather than just refusing.
        assert "'is-none' expects an (Option T), got Int" in combined, combined
        assert "'is-some' expects an (Option T), got Point" in combined, combined
        # A List is a container too, but it is not an Option.
        assert "'is-none' expects an (Option T), got List" in combined, combined
        # A range alias is a resolved, definitely-not-Option type.
        assert "'is-none' expects an (Option T), got Meters" in combined, combined
        assert "'is-some' expects 1 argument(s), got 2" in combined, combined

    def test_valid_uses_are_silent(self):
        """The bail-outs, which are what keep the new check from becoming noise.

        Covers an Option in parameter position, over a record payload, built
        inline from (some ...) / (none), the two inferred Options that list-get
        and map-get return, and -- the one that caught a real false positive --
        an Option reached through a type alias. collect.slop records no inner for
        a form alias, so (type MaybeInt (Option Int)) arrives as a bare
        rk-primitive with nothing marking it as an Option.
        """
        rc, stdout, stderr = slop_check("fixtures/test_option_predicate_ok.slop")
        combined = stdout + stderr

        assert rc == 0, combined
        assert ": error:" not in combined, combined
        assert ": warning:" not in combined, combined

    def test_lowering_is_a_tag_test(self):
        """No payload access, and no call into a generated equality function."""
        with tempfile.TemporaryDirectory() as tmp:
            out = str(Path(tmp) / "opt.c")
            rc, stdout, stderr = slop_transpile("test_option_predicates.slop", out)
            assert rc == 0, stdout + stderr
            c_src = Path(out).read_text()

        assert ".has_value" in c_src, "expected a tag test in the generated C"
        # A tag predicate must not reach for structural equality; that is exactly
        # what it exists to avoid, since the payload may have none.
        assert "slop_eq_test_option_predicates_UnComparable" not in c_src, c_src
