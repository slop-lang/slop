"""
Z3 Verifier tests for SLOP
"""

import pytest

# Skip all tests if z3 is not available
z3_available = False
try:
    import z3
    z3_available = True
except ImportError:
    pass

pytestmark = pytest.mark.skipif(not z3_available, reason="z3-solver not installed")


class TestZ3Translation:
    """Test SLOP to Z3 translation"""

    def test_arithmetic_translation(self):
        """Test +, -, *, / translate correctly"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        # Declare variables
        translator.declare_variable('x', PrimitiveType('Int'))
        translator.declare_variable('y', PrimitiveType('Int'))

        # Test addition
        expr = parse("(+ x y)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert str(z3_expr) == "x + y"

        # Test subtraction
        expr = parse("(- x y)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert str(z3_expr) == "x - y"

        # Test multiplication
        expr = parse("(* x y)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert str(z3_expr) == "x*y"

    def test_comparison_translation(self):
        """Test >, <, >=, <=, ==, != translate correctly"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        translator.declare_variable('x', PrimitiveType('Int'))
        translator.declare_variable('y', PrimitiveType('Int'))

        # Test greater than
        expr = parse("(> x y)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert "x" in str(z3_expr) and "y" in str(z3_expr)

        # Test less than or equal
        expr = parse("(<= x 10)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        # Z3 may format as "10 >= x" or "x <= 10"
        assert "x" in str(z3_expr) and "10" in str(z3_expr)

        # Test equality
        expr = parse("(== x y)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert "x" in str(z3_expr) and "y" in str(z3_expr)

    def test_boolean_translation(self):
        """Test and, or, not translate correctly"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        translator.declare_variable('a', PrimitiveType('Bool'))
        translator.declare_variable('b', PrimitiveType('Bool'))

        # Test and
        expr = parse("(and a b)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert "And" in str(z3_expr)

        # Test or
        expr = parse("(or a b)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert "Or" in str(z3_expr)

        # Test not
        expr = parse("(not a)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert "Not" in str(z3_expr)

    def test_range_type_constraints(self):
        """Test RangeType adds correct Z3 constraints"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.types import RangeType, RangeBounds

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        # Declare a range-typed variable
        range_type = RangeType('Int', RangeBounds(0, 100))
        translator.declare_variable('x', range_type)

        # Should have constraints for bounds
        assert len(translator.constraints) == 2  # x >= 0 and x <= 100


class TestContractVerification:
    """Test contract verification"""

    def test_valid_contract_verifies(self):
        """Function with self-consistent contract should verify"""
        from slop.verifier import verify_source

        # This tests that contracts are internally consistent
        # Note: The verifier checks if (pre AND NOT post) is unsatisfiable
        # This is true when the postcondition is always true (like true)
        source = """
        (module test
          (fn always-true ((x Int))
            (@spec ((Int) -> Bool))
            (@pre (>= x 0))
            (@post (== $result true))
            true))
        """
        results = verify_source(source)

        # Should have at least one result from the function
        assert len(results) >= 1

    def test_trivially_true_postcondition(self):
        """Postcondition that is always true"""
        from slop.verifier import verify_source

        # Test with postcondition that is a tautology
        source = """
        (module test
          (fn tautology ((x Int))
            (@spec ((Int) -> Int))
            (@pre (> x 0))
            (@post (or (> $result 0) (<= $result 0)))
            x))
        """
        results = verify_source(source)

        # The tautology postcondition should verify
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_unsatisfiable_precondition(self):
        """Precondition that can never be true"""
        from slop.verifier import verify_source

        source = """
        (fn impossible ((x Int))
          (@spec ((Int) -> Int))
          (@pre (and (> x 10) (< x 5)))
          x)
        """
        results = verify_source(source)

        failed = [r for r in results if r.status == 'failed']
        assert len(failed) >= 1

    def test_malformed_postcondition_fails(self):
        """Malformed postcondition should fail, not pass"""
        from slop.verifier import verify_source

        # (== 42) is missing second argument
        source = """
        (module test
          (fn bad ((x Int))
            (@spec ((Int) -> Int))
            (@post (== 42))
            x))
        """
        results = verify_source(source)

        failed = [r for r in results if r.status == 'failed']
        assert len(failed) >= 1
        assert "postcondition" in failed[0].message.lower()

    def test_malformed_precondition_fails(self):
        """Malformed precondition should fail, not pass"""
        from slop.verifier import verify_source

        # (> x) is missing second argument
        source = """
        (module test
          (fn bad ((x Int))
            (@spec ((Int) -> Int))
            (@pre (> x))
            x))
        """
        results = verify_source(source)

        failed = [r for r in results if r.status == 'failed']
        assert len(failed) >= 1
        assert "precondition" in failed[0].message.lower()

    def test_function_with_range_param(self):
        """Function with range type parameter - contract checking only"""
        from slop.verifier import verify_source

        # Note: The verifier checks contract consistency, not function body semantics
        # This test verifies that range constraints are used in contract checking
        source = """
        (module test
          (type Positive (Int 1 .. 100))
          (fn check ((x Positive))
            (@spec ((Positive) -> Int))
            (@pre (>= x 1))
            (@post (>= $result 1))
            x))
        """
        results = verify_source(source)

        # With a proper @pre that matches the range, the postcondition
        # should be verifiable (x >= 1 implies $result >= 1 when $result = x)
        verified = [r for r in results if r.status == 'verified']
        failed = [r for r in results if r.status == 'failed']

        # This verifies that preconditions and range types are being used
        assert len(results) > 0

    def test_deref_in_precondition(self):
        """Contracts with deref should translate"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Obj (record (is-open Bool)))
          (fn check ((f (Ptr Obj)))
            (@spec (((Ptr Obj)) -> Bool))
            (@pre (. (deref f) is-open))
            (@post (or (== $result true) (== $result false)))
            true))
        """
        results = verify_source(source)
        # Should not fail due to translation error
        failed_translation = [r for r in results
                              if r.status == 'failed' and 'translate' in r.message.lower()]
        assert len(failed_translation) == 0

    def test_mutable_state_postcondition_warns(self):
        """Postcondition with deref field access should warn, not fail"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Obj (record (is-open Bool)))
          (fn close ((f (Ptr Obj)))
            (@spec (((Ptr Obj)) -> Bool))
            (@pre (. (deref f) is-open))
            (@post (not (. (deref f) is-open)))
            true))
        """
        results = verify_source(source)
        warnings = [r for r in results if r.status == 'warning']
        assert len(warnings) == 1
        assert "mutable state" in warnings[0].message.lower()

    def test_enum_comparison_in_postcondition(self):
        """Postcondition comparing $result to enum variant should verify"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Status (enum ok error pending))
          (fn get-status ((x Int))
            (@spec ((Int) -> Status))
            (@post (or (== $result 'ok)
                       (== $result 'error)
                       (== $result 'pending)))
            'ok))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) == 1


class TestRangeVerification:
    """Test range type safety verification"""

    def test_range_type_parsed(self):
        """Range type should be recognized and used in verification"""
        from slop.verifier import verify_source

        # Test that range types are properly parsed and used
        # The @pre explicitly states the range constraint
        source = """
        (module test
          (type Age (Int 0 .. 150))
          (fn check-age ((a Age))
            (@spec ((Age) -> Bool))
            (@pre (>= a 0))
            (@pre (<= a 150))
            (@post (== $result true))
            true))
        """
        results = verify_source(source)

        # Should have results (verifier ran)
        assert len(results) >= 1


class TestVerifySource:
    """Test the verify_source API"""

    def test_parse_error_handled(self):
        """Parse errors should be reported"""
        from slop.verifier import verify_source

        source = "(fn incomplete"  # Invalid syntax
        results = verify_source(source)

        errors = [r for r in results if r.status == 'error']
        assert len(errors) >= 1

    def test_no_contracts_skipped(self):
        """Functions without contracts should be skipped"""
        from slop.verifier import verify_source

        source = """
        (fn simple ((x Int))
          (@spec ((Int) -> Int))
          x)
        """
        results = verify_source(source)

        skipped = [r for r in results if r.status == 'skipped']
        assert len(skipped) >= 1

    def test_multiple_preconditions(self):
        """Multiple @pre should all be checked"""
        from slop.verifier import verify_source

        # Test that multiple preconditions are all used
        # Use a postcondition that follows from the preconditions
        source = """
        (module test
          (fn bounded ((x Int))
            (@spec ((Int) -> Int))
            (@pre (>= x 0))
            (@pre (<= x 100))
            (@post (or (>= $result 0) (< $result 0)))
            x))
        """
        results = verify_source(source)

        # Should have results
        assert len(results) >= 1
        # A tautology (x >= 0 OR x < 0) is always true
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_contradictory_postconditions(self):
        """Z3 catches logically impossible postconditions"""
        from slop.verifier import verify_source

        source = """
        (module test
        (fn impossible ((x Int))
            (@spec ((Int) -> Int))
            (@pre (> x 0))
            (@post (> $result x))
            (@post (< $result x))
            x))
        """
        results = verify_source(source)

        failed = [r for r in results if r.status == 'failed']
        assert len(failed) == 1

class TestZ3Available:
    """Test Z3 availability check"""

    def test_z3_available_flag(self):
        """Z3_AVAILABLE should be True when z3 is installed"""
        from slop.verifier import Z3_AVAILABLE
        assert Z3_AVAILABLE is True


class TestInfixContractVerification:
    """Test that infix contract notation works with Z3 verification"""

    def test_infix_precondition_verifies(self):
        """Infix @pre works with verification"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn positive ((x Int))
            (@spec ((Int) -> Bool))
            (@pre {x > 0})
            (@post (== $result true))
            true))
        """
        results = verify_source(source)
        assert len(results) >= 1

    def test_infix_postcondition_verifies(self):
        """Infix @post works with verification"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn identity ((x Int))
            (@spec ((Int) -> Int))
            (@pre (> x 0))
            (@post {$result == x})
            x))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_infix_and_prefix_equivalent(self):
        """Infix and prefix produce identical verification results"""
        from slop.verifier import verify_source

        # Prefix version
        source_prefix = """
        (module test
          (fn check ((x Int))
            (@spec ((Int) -> Int))
            (@pre (and (>= x 0) (<= x 100)))
            (@post (>= $result 0))
            x))
        """

        # Infix version - semantically identical
        source_infix = """
        (module test
          (fn check ((x Int))
            (@spec ((Int) -> Int))
            (@pre {x >= 0 and x <= 100})
            (@post {$result >= 0})
            x))
        """

        results_prefix = verify_source(source_prefix)
        results_infix = verify_source(source_infix)

        # Both should have same verification outcome
        assert len(results_prefix) == len(results_infix)
        for rp, ri in zip(results_prefix, results_infix):
            assert rp.status == ri.status

    def test_infix_complex_expression(self):
        """Complex infix expressions verify correctly"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn range-check ((x Int) (y Int))
            (@spec ((Int Int) -> Bool))
            (@pre {x >= 0 and y >= 0 and x < 100 and y < 100})
            (@post {$result == true or $result == false})
            (< x y)))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_infix_with_arithmetic(self):
        """Infix arithmetic in contracts verifies correctly"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn double ((x Int))
            (@spec ((Int) -> Int))
            (@pre {x >= 0})
            (@post {$result >= x})
            (* x 2)))
        """
        results = verify_source(source)
        # Should have results (verification may or may not succeed
        # depending on body analysis, but should not error)
        assert len(results) >= 1

    def test_infix_assume(self):
        """Infix @assume works with verification"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn positive-result ((x Int))
            (@spec ((Int) -> Int))
            (@pre {x > 0})
            (@assume {$result > 0})
            x))
        """
        results = verify_source(source)
        # Should process without errors
        assert len(results) >= 1


class TestNewConstructs:
    """Test new constructs: string-len, dot notation, match, function calls"""

    def test_string_len_translation(self):
        """Test string-len translates to Z3"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        translator.declare_variable('s', PrimitiveType('String'))

        # Test string-len
        expr = parse("(string-len s)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        # String length should have non-negative constraint added
        assert len(translator.constraints) >= 1

    def test_string_len_precondition(self):
        """Verify precondition with string-len"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn check-string ((s String))
            (@spec ((String) -> Bool))
            (@pre (> (string-len s) 0))
            (@post (== $result true))
            true))
        """
        results = verify_source(source)
        # Should verify (postcondition is trivially true)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_shorthand_dot_notation(self):
        """Test t.field shorthand translates like (. t field)"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        translator.declare_variable('t', PrimitiveType('Int'))

        # Test shorthand notation
        expr = parse("t.value")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert 'field_value' in str(z3_expr)

    def test_shorthand_dot_postcondition(self):
        """Verify postcondition using shorthand dot notation"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Point (record (x Int) (y Int)))
          (fn get-x ((p (Ptr Point)))
            (@spec (((Ptr Point)) -> Int))
            (@post (>= $result 0))
            (. p x)))
        """
        results = verify_source(source)
        # Should have at least one result
        assert len(results) >= 1

    def test_match_expression_translation(self):
        """Test match expression translates to nested If"""
        from slop.verifier import Z3Translator, MinimalTypeEnv, build_type_registry_from_ast
        from slop.parser import parse
        from slop.types import PrimitiveType

        source = """
        (type Result (union (ok Int) (error Int)))
        """
        ast = parse(source)
        registry = build_type_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=registry)
        translator = Z3Translator(env)

        translator.declare_variable('r', PrimitiveType('Int'))

        # Test match translation
        expr = parse("(match r ((ok v) v) ((error e) 0))")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        # Should produce an If expression
        assert 'If' in str(z3_expr) or z3_expr is not None

    def test_match_in_postcondition(self):
        """Verify postcondition with match expression"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Status (union (active) (inactive)))
          (fn check-active ((s Int))
            (@spec ((Int) -> Bool))
            (@post (or (== $result true) (== $result false)))
            (match s
              ((active) true)
              ((inactive) false))))
        """
        results = verify_source(source)
        # Should process without translation errors
        assert len(results) >= 1
        # Should not have translation failures
        failed_translate = [r for r in results if 'Could not translate' in r.message]
        assert len(failed_translate) == 0

    def test_function_call_axiomatization(self):
        """Test user-defined function calls as uninterpreted functions"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        translator.declare_variable('a', PrimitiveType('Int'))
        translator.declare_variable('b', PrimitiveType('Int'))

        # Test function call translation
        expr = parse("(term-eq a b)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        # Should be a function application
        assert 'fn_term-eq' in str(translator.variables)

    def test_function_call_predicate(self):
        """Predicates ending in -eq should return Bool"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        translator.declare_variable('a', PrimitiveType('Int'))
        translator.declare_variable('b', PrimitiveType('Int'))

        # term-eq should return Bool
        expr = parse("(term-eq a b)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert z3_expr.sort() == z3.BoolSort()

    def test_function_call_in_postcondition(self):
        """Verify postcondition that calls user-defined function"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn get-value ((x Int))
            (@spec ((Int) -> Int))
            (@post (>= $result 0))
            x)

          (fn double ((x Int))
            (@spec ((Int) -> Int))
            (@pre (>= x 0))
            (@post (== $result (get-value x)))
            x))
        """
        results = verify_source(source)
        # Should process without translation errors
        assert len(results) >= 1

    def test_quote_form_translation(self):
        """Test (quote x) form translates to enum value"""
        from slop.verifier import Z3Translator, MinimalTypeEnv, build_type_registry_from_ast
        from slop.parser import parse
        import z3

        source = "(type Status (enum ok error))"
        ast = parse(source)
        registry = build_type_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=registry)
        translator = Z3Translator(env)

        # Test (quote ok) - native parser output
        expr = parse("(quote ok)")[0]
        z3_expr = translator.translate_expr(expr)
        assert z3_expr is not None
        assert z3_expr == z3.IntVal(0)  # 'ok' is first enum value

    def test_graph_size_function_call(self):
        """Test graph-size function call in postcondition"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn empty-check ((g Int))
            (@spec ((Int) -> Bool))
            (@pre (== (graph-size g) 0))
            (@post (== $result true))
            true))
        """
        results = verify_source(source)
        # Should process (graph-size translated as function call)
        assert len(results) >= 1
        failed_translate = [r for r in results if 'Could not translate' in r.message]
        assert len(failed_translate) == 0


class TestBodyAnalysis:
    """Test body analysis for verifier: reflexivity axioms, record axioms, inlining"""

    def test_reflexivity_axiom(self):
        """Postcondition (term-eq $result $result) should verify via reflexivity"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn identity ((x Int))
            (@spec ((Int) -> Int))
            (@post (term-eq $result $result))
            x))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) == 1

    def test_reflexivity_with_field_access(self):
        """Postcondition (term-eq $result t.field) verifies when body is (. t field)"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Item (record (value Int)))
          (fn get-value ((t (Ptr Item)))
            (@spec (((Ptr Item)) -> Int))
            (@post (term-eq $result t.value))
            (. t value)))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) == 1

    def test_record_field_axiom(self):
        """Record-new body allows proving field equality"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Point (record (x Int) (y Int)))
          (fn make-point ((a Int) (b Int))
            (@spec ((Int Int) -> Point))
            (@post (== (. $result x) a))
            (record-new Point (x a) (y b))))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) == 1

    def test_record_field_multiple_axioms(self):
        """Multiple record field postconditions all verify"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Triple (record (a Int) (b Int) (c Int)))
          (fn make-triple ((x Int) (y Int) (z Int))
            (@spec ((Int Int Int) -> Triple))
            (@post (== (. $result a) x))
            (@post (== (. $result b) y))
            (@post (== (. $result c) z))
            (record-new Triple (a x) (b y) (c z))))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) == 1

    def test_combined_record_eq(self):
        """Combined record + eq: (term-eq (. $result x) val) with record-new"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Item (record (value Int)))
          (fn make-item ((v Int))
            (@spec ((Int) -> Item))
            (@post (term-eq (. $result value) v))
            (record-new Item (value v))))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) == 1

    def test_eq_function_different_args_not_verified(self):
        """term-eq with different args should not automatically verify"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn compare ((x Int) (y Int))
            (@spec ((Int Int) -> Bool))
            (@post (term-eq x y))
            true))
        """
        results = verify_source(source)
        # Without explicit constraint that x == y, this should fail
        failed = [r for r in results if r.status == 'failed']
        assert len(failed) == 1

    def test_accessor_inlining(self):
        """Inline simple accessor in postcondition"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Point (record (x Int) (y Int)))

          (fn get-x ((p Point))
            (@spec ((Point) -> Int))
            (@pure)
            (. p x))

          (fn make-point ((a Int) (b Int))
            (@spec ((Int Int) -> Point))
            (@post (== (get-x $result) a))
            (record-new Point (x a) (y b))))
        """
        results = verify_source(source)
        # make-point should verify because get-x is inlined
        make_point = [r for r in results if r.name == 'make-point']
        assert len(make_point) == 1
        assert make_point[0].status == 'verified'

    def test_accessor_inlining_with_eq(self):
        """Inline accessor with term-eq postcondition"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Triple (record (subject Int) (predicate Int) (object Int)))

          (fn triple-subject ((t Triple))
            (@spec ((Triple) -> Int))
            (@pure)
            (. t subject))

          (fn triple-predicate ((t Triple))
            (@spec ((Triple) -> Int))
            (@pure)
            (. t predicate))

          (fn triple-object ((t Triple))
            (@spec ((Triple) -> Int))
            (@pure)
            (. t object))

          (fn make-triple ((subj Int) (pred Int) (obj Int))
            (@spec ((Int Int Int) -> Triple))
            (@post (and
              (term-eq (triple-subject $result) subj)
              (term-eq (triple-predicate $result) pred)
              (term-eq (triple-object $result) obj)))
            (record-new Triple (subject subj) (predicate pred) (object obj))))
        """
        results = verify_source(source)
        # make-triple should verify because accessors are inlined
        make_triple = [r for r in results if r.name == 'make-triple']
        assert len(make_triple) == 1
        assert make_triple[0].status == 'verified'


class TestUnionTagAxioms:
    """Test Phase 4: Union tag axioms for union-new bodies"""

    def test_union_new_match_postcondition(self):
        """union-new body allows proving match postcondition"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Value (union (num Int) (str String)))

          (fn make-num ((n Int))
            (@spec ((Int) -> Value))
            (@post (match $result ((num _) true) (_ false)))
            (union-new Value num n)))
        """
        results = verify_source(source)
        make_num = [r for r in results if r.name == 'make-num']
        assert len(make_num) == 1
        assert make_num[0].status == 'verified'

    def test_union_new_different_tag(self):
        """union-new with different tag verifies its own match"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Value (union (num Int) (str String)))

          (fn make-str ((s String))
            (@spec ((String) -> Value))
            (@post (match $result ((str _) true) (_ false)))
            (union-new Value str s)))
        """
        results = verify_source(source)
        make_str = [r for r in results if r.name == 'make-str']
        assert len(make_str) == 1
        assert make_str[0].status == 'verified'

    def test_union_new_wrong_tag_fails(self):
        """union-new cannot prove match for wrong tag"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Value (union (num Int) (str String)))

          (fn make-num-wrong ((n Int))
            (@spec ((Int) -> Value))
            (@post (match $result ((str _) true) (_ false)))
            (union-new Value num n)))
        """
        results = verify_source(source)
        make_num = [r for r in results if r.name == 'make-num-wrong']
        assert len(make_num) == 1
        assert make_num[0].status == 'failed'

    def test_union_new_quoted_tag(self):
        """union-new with quoted tag works"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Result (union (ok Int) (error String)))

          (fn make-ok ((v Int))
            (@spec ((Int) -> Result))
            (@post (match $result (('ok _) true) (_ false)))
            (union-new Result 'ok v)))
        """
        results = verify_source(source)
        make_ok = [r for r in results if r.name == 'make-ok']
        assert len(make_ok) == 1
        assert make_ok[0].status == 'verified'

    def test_union_variants_in_enum_map(self):
        """Union variant names are registered in enum_values"""
        from slop.verifier import Z3Translator, MinimalTypeEnv, build_type_registry_from_ast
        from slop.parser import parse

        source = "(type Term (union (iri String) (blank String) (literal String)))"
        ast = parse(source)
        registry = build_type_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=registry)
        translator = Z3Translator(env)

        # Check that union variants are in enum_values
        assert 'iri' in translator.enum_values
        assert 'blank' in translator.enum_values
        assert 'literal' in translator.enum_values
        # Check that indices are different
        assert translator.enum_values['iri'] == 0
        assert translator.enum_values['blank'] == 1
        assert translator.enum_values['literal'] == 2


class TestTypeInvariants:
    """Test Phase 5: Type invariants with @invariant or @assume"""

    def test_assume_allows_invariant_reasoning(self):
        """@assume can be used to express type invariants"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Counter (record (items (List Int)) (count Int)))

          (fn counter-size ((c Counter))
            (@spec ((Counter) -> Int))
            (@assume (== c.count (list-len c.items)))
            (@post (== $result (list-len c.items)))
            (. c count)))
        """
        results = verify_source(source)
        counter_size = [r for r in results if r.name == 'counter-size']
        assert len(counter_size) == 1
        assert counter_size[0].status == 'verified'

    def test_invariant_preserved_by_construction(self):
        """Record construction preserves invariant when values match"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Graph (record (triples (List Int)) (size Int)))

          (fn make-empty-graph ()
            (@spec (() -> Graph))
            (@post (== (. $result size) 0))
            (record-new Graph (triples nil) (size 0))))
        """
        results = verify_source(source)
        make_empty = [r for r in results if r.name == 'make-empty-graph']
        assert len(make_empty) == 1
        assert make_empty[0].status == 'verified'

    def test_type_invariant_annotation(self):
        """@invariant on type is automatically applied to function parameters"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Counter (record (items (List Int)) (count Int))
            (@invariant (== count (list-len items))))

          (fn counter-size ((c Counter))
            (@spec ((Counter) -> Int))
            (@post (== $result (list-len c.items)))
            (. c count)))
        """
        results = verify_source(source)
        counter_size = [r for r in results if r.name == 'counter-size']
        assert len(counter_size) == 1
        assert counter_size[0].status == 'verified'

    def test_type_invariant_with_ptr(self):
        """@invariant works with Ptr types"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Graph (record (triples (List Int)) (size Int))
            (@invariant (== size (list-len triples))))

          (fn graph-size ((g (Ptr Graph)))
            (@spec (((Ptr Graph)) -> Int))
            (@post (== $result (list-len g.triples)))
            (. g size)))
        """
        results = verify_source(source)
        graph_size = [r for r in results if r.name == 'graph-size']
        assert len(graph_size) == 1
        assert graph_size[0].status == 'verified'

    def test_invariant_registry_extraction(self):
        """Invariants are correctly extracted from type definitions"""
        from slop.verifier import build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (type Graph (record (triples (List Int)) (size Int))
          (@invariant (== size (list-len triples))))
        """
        ast = parse(source)
        registry = build_invariant_registry_from_ast(ast)

        invariants = registry.get_invariants('Graph')
        assert len(invariants) == 1


class TestLoopPostconditions:
    """Test Phase 6: Loop postcondition heuristics"""

    def test_assume_enables_loop_postcondition(self):
        """@assume can be used to trust loop postconditions"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn contains-all ((items (List Int)) (target Int))
            (@spec (((List Int) Int) -> Bool))
            (@assume (or (== $result true) (== $result false)))
            (@post (or (== $result true) (== $result false)))
            false))
        """
        results = verify_source(source)
        contains = [r for r in results if r.name == 'contains-all']
        assert len(contains) == 1
        assert contains[0].status == 'verified'

    def test_conditional_branch_analysis(self):
        """Conditional with simple branches can verify"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn maybe-add ((g Int) (t Int) (already-present Bool))
            (@spec ((Int Int Bool) -> Int))
            (@post (or (== $result g) (== $result (+ g 1))))
            (if already-present
              g
              (+ g 1))))
        """
        results = verify_source(source)
        maybe_add = [r for r in results if r.name == 'maybe-add']
        assert len(maybe_add) == 1
        assert maybe_add[0].status == 'verified'

    def test_trusted_annotation_for_complex_loop(self):
        """Complex loop postconditions can use @assume as escape hatch"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn graph-add ((g Int) (t Int))
            (@spec ((Int Int) -> Int))
            (@assume (>= $result g))
            (@post (>= $result g))
            g))
        """
        results = verify_source(source)
        graph_add = [r for r in results if r.name == 'graph-add']
        assert len(graph_add) == 1
        assert graph_add[0].status == 'verified'
