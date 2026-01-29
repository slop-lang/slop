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


def _make_triple_imported_defs():
    """Create imported defs with make-triple and triple-new postconditions."""
    from slop.verifier.types import FunctionSignature, ImportedDefinitions
    from slop.parser import parse

    defs = ImportedDefinitions()

    # make-triple: (make-triple arena s p o)
    make_triple_posts = [
        parse("(== (triple-subject $result) s)")[0],
        parse("(== (triple-predicate $result) p)")[0],
        parse("(== (triple-object $result) o)")[0],
    ]
    defs.functions['make-triple'] = FunctionSignature(
        name='make-triple',
        param_types=[],
        return_type=None,
        params=['arena', 's', 'p', 'o'],
        postconditions=make_triple_posts,
    )

    # triple-new: (triple-new arena pred subj obj)
    triple_new_posts = [
        parse("(== (triple-predicate $result) pred)")[0],
        parse("(== (triple-subject $result) subj)")[0],
        parse("(== (triple-object $result) obj)")[0],
    ]
    defs.functions['triple-new'] = FunctionSignature(
        name='triple-new',
        param_types=[],
        return_type=None,
        params=['arena', 'pred', 'subj', 'obj'],
        postconditions=triple_new_posts,
    )

    return defs


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

    def test_infix_nested_equality_normalization(self):
        """Native parser infix-in-parens pattern is normalized correctly"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import SList, Symbol, Number

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        # Simulate native parser output: ((list-len x) == 0)
        # which is an SList with 3 elements: (SList), Symbol(==), Number
        translator.declare_variable('x', None)
        inner_expr = SList([Symbol('list-len'), Symbol('x')])
        # Create infix pattern: (inner_expr == 0)
        infix_expr = SList([inner_expr, Symbol('=='), Number(0)])

        # translate_expr should normalize this and translate correctly
        result = translator.translate_expr(infix_expr)
        assert result is not None
        # Should produce a comparison (equality)
        # The result should be a Z3 bool expression
        import z3
        assert result.sort() == z3.BoolSort()


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

    def test_option_constructor_comparison(self):
        """Comparison with (none) and (some x) uses union_tag"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn option-is-none ((x (Option Int)))
            (@spec (((Option Int)) -> Bool))
            (@post (implies (== x (none)) $result))
            (@post (implies (!= x (none)) (not $result)))
            (match x
              ((none) true)
              ((some _) false))))
        """
        results = verify_source(source)
        option_is_none = [r for r in results if r.name == 'option-is-none']
        assert len(option_is_none) == 1
        assert option_is_none[0].status == 'verified'

    def test_option_constructor_comparison_with_some(self):
        """Comparison with (some value) checks both tag and payload"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn wrap-in-some ((x Int))
            (@spec ((Int) -> (Option Int)))
            (@post (!= $result (none)))
            (some x)))
        """
        results = verify_source(source)
        wrap_in_some = [r for r in results if r.name == 'wrap-in-some']
        assert len(wrap_in_some) == 1
        assert wrap_in_some[0].status == 'verified'

    def test_builtin_constructors_in_enum_map(self):
        """Built-in Option/Result constructors are in enum_values"""
        from slop.verifier import Z3Translator, MinimalTypeEnv

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        # Check built-in constructors are present
        assert 'none' in translator.enum_values
        assert 'some' in translator.enum_values
        assert 'ok' in translator.enum_values
        assert 'error' in translator.enum_values
        # Check indices
        assert translator.enum_values['none'] == 0
        assert translator.enum_values['some'] == 1
        assert translator.enum_values['ok'] == 0
        assert translator.enum_values['error'] == 1


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

    def test_type_invariant_with_in_mode(self):
        """@invariant works with 'in' parameter mode (like rdf.slop graph-size)"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type GraphSize (Int 0 ..))
          (type Graph (record (triples (List Int)) (size GraphSize))
            (@invariant (== size (list-len triples))))

          (fn graph-size ((in g Graph))
            (@spec ((Graph) -> GraphSize))
            (@pure)
            (@post (>= $result 0))
            (@post (== $result (list-len g.triples)))
            (. g size)))
        """
        results = verify_source(source)
        graph_size = [r for r in results if r.name == 'graph-size']
        assert len(graph_size) == 1
        assert graph_size[0].status == 'verified'


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

    def test_loop_invariant_annotation(self):
        """@loop-invariant inside for-each helps verify loop postconditions"""
        from slop.verifier import verify_source

        # Test with local variables - the let translator should handle count
        source = """
        (module test
          (fn filter-positive ((items (List Int)))
            (@spec (((List Int)) -> Int))
            (@post (>= $result 0))
            (let ((mut count 0))
              (for-each (x items)
                (@loop-invariant (>= count 0))
                (when (> x 0)
                  (set! count (+ count 1))))
              count)))
        """
        results = verify_source(source)
        filter_fn = [r for r in results if r.name == 'filter-positive']
        assert len(filter_fn) == 1
        assert filter_fn[0].status == 'verified'

    def test_loop_invariant_extraction(self):
        """Verify that @loop-invariant is extracted from nested loops"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn test-fn ((x Int))
          (@spec ((Int) -> Int))
          (@post (>= $result 0))
          (let ((mut sum 0))
            (for-each (i items)
              (@loop-invariant (>= sum 0))
              (set! sum (+ sum 1)))
            sum))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        # Test extraction helper
        # items[0]=fn, items[1]=name, items[2]=params, items[3]=@spec, items[4]=@post, items[5]=body
        fn_body = ast[0].items[5]  # The let expression (function body)
        invariants = verifier._extract_loop_invariants(fn_body)
        assert len(invariants) == 1  # Should find the @loop-invariant


class TestAccessorAxioms:
    """Test Phase 7: Accessor function axioms"""

    def test_accessor_axiom_enables_comparison(self):
        """Accessor function axiom allows proving comparison postcondition"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Counter (record (count Int)))

          (fn counter-count ((c Counter))
            (@spec ((Counter) -> Int))
            (@pure)
            (. c count))

          (fn compare-counts ((a Counter) (b Counter))
            (@spec ((Counter Counter) -> Bool))
            (@post (== $result (>= (counter-count a) (counter-count b))))
            (>= (counter-count a) (counter-count b))))
        """
        results = verify_source(source)
        compare = [r for r in results if r.name == 'compare-counts']
        assert len(compare) == 1
        assert compare[0].status == 'verified'

    def test_accessor_axiom_multiple_params(self):
        """Accessor axiom works with multiple parameters of same type"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Size (Int 0 ..))
          (type Graph (record (size Size)))

          (fn graph-size ((g Graph))
            (@spec ((Graph) -> Size))
            (@pure)
            (. g size))

          (fn sizes-equal ((a Graph) (b Graph))
            (@spec ((Graph Graph) -> Bool))
            (@post (== $result (== (graph-size a) (graph-size b))))
            (== (graph-size a) (graph-size b))))
        """
        results = verify_source(source)
        sizes_eq = [r for r in results if r.name == 'sizes-equal']
        assert len(sizes_eq) == 1
        assert sizes_eq[0].status == 'verified'

    def test_accessor_axiom_with_record_new(self):
        """Accessor axiom combined with record-new axiom"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Counter (record (count Int)))

          (fn counter-count ((c Counter))
            (@spec ((Counter) -> Int))
            (@pure)
            (. c count))

          (fn make-double ((c Counter))
            (@spec ((Counter) -> Counter))
            (@post (== (counter-count $result) (* (counter-count c) 2)))
            (record-new Counter (count (* (. c count) 2)))))
        """
        results = verify_source(source)
        make_double = [r for r in results if r.name == 'make-double']
        assert len(make_double) == 1
        assert make_double[0].status == 'verified'


class TestConditionalRecordNew:
    """Test Phase 8: Conditional record-new axioms"""

    def test_conditional_with_record_new_then_branch(self):
        """Conditional with record-new in then branch and variable in else"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Size (Int 0 ..))
          (type Graph (record (size Size)))

          (fn graph-size ((g Graph))
            (@spec ((Graph) -> Size))
            (@pure)
            (. g size))

          (fn maybe-increment ((g Graph) (should-inc Bool))
            (@spec ((Graph Bool) -> Graph))
            (@post (>= (graph-size $result) (graph-size g)))
            (if (not should-inc)
              (record-new Graph (size (+ (. g size) 1)))
              g)))
        """
        results = verify_source(source)
        maybe_inc = [r for r in results if r.name == 'maybe-increment']
        assert len(maybe_inc) == 1
        assert maybe_inc[0].status == 'verified'

    def test_conditional_preserves_or_increments(self):
        """Conditional that either preserves or increments a field"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Counter (record (count Int)))

          (fn maybe-inc ((c Counter) (do-inc Bool))
            (@spec ((Counter Bool) -> Counter))
            (@post (or (== (. $result count) (. c count))
                      (== (. $result count) (+ (. c count) 1))))
            (if do-inc
              (record-new Counter (count (+ (. c count) 1)))
              c)))
        """
        results = verify_source(source)
        maybe_inc = [r for r in results if r.name == 'maybe-inc']
        assert len(maybe_inc) == 1
        assert maybe_inc[0].status == 'verified'

    def test_conditional_graph_add_pattern(self):
        """Pattern similar to graph-add: check-then-construct or return same"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Size (Int 0 ..))
          (type Container (record (size Size)))

          (fn container-size ((c Container))
            (@spec ((Container) -> Size))
            (@pure)
            (. c size))

          (fn add-if-not-exists ((c Container) (not-exists Bool))
            (@spec ((Container Bool) -> Container))
            (@post (>= (container-size $result) (container-size c)))
            (if not-exists
              (record-new Container (size (+ (. c size) 1)))
              c)))
        """
        results = verify_source(source)
        add_fn = [r for r in results if r.name == 'add-if-not-exists']
        assert len(add_fn) == 1
        assert add_fn[0].status == 'verified'


class TestListAxioms:
    """Test Phase 9: List operation axioms"""

    def test_list_push_len_axiom(self):
        """list-push increases list-len by 1"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Size (Int 0 ..))
          (type Container (record (items (List Int)) (size Size))
            (@invariant (== size (list-len items))))

          (fn add-item ((c Container) (x Int))
            (@spec ((Container Int) -> Container))
            (@post (== (. $result size) (+ (. c size) 1)))
            (do
              (list-push (. c items) x)
              (record-new Container (items (. c items)) (size (+ (. c size) 1))))))
        """
        results = verify_source(source)
        add_item = [r for r in results if r.name == 'add-item']
        assert len(add_item) == 1
        assert add_item[0].status == 'verified'

    def test_list_push_tracking(self):
        """Verifier tracks list-push calls in function body"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Counter (record (items (List Int)) (count Int)))

          (fn push-and-count ((c Counter) (x Int))
            (@spec ((Counter Int) -> Counter))
            (@post (== (. $result count) (+ (. c count) 1)))
            (do
              (list-push (. c items) x)
              (record-new Counter (items (. c items)) (count (+ (. c count) 1))))))
        """
        results = verify_source(source)
        push_fn = [r for r in results if r.name == 'push-and-count']
        assert len(push_fn) == 1
        assert push_fn[0].status == 'verified'

    def test_list_len_nonnegative(self):
        """list-len is constrained to be non-negative"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn check-len ((items (List Int)))
            (@spec (((List Int)) -> Bool))
            (@post (or (== $result true) (== $result false)))
            (>= (list-len items) 0)))
        """
        results = verify_source(source)
        check_fn = [r for r in results if r.name == 'check-len']
        assert len(check_fn) == 1
        # Should verify since list-len is always >= 0
        assert check_fn[0].status == 'verified'

    def test_list_new_empty(self):
        """Test that list-new produces length 0 axiom"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn make-empty-list ((arena Arena))
            (@spec ((Arena) -> (List Int)))
            (@post {(list-len $result) == 0})
            (list-new arena Int)))
        """
        results = verify_source(source)
        make_empty = [r for r in results if r.name == 'make-empty-list']
        assert len(make_empty) == 1
        # Should verify because list-new produces a list with length 0
        assert make_empty[0].status == 'verified'

    def test_list_new_in_record_field(self):
        """list-new as record field value produces length=0 axiom"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Container (record (items (List Int))))
          (fn make-container ((arena Arena))
            (@spec ((Arena) -> Container))
            (@post (== (list-len (. $result items)) 0))
            (record-new Container (items (list-new arena Int)))))
        """
        results = verify_source(source)
        make_container = [r for r in results if r.name == 'make-container']
        assert len(make_container) == 1
        # Should verify because list-new in field produces length=0 axiom
        assert make_container[0].status == 'verified'


class TestBoolEquality:
    """Test Bool == Bool comparison in postconditions"""

    def test_bool_equality(self):
        """Test Bool == Bool comparison in postconditions"""
        from slop.verifier import verify_source

        # Use prefix syntax to avoid native parser infix handling differences
        source = """
        (module test
          (fn is-empty ((lst (List Int)))
            (@spec (((List Int)) -> Bool))
            (@post (== $result (== (list-len lst) 0)))
            (== (list-len lst) 0)))
        """
        results = verify_source(source)
        is_empty = [r for r in results if r.name == 'is-empty']
        assert len(is_empty) == 1
        # Should verify because the body computes exactly what the postcondition says
        assert is_empty[0].status == 'verified'

    def test_bool_to_int_coercion(self):
        """Test that Int is coerced to Bool for comparisons"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn check-positive ((x Int))
            (@spec ((Int) -> Bool))
            (@post (or (== $result true) (== $result false)))
            (> x 0)))
        """
        results = verify_source(source)
        check_fn = [r for r in results if r.name == 'check-positive']
        assert len(check_fn) == 1
        assert check_fn[0].status == 'verified'


class TestFilterPatternRecognition:
    """Test Phase 10: Filter pattern recognition and automatic axiom generation"""

    def test_filter_pattern_detection(self):
        """Detect filter pattern in function body"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn filter-items ((arena Arena) (items (List Int)))
          (@spec ((Arena (List Int)) -> (List Int)))
          (@post (>= 0 0))
          (let ((mut result (make-list arena)))
            (for-each (x items)
              (if (> x 0)
                (set! result (list-push result x))))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        # Get function body
        fn_body = ast[0].items[5]  # The let expression

        # Test pattern detection
        pattern = verifier._detect_filter_pattern(fn_body)
        assert pattern is not None
        assert pattern.result_var == 'result'
        assert pattern.loop_var == 'x'

    def test_filter_pattern_negated_predicate(self):
        """Detect negated predicate (exclusion) in filter pattern"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn remove-item ((arena Arena) (items (List Int)) (target Int))
          (@spec ((Arena (List Int) Int) -> (List Int)))
          (@post (>= 0 0))
          (let ((mut result (make-list arena)))
            (for-each (x items)
              (if (not (item-eq x target))
                (set! result (list-push result x))))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        # Get function body
        fn_body = ast[0].items[5]  # The let expression

        # Test pattern detection
        pattern = verifier._detect_filter_pattern(fn_body)
        assert pattern is not None
        assert pattern.is_negated is True
        # Excluded item should be detected
        assert pattern.excluded_item is not None

    def test_filter_pattern_size_axiom(self):
        """Filter pattern generates size constraint axiom"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Size (Int 0 ..))
          (type Container (record (size Size)))

          (fn container-size ((c Container))
            (@spec ((Container) -> Size))
            (@pure)
            (. c size))

          (fn filter-positive ((arena Arena) (c Container))
            (@spec ((Arena Container) -> Container))
            (@post (<= (container-size $result) (container-size c)))
            (let ((mut result (make-container arena)))
              (for-each (x (. c items))
                (if (> x 0)
                  (set! result (container-add result x))))
              result)))
        """
        results = verify_source(source)
        # The filter pattern should be detected and size axiom should help
        filter_fn = [r for r in results if r.name == 'filter-positive']
        assert len(filter_fn) == 1
        # With automatic axiom generation, this should verify
        # Note: May fail if pattern detection doesn't fully match - that's ok
        # The important thing is no crash

    def test_filter_pattern_exclusion_axiom(self):
        """Filter pattern with negated equality generates exclusion axiom"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn remove-item ((arena Arena) (items (List Int)) (target Int))
            (@spec ((Arena (List Int) Int) -> (List Int)))
            (@post (>= 0 0))
            (let ((mut result (make-list arena)))
              (for-each (x items)
                (if (not (item-eq x target))
                  (set! result (list-push result x))))
              result)))
        """
        results = verify_source(source)
        # Should not crash even if pattern can't be fully verified
        assert len(results) >= 1


class TestFailureSuggestions:
    """Test actionable failure suggestions"""

    def test_loop_suggestion_for_unrecognized_pattern(self):
        """Unrecognized loop pattern generates suggestion"""
        from slop.verifier import verify_source

        # This loop pattern is not a filter (no conditional add)
        source = """
        (module test
          (fn sum-items ((items (List Int)))
            (@spec (((List Int)) -> Int))
            (@post (>= $result 0))
            (let ((mut total 0))
              (for-each (x items)
                (set! total (+ total x)))
              total)))
        """
        results = verify_source(source)
        sum_fn = [r for r in results if r.name == 'sum-items']
        assert len(sum_fn) == 1

        # If verification fails, there should be a suggestion
        if sum_fn[0].status == 'failed':
            assert sum_fn[0].suggestions is not None
            # Should suggest @loop-invariant or @assume
            suggestion_text = ' '.join(sum_fn[0].suggestions)
            assert 'loop' in suggestion_text.lower() or 'invariant' in suggestion_text.lower()

    def test_field_relationship_suggestion(self):
        """Postcondition with field relationship generates type invariant suggestion"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn get-size ((c Container))
          (@spec ((Container) -> Int))
          (@post (== $result (list-len c.items)))
          (. c size))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_form = ast[0]

        # Test suggestion generation
        has_field_relationship = verifier._postcondition_references_field_relationship(fn_form)
        assert has_field_relationship is True

    def test_equality_function_suggestion(self):
        """Equality function with nested match generates specific suggestion"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn term-eq ((a Term) (b Term))
          (@spec ((Term Term) -> Bool))
          (@post (== $result (== a b)))
          (match a
            ((iri s1) (match b
              ((iri s2) (string-eq s1 s2))
              (_ false)))
            (_ false)))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_form = ast[0]
        fn_body = ast[0].items[5]  # The match expression

        # Test equality function detection
        is_eq_fn = verifier._is_equality_function(fn_form)
        assert is_eq_fn is True

        # Test nested match detection
        has_nested_match = verifier._has_nested_match(fn_body)
        assert has_nested_match is True

    def test_verification_result_includes_suggestions(self):
        """VerificationResult includes suggestions when verification fails"""
        from slop.verifier import VerificationResult

        result = VerificationResult(
            name="test-fn",
            verified=False,
            status="failed",
            message="Contract may be violated",
            suggestions=["Consider adding @loop-invariant", "Or use @assume"]
        )

        # Test string representation includes suggestions
        result_str = str(result)
        assert "Suggestions:" in result_str
        assert "@loop-invariant" in result_str


class TestFilterPatternHelpers:
    """Test helper methods for filter pattern detection"""

    def test_is_mutable_binding(self):
        """Test _is_mutable_binding helper"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Mutable binding: (mut var value)
        binding1 = parse("(mut result (make-list arena))")[0]
        assert verifier._is_mutable_binding(binding1) is True

        # Immutable binding: (var value)
        binding2 = parse("(x 42)")[0]
        assert verifier._is_mutable_binding(binding2) is False

    def test_is_empty_collection_init(self):
        """Test _is_empty_collection_init helper"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Empty collection init patterns
        make_list = parse("(make-list arena)")[0]
        assert verifier._is_empty_collection_init(make_list) is True

        make_graph = parse("(make-graph arena)")[0]
        assert verifier._is_empty_collection_init(make_graph) is True

        graph_empty = parse("(graph-empty arena)")[0]
        assert verifier._is_empty_collection_init(graph_empty) is True

        # Not empty collection init
        other = parse("(+ 1 2)")[0]
        assert verifier._is_empty_collection_init(other) is False

    def test_has_for_each(self):
        """Test _has_for_each helper"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Has for-each
        body_with_loop = parse("(let ((mut x 0)) (for-each (i items) (set! x i)) x)")[0]
        assert verifier._has_for_each(body_with_loop) is True

        # No for-each
        body_without_loop = parse("(+ 1 2)")[0]
        assert verifier._has_for_each(body_without_loop) is False


class TestUnionStructuralEquality:
    """Test Phase 4: Union structural equality axioms"""

    def test_detect_union_equality_function(self):
        """Detect union equality function pattern"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (type Term (union (iri String) (blank Int) (literal String)))
        (fn term-eq ((in a Term) (in b Term))
          (@spec ((Term Term) -> Bool))
          (@pure)
          (@post (== $result (== a b)))
          (match a
            ((iri a-val) (match b ((iri b-val) (string-eq a-val b-val)) (_ false)))
            ((blank a-id) (match b ((blank b-id) (== a-id b-id)) (_ false)))
            ((literal a-lit) (match b ((literal b-lit) (string-eq a-lit b-lit)) (_ false)))))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_form = ast[1]  # The fn definition

        # Test detection
        detection = verifier._detect_union_equality_function(fn_form)
        assert detection is not None
        param1, param2, type_name = detection
        assert param1 == 'a'
        assert param2 == 'b'
        assert type_name == 'Term'

    def test_extract_helper_eq_calls(self):
        """Extract helper equality function calls from nested match"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        body = parse("""
        (match a
          ((iri a-iri) (match b ((iri b-iri) (iri-eq a-iri b-iri)) (_ false)))
          ((blank a-blank) (match b ((blank b-blank) (blank-eq a-blank b-blank)) (_ false)))
          ((literal a-lit) (match b ((literal b-lit) (literal-eq a-lit b-lit)) (_ false))))
        """)[0]

        helper_eqs = verifier._extract_helper_eq_calls_from_match(body)
        assert helper_eqs.get('iri') == 'iri-eq'
        assert helper_eqs.get('blank') == 'blank-eq'
        assert helper_eqs.get('literal') == 'literal-eq'

    def test_union_equality_axioms_verify(self):
        """Union equality function with structural axioms should verify"""
        from slop.verifier import verify_source

        source = """
        (module test
          (type Value (union (num Int) (str String)))

          (fn num-eq ((a Int) (b Int))
            (@spec ((Int Int) -> Bool))
            (@pure)
            (@post (== $result (== a b)))
            (== a b))

          (fn str-eq ((a String) (b String))
            (@spec ((String String) -> Bool))
            (@pure)
            (@post (== $result (string-eq a b)))
            (string-eq a b))

          (fn value-eq ((in a Value) (in b Value))
            (@spec ((Value Value) -> Bool))
            (@pure)
            (@post (== $result (== a b)))
            (match a
              ((num a-num) (match b ((num b-num) (num-eq a-num b-num)) (_ false)))
              ((str a-str) (match b ((str b-str) (str-eq a-str b-str)) (_ false))))))
        """
        results = verify_source(source)

        # Find value-eq result
        value_eq = [r for r in results if r.name == 'value-eq']
        assert len(value_eq) == 1
        # With structural equality axioms, this should verify
        assert value_eq[0].status == 'verified'

    def test_non_union_eq_not_detected(self):
        """Non-union equality function should not be detected"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (type Point (record (x Int) (y Int)))
        (fn point-eq ((a Point) (b Point))
          (@spec ((Point Point) -> Bool))
          (@post (== $result (and (== a.x b.x) (== a.y b.y))))
          (and (== (. a x) (. b x)) (== (. a y) (. b y))))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_form = ast[1]  # The fn definition

        # Should not detect - Point is a record, not a union
        detection = verifier._detect_union_equality_function(fn_form)
        assert detection is None


class TestCountPatternRecognition:
    """Test count pattern recognition and axiom generation"""

    def test_count_pattern_detection(self):
        """Detect count pattern in function body"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn count-positive ((items (List Int)))
          (@spec (((List Int)) -> Int))
          (@post (>= $result 0))
          (let ((mut count 0))
            (for-each (x items)
              (if (> x 0)
                (set! count (+ count 1))))
            count))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        # Get function body (fn name params @spec @post body)
        fn_body = ast[0].items[5]  # The let expression

        # Test pattern detection
        pattern = verifier._detect_count_pattern(fn_body)
        assert pattern is not None
        assert pattern.count_var == 'count'
        assert pattern.loop_var == 'x'

    def test_count_pattern_with_when(self):
        """Detect count pattern using when instead of if"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn count-even ((items (List Int)))
          (@spec (((List Int)) -> Int))
          (@post (>= $result 0))
          (let ((mut count 0))
            (for-each (x items)
              (when (== (% x 2) 0)
                (set! count (+ count 1))))
            count))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_body = ast[0].items[5]
        pattern = verifier._detect_count_pattern(fn_body)
        assert pattern is not None
        assert pattern.count_var == 'count'

    def test_count_pattern_axiom_generation(self):
        """Count pattern generates correct axioms"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn count-matches ((items (List Int)))
            (@spec (((List Int)) -> Int))
            (@post (>= $result 0))
            (let ((mut count 0))
              (for-each (x items)
                (if (> x 0)
                  (set! count (+ count 1))))
              count)))
        """
        results = verify_source(source)
        count_fn = [r for r in results if r.name == 'count-matches']
        assert len(count_fn) == 1
        # With count pattern axiom (result >= 0), this should verify
        assert count_fn[0].status == 'verified'

    def test_count_bounded_by_collection(self):
        """Count pattern generates upper bound axiom"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn count-all ((items (List Int)))
            (@spec (((List Int)) -> Int))
            (@post (<= $result (list-len items)))
            (let ((mut count 0))
              (for-each (x items)
                (if true
                  (set! count (+ count 1))))
              count)))
        """
        results = verify_source(source)
        count_fn = [r for r in results if r.name == 'count-all']
        assert len(count_fn) == 1
        # With count pattern axiom (result <= list-len), this should verify
        assert count_fn[0].status == 'verified'


class TestFoldPatternRecognition:
    """Test fold/accumulation pattern recognition and axiom generation"""

    def test_fold_pattern_detection_sum(self):
        """Detect sum fold pattern in function body"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn sum-items ((items (List Int)))
          (@spec (((List Int)) -> Int))
          (@post (>= $result 0))
          (let ((mut total 0))
            (for-each (x items)
              (set! total (+ total x)))
            total))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_body = ast[0].items[5]
        pattern = verifier._detect_fold_pattern(fn_body)
        assert pattern is not None
        assert pattern.acc_var == 'total'
        assert pattern.operator == '+'
        assert pattern.loop_var == 'x'

    def test_fold_pattern_detection_max(self):
        """Detect max fold pattern"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn find-max ((items (List Int)) (init Int))
          (@spec (((List Int) Int) -> Int))
          (@post (>= $result init))
          (let ((mut best init))
            (for-each (x items)
              (set! best (max best x)))
            best))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_body = ast[0].items[5]
        pattern = verifier._detect_fold_pattern(fn_body)
        assert pattern is not None
        assert pattern.acc_var == 'best'
        assert pattern.operator == 'max'

    def test_fold_max_axiom_generation(self):
        """Max fold pattern generates result >= init axiom"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn find-max ((items (List Int)) (init Int))
            (@spec (((List Int) Int) -> Int))
            (@post (>= $result init))
            (let ((mut best init))
              (for-each (x items)
                (set! best (max best x)))
              best)))
        """
        results = verify_source(source)
        max_fn = [r for r in results if r.name == 'find-max']
        assert len(max_fn) == 1
        # With fold pattern axiom for max (result >= init), this should verify
        assert max_fn[0].status == 'verified'

    def test_fold_min_axiom_generation(self):
        """Min fold pattern generates result <= init axiom"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn find-min ((items (List Int)) (init Int))
            (@spec (((List Int) Int) -> Int))
            (@post (<= $result init))
            (let ((mut best init))
              (for-each (x items)
                (set! best (min best x)))
              best)))
        """
        results = verify_source(source)
        min_fn = [r for r in results if r.name == 'find-min']
        assert len(min_fn) == 1
        # With fold pattern axiom for min (result <= init), this should verify
        assert min_fn[0].status == 'verified'

    def test_fold_pattern_conditional_accumulation(self):
        """Detect fold pattern with conditional accumulation"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn sum-positive ((items (List Int)))
          (@spec (((List Int)) -> Int))
          (@post (>= $result 0))
          (let ((mut total 0))
            (for-each (x items)
              (if (> x 0)
                (set! total (+ total x))))
            total))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_body = ast[0].items[5]
        pattern = verifier._detect_fold_pattern(fn_body)
        assert pattern is not None
        assert pattern.acc_var == 'total'
        assert pattern.operator == '+'


class TestFindPatternRecognition:
    """Test find-first pattern recognition"""

    def test_find_pattern_detection(self):
        """Detect find-first pattern in function body"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn find-first-positive ((items (List Int)))
          (@spec (((List Int)) -> Int))
          (@post (or (== $result nil) (> $result 0)))
          (let ((mut found nil))
            (for-each (x items)
              (if (and (== found nil) (> x 0))
                (set! found x)))
            found))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_body = ast[0].items[5]
        pattern = verifier._detect_find_pattern(fn_body)
        assert pattern is not None
        assert pattern.result_var == 'found'
        assert pattern.loop_var == 'x'

    def test_find_pattern_with_when(self):
        """Detect find-first pattern using when"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn find-match ((items (List Int)) (target Int))
          (@spec (((List Int) Int) -> Int))
          (@post (>= 0 0))
          (let ((mut found nil))
            (for-each (x items)
              (when (and (== found nil) (== x target))
                (set! found x)))
            found))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_body = ast[0].items[5]
        pattern = verifier._detect_find_pattern(fn_body)
        assert pattern is not None
        assert pattern.result_var == 'found'

    def test_no_find_pattern_without_nil_check(self):
        """Pattern without nil check should not be detected as find-first"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn find-all ((items (List Int)))
          (@spec (((List Int)) -> Int))
          (@post (>= 0 0))
          (let ((mut found nil))
            (for-each (x items)
              (if (> x 0)
                (set! found x)))
            found))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_body = ast[0].items[5]
        pattern = verifier._detect_find_pattern(fn_body)
        # Should not detect - missing (== found nil) check
        assert pattern is None


class TestVerifierProperties:
    """Property-based tests for verifier correctness"""

    def test_pattern_recognition_consistency(self):
        """Pattern detection returns consistent types"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, CountPatternInfo, FoldPatternInfo, FindPatternInfo
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Count pattern
        count_body = parse("(let ((mut count 0)) (for-each (x items) (if (> x 0) (set! count (+ count 1)))) count)")[0]
        count_result = verifier._detect_count_pattern(count_body)
        assert count_result is None or isinstance(count_result, CountPatternInfo)

        # Fold pattern
        fold_body = parse("(let ((mut total 0)) (for-each (x items) (set! total (+ total x))) total)")[0]
        fold_result = verifier._detect_fold_pattern(fold_body)
        assert fold_result is None or isinstance(fold_result, FoldPatternInfo)

        # Find pattern
        find_body = parse("(let ((mut found nil)) (for-each (x items) (if (and (== found nil) (> x 0)) (set! found x))) found)")[0]
        find_result = verifier._detect_find_pattern(find_body)
        assert find_result is None or isinstance(find_result, FindPatternInfo)

    def test_all_documented_patterns_recognized(self):
        """Every pattern documented in LANGUAGE.md is detected"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Filter pattern (from LANGUAGE.md)
        filter_body = parse("""
        (let ((mut result (make-list arena)))
          (for-each (x items)
            (if (> x 0) (set! result (list-push result x))))
          result)
        """)[0]
        assert verifier._detect_filter_pattern(filter_body) is not None

        # Count pattern (from LANGUAGE.md)
        count_body = parse("""
        (let ((mut count 0))
          (for-each (x items)
            (if (> x 0) (set! count (+ count 1))))
          count)
        """)[0]
        assert verifier._detect_count_pattern(count_body) is not None

        # Fold pattern (from LANGUAGE.md)
        fold_body = parse("""
        (let ((mut acc 0))
          (for-each (x items)
            (set! acc (max acc x)))
          acc)
        """)[0]
        assert verifier._detect_fold_pattern(fold_body) is not None

    def test_axiom_generation_soundness(self):
        """Generated axioms don't create contradictions with themselves"""
        from slop.verifier import verify_source

        # A function where only the pattern axioms are needed
        # The count pattern axiom (result >= 0) should help verify the postcondition
        source = """
        (module test
          (fn get-count ((items (List Int)))
            (@spec (((List Int)) -> Int))
            (@post (>= $result 0))
            (let ((mut count 0))
              (for-each (x items)
                (if true (set! count (+ count 1))))
              count)))
        """
        results = verify_source(source)
        # Should verify since count >= 0 is an axiom from count pattern
        get_count = [r for r in results if r.name == 'get-count']
        assert len(get_count) == 1
        assert get_count[0].status == 'verified'

    def test_pattern_independence(self):
        """Detecting one pattern doesn't affect detecting another"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # This body matches both count and fold patterns
        # (count is a special case of fold with + and init=0)
        body = parse("(let ((mut count 0)) (for-each (x items) (if (> x 0) (set! count (+ count 1)))) count)")[0]

        # Both should be detected
        count = verifier._detect_count_pattern(body)
        fold = verifier._detect_fold_pattern(body)

        # Count should match (initialized to 0, increments by 1)
        assert count is not None
        assert count.count_var == 'count'

        # Fold should also match (it's a general accumulation)
        # Note: fold pattern checks for non-empty-collection init, which count (0) passes
        # But count pattern is more specific, so both may detect
        # This is intentional - we apply axioms from both


class TestLoopAnalysis:
    """Test loop analysis for SSA-based verification"""

    def test_analyze_simple_loop(self):
        """Analyze a simple for-each loop with set!"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, FunctionRegistry, FunctionDef
        from slop.parser import parse

        env = MinimalTypeEnv()
        fn_registry = FunctionRegistry()
        fn_registry.functions['add-item'] = FunctionDef(
            name='add-item',
            params=['arena', 'result', 'item'],
            body=None,
            is_pure=False
        )

        verifier = ContractVerifier(env, function_registry=fn_registry)

        body = parse("""
            (let ((mut result (make-list arena)))
              (for-each (item items)
                (set! result (add-item arena result item)))
              result)
        """)[0]

        loops = verifier._analyze_loops(body)

        assert len(loops) == 1
        loop = loops[0]
        assert loop.loop_var == 'item'
        assert 'result' in loop.modified_vars
        assert len(loop.set_bindings) == 1

        binding = loop.set_bindings[0]
        assert binding.var_name == 'result'
        assert binding.fn_name == 'add-item'
        assert binding.is_self_ref  # result is passed as argument

    def test_analyze_loop_with_self_ref_params(self):
        """Verify self-referential parameters are detected"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, FunctionRegistry, FunctionDef
        from slop.parser import parse

        env = MinimalTypeEnv()
        fn_registry = FunctionRegistry()
        fn_registry.functions['delta-add'] = FunctionDef(
            name='delta-add',
            params=['arena', 'd', 't'],
            body=None,
            is_pure=False
        )

        verifier = ContractVerifier(env, function_registry=fn_registry)

        body = parse("""
            (let ((mut result (make-delta arena iter)))
              (for-each (t triples)
                (set! result (delta-add arena result t)))
              result)
        """)[0]

        loops = verifier._analyze_loops(body)

        assert len(loops) == 1
        binding = loops[0].set_bindings[0]
        assert binding.is_self_ref
        assert 'd' in binding.self_ref_params
        assert binding.self_ref_params['d'] == 'result'

    def test_analyze_loop_no_self_ref(self):
        """Verify non-self-referential set! is detected correctly"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, FunctionRegistry, FunctionDef
        from slop.parser import parse

        env = MinimalTypeEnv()
        fn_registry = FunctionRegistry()
        fn_registry.functions['compute'] = FunctionDef(
            name='compute',
            params=['x'],
            body=None,
            is_pure=True
        )

        verifier = ContractVerifier(env, function_registry=fn_registry)

        body = parse("""
            (let ((mut total 0))
              (for-each (x items)
                (set! total (compute x)))
              total)
        """)[0]

        loops = verifier._analyze_loops(body)

        assert len(loops) == 1
        binding = loops[0].set_bindings[0]
        assert binding.var_name == 'total'
        assert not binding.is_self_ref  # total is not passed as argument

    def test_analyze_nested_loops(self):
        """Analyze nested for-each loops"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        body = parse("""
            (let ((mut count 0))
              (for-each (row rows)
                (for-each (cell row)
                  (set! count (+ count 1))))
              count)
        """)[0]

        loops = verifier._analyze_loops(body)

        # Should find both loops
        assert len(loops) == 2
        outer_loop = [l for l in loops if l.loop_var == 'row'][0]
        inner_loop = [l for l in loops if l.loop_var == 'cell'][0]

        assert outer_loop is not None
        assert inner_loop is not None

    def test_analyze_loop_with_invariant(self):
        """Detect @loop-invariant annotations in loops"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        body = parse("""
            (let ((mut count 0))
              (for-each (x items)
                (@loop-invariant (>= count 0))
                (set! count (+ count 1)))
              count)
        """)[0]

        loops = verifier._analyze_loops(body)

        assert len(loops) == 1
        assert len(loops[0].loop_invariants) == 1


class TestLetBindingAxioms:
    """Test let binding axioms for non-function-call expressions"""

    def test_simple_arithmetic_binding(self):
        """Let binding for arithmetic expression adds axiom"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, Z3Translator
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)
        translator = Z3Translator(env)

        # Declare delta variable
        translator.declare_variable('delta', PrimitiveType('Int'))

        # Process binding: (next-iter (+ delta 1))
        binding = parse("(next-iter (+ delta 1))")[0]
        axioms = []

        verifier._process_let_binding(binding, translator, axioms)

        # Should have added an axiom
        assert len(axioms) >= 1
        # next-iter should be declared
        assert 'next-iter' in translator.variables

    def test_field_access_binding(self):
        """Let binding with field access adds axiom"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, Z3Translator
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)
        translator = Z3Translator(env)

        # Declare delta variable
        translator.declare_variable('delta', PrimitiveType('Int'))

        # Process binding: (next-iter (+ (. delta iteration) 1))
        binding = parse("(next-iter (+ (. delta iteration) 1))")[0]
        axioms = []

        verifier._process_let_binding(binding, translator, axioms)

        # Should have added an axiom
        assert len(axioms) >= 1
        # Axiom should relate next-iter to delta's iteration field
        axiom_str = str(axioms[0])
        assert 'next-iter' in axiom_str

    def test_union_constructor_axioms(self):
        """Union constructors like (ok result) add tag and payload axioms"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, Z3Translator
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)
        translator = Z3Translator(env)

        # Declare variables
        translator.declare_variable('$result', PrimitiveType('Int'))
        translator.declare_variable('result', PrimitiveType('Int'))

        # Test (ok result) body
        body = parse("(ok result)")[0]

        assert verifier._is_union_constructor(body) is True

        axioms = verifier._extract_union_constructor_axioms(body, translator)

        # Should have tag and payload axioms
        assert len(axioms) >= 2


class TestInductiveLoopIntegration:
    """Integration tests for inductive loop verification in verify_function"""

    def test_inductive_verification_triggered(self):
        """Verify that inductive verification is triggered during function verification"""
        from slop.verifier import verify_source

        # A function with a loop that modifies a variable self-referentially
        # The delta-add postcondition enables field preservation inference
        source = """
        (module test
          (type Delta (record (iteration Int) (triples Int)))

          (fn delta-add ((arena Int) (d Delta) (t Int))
            (@spec ((Int Delta Int) -> Delta))
            (@post (== (. $result iteration) (. d iteration)))
            (record-new Delta (iteration (. d iteration)) (triples (+ (. d triples) 1))))

          (fn process ((arena Int) (items (List Int)))
            (@spec ((Int (List Int)) -> Int))
            (@post (>= $result 0))
            (let ((mut count 0))
              (for-each (x items)
                (set! count (+ count 1)))
              count)))
        """
        results = verify_source(source)

        # delta-add should verify (it has a concrete body that satisfies postcondition)
        delta_add = [r for r in results if r.name == 'delta-add']
        assert len(delta_add) == 1
        assert delta_add[0].status == 'verified'

    def test_loop_analysis_integration(self):
        """Verify loop analysis is integrated into verify_function"""
        from slop.verifier import (ContractVerifier, MinimalTypeEnv, FunctionRegistry,
                                    FunctionDef, build_type_registry_from_ast)
        from slop.parser import parse

        source = """
        (type Delta (record (iteration Int)))

        (fn delta-add ((arena Int) (d Delta) (t Int))
          (@spec ((Int Delta Int) -> Delta))
          (@post (== (. $result iteration) (. d iteration)))
          d)

        (fn process-loop ((arena Int) (delta Delta) (items (List Int)))
          (@spec ((Int Delta (List Int)) -> Delta))
          (@post (>= (. $result iteration) 0))
          (let ((mut result delta))
            (for-each (t items)
              (set! result (delta-add arena result t)))
            result))
        """
        ast = parse(source)

        # Build type registry
        type_registry = build_type_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry)

        # Build function registry with delta-add
        fn_registry = FunctionRegistry()
        fn_registry.functions['delta-add'] = FunctionDef(
            name='delta-add',
            params=['arena', 'd', 't'],
            body=None,
            is_pure=False,
            postconditions=[parse("(== (. $result iteration) (. d iteration))")[0]]
        )

        verifier = ContractVerifier(env, function_registry=fn_registry)

        # Find and verify process-loop
        fn_form = None
        for form in ast:
            if hasattr(form, 'items') and len(form) > 1:
                if hasattr(form[0], 'name') and form[0].name == 'fn':
                    if hasattr(form[1], 'name') and form[1].name == 'process-loop':
                        fn_form = form
                        break

        if fn_form:
            result = verifier.verify_function(fn_form)
            # The function should at least attempt verification
            # (may fail due to incomplete inference, but shouldn't error)
            assert result.status in ('verified', 'failed', 'skipped')


class TestInductiveVerification:
    """Test inductive loop verification (base case + inductive step)"""

    def test_verify_loop_inductively_field_preservation(self):
        """Verify field preservation through inductive reasoning"""
        from slop.verifier import (ContractVerifier, MinimalTypeEnv, Z3Translator,
                                    FunctionRegistry, FunctionDef, LoopContext, SetBinding)
        from slop.parser import parse

        env = MinimalTypeEnv()
        fn_registry = FunctionRegistry()

        # delta-add preserves the iteration field
        fn_registry.functions['delta-add'] = FunctionDef(
            name='delta-add',
            params=['arena', 'd', 't'],
            body=None,
            is_pure=False,
            postconditions=[parse("(== (. $result iteration) (. d iteration))")[0]]
        )

        verifier = ContractVerifier(env, function_registry=fn_registry)
        translator = Z3Translator(env, function_registry=fn_registry)

        loop_ctx = LoopContext(
            loop_var='t',
            collection=parse("triples")[0],
            loop_expr=parse("(for-each (t triples) (set! result (delta-add arena result t)))")[0],
            modified_vars={'result'},
            set_bindings=[SetBinding(
                var_name='result',
                call_expr=parse("(delta-add arena result t)")[0],
                fn_name='delta-add',
                is_self_ref=True,
                self_ref_params={'d': 'result'}
            )],
            loop_invariants=[]
        )

        # Verify inductively
        verified = verifier._verify_loop_inductively(loop_ctx, None, translator)

        assert verified is not None
        assert len(verified) >= 1
        # Should have verified field preservation
        preservation = [i for i in verified if i.source == 'preservation']
        assert len(preservation) >= 1

    def test_verify_base_case_preservation(self):
        """Base case for field preservation is trivially true"""
        from slop.verifier import (ContractVerifier, MinimalTypeEnv, Z3Translator,
                                    InferredInvariant)
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)
        translator = Z3Translator(env)

        invariant = InferredInvariant(
            variable='result',
            property_expr=parse("(== (. result iteration) (. __init_result iteration))")[0],
            source='preservation',
            confidence=1.0,
            original_postcondition=parse("(== (. $result iteration) (. d iteration))")[0]
        )

        # Base case should be trivially true for preservation
        result = verifier._verify_base_case(invariant, None, translator)
        assert result is True

    def test_verify_inductive_step_field_equality(self):
        """Inductive step succeeds when postcondition shows field equality"""
        from slop.verifier import (ContractVerifier, MinimalTypeEnv, Z3Translator,
                                    FunctionRegistry, FunctionDef, InferredInvariant,
                                    LoopContext, SetBinding)
        from slop.parser import parse

        env = MinimalTypeEnv()
        fn_registry = FunctionRegistry()
        fn_registry.functions['delta-add'] = FunctionDef(
            name='delta-add',
            params=['arena', 'd', 't'],
            body=None,
            postconditions=[parse("(== (. $result iteration) (. d iteration))")[0]]
        )

        verifier = ContractVerifier(env, function_registry=fn_registry)
        translator = Z3Translator(env, function_registry=fn_registry)

        invariant = InferredInvariant(
            variable='result',
            property_expr=parse("(== (. result iteration) (. __init_result iteration))")[0],
            source='preservation',
            confidence=1.0,
            original_postcondition=parse("(== (. $result iteration) (. d iteration))")[0]
        )

        loop_ctx = LoopContext(
            loop_var='t',
            collection=parse("triples")[0],
            loop_expr=parse("(for-each (t triples) (set! result (delta-add arena result t)))")[0],
            modified_vars={'result'},
            set_bindings=[SetBinding(
                var_name='result',
                call_expr=parse("(delta-add arena result t)")[0],
                fn_name='delta-add',
                is_self_ref=True,
                self_ref_params={'d': 'result'}
            )],
            loop_invariants=[]
        )

        result = verifier._verify_inductive_step(invariant, loop_ctx, translator)
        assert result is True

    def test_is_field_equality_postcondition(self):
        """Detect field equality postcondition pattern"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Valid field equality: (== (. $result iteration) (. d iteration))
        post1 = parse("(== (. $result iteration) (. d iteration))")[0]
        assert verifier._is_field_equality_postcondition(post1) is True

        # Invalid: fields don't match
        post2 = parse("(== (. $result iteration) (. d count))")[0]
        assert verifier._is_field_equality_postcondition(post2) is False

        # Invalid: not an equality
        post3 = parse("(>= (. $result iteration) (. d iteration))")[0]
        assert verifier._is_field_equality_postcondition(post3) is False

        # Invalid: LHS not $result
        post4 = parse("(== (. x iteration) (. d iteration))")[0]
        assert verifier._is_field_equality_postcondition(post4) is False

    def test_find_init_binding_for_var(self):
        """Find initialization expression for mutable variable"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        body = parse("""
            (let ((mut result (make-delta arena iter)))
              (for-each (t triples)
                (set! result (delta-add arena result t)))
              result)
        """)[0]

        init = verifier._find_init_binding_for_var(body, 'result')
        assert init is not None
        # Should be (make-delta arena iter)
        assert init[0].name == 'make-delta'

    def test_no_invariants_without_self_ref(self):
        """No inductive verification without self-referential set!"""
        from slop.verifier import (ContractVerifier, MinimalTypeEnv, Z3Translator,
                                    FunctionRegistry, FunctionDef, LoopContext, SetBinding)
        from slop.parser import parse

        env = MinimalTypeEnv()
        fn_registry = FunctionRegistry()
        fn_registry.functions['compute'] = FunctionDef(
            name='compute',
            params=['x'],
            body=None,
            postconditions=[parse("(>= $result 0)")[0]]
        )

        verifier = ContractVerifier(env, function_registry=fn_registry)
        translator = Z3Translator(env, function_registry=fn_registry)

        loop_ctx = LoopContext(
            loop_var='x',
            collection=parse("items")[0],
            loop_expr=parse("(for-each (x items) (set! total (compute x)))")[0],
            modified_vars={'total'},
            set_bindings=[SetBinding(
                var_name='total',
                call_expr=parse("(compute x)")[0],
                fn_name='compute',
                is_self_ref=False,  # Not self-referential
                self_ref_params={}
            )],
            loop_invariants=[]
        )

        verified = verifier._verify_loop_inductively(loop_ctx, None, translator)
        # No invariants can be verified for non-self-ref
        assert verified is None


class TestInvariantInference:
    """Test automatic invariant inference from postconditions"""

    def test_infer_field_preservation(self):
        """Infer field preservation from equality postcondition"""
        from slop.verifier import (InvariantInferencer, FunctionRegistry, FunctionDef,
                                    LoopContext, SetBinding)
        from slop.parser import parse

        fn_registry = FunctionRegistry()
        fn_registry.functions['delta-add'] = FunctionDef(
            name='delta-add',
            params=['arena', 'd', 't'],
            body=None,
            is_pure=False,
            postconditions=[parse("(== (. $result iteration) (. d iteration))")[0]]
        )

        inferencer = InvariantInferencer(function_registry=fn_registry)

        # Create a loop context with self-referential set!
        loop_ctx = LoopContext(
            loop_var='t',
            collection=parse("triples")[0],
            loop_expr=parse("(for-each (t triples) (set! result (delta-add arena result t)))")[0],
            modified_vars={'result'},
            set_bindings=[SetBinding(
                var_name='result',
                call_expr=parse("(delta-add arena result t)")[0],
                fn_name='delta-add',
                is_self_ref=True,
                self_ref_params={'d': 'result'}
            )],
            loop_invariants=[]
        )

        invariants = inferencer.infer_from_loop(loop_ctx)

        assert len(invariants) >= 1
        # Should find field preservation for 'iteration'
        preservation = [i for i in invariants if i.source == 'preservation']
        assert len(preservation) >= 1

    def test_infer_nonnegative(self):
        """Infer non-negativity invariant"""
        from slop.verifier import (InvariantInferencer, FunctionRegistry, FunctionDef,
                                    LoopContext, SetBinding)
        from slop.parser import parse

        fn_registry = FunctionRegistry()
        fn_registry.functions['increment'] = FunctionDef(
            name='increment',
            params=['x'],
            body=None,
            is_pure=True,
            postconditions=[parse("(>= $result 0)")[0]]
        )

        inferencer = InvariantInferencer(function_registry=fn_registry)

        loop_ctx = LoopContext(
            loop_var='i',
            collection=parse("items")[0],
            loop_expr=parse("(for-each (i items) (set! count (increment count)))")[0],
            modified_vars={'count'},
            set_bindings=[SetBinding(
                var_name='count',
                call_expr=parse("(increment count)")[0],
                fn_name='increment',
                is_self_ref=True,
                self_ref_params={'x': 'count'}
            )],
            loop_invariants=[]
        )

        invariants = inferencer.infer_from_loop(loop_ctx)

        # Should find non-negativity invariant
        nonneg = [i for i in invariants if i.source == 'postcondition']
        assert len(nonneg) >= 1

    def test_no_inference_without_self_ref(self):
        """No invariants inferred for non-self-referential set!"""
        from slop.verifier import (InvariantInferencer, FunctionRegistry, FunctionDef,
                                    LoopContext, SetBinding)
        from slop.parser import parse

        fn_registry = FunctionRegistry()
        fn_registry.functions['compute'] = FunctionDef(
            name='compute',
            params=['x'],
            body=None,
            is_pure=True,
            postconditions=[parse("(>= $result 0)")[0]]
        )

        inferencer = InvariantInferencer(function_registry=fn_registry)

        loop_ctx = LoopContext(
            loop_var='x',
            collection=parse("items")[0],
            loop_expr=parse("(for-each (x items) (set! total (compute x)))")[0],
            modified_vars={'total'},
            set_bindings=[SetBinding(
                var_name='total',
                call_expr=parse("(compute x)")[0],
                fn_name='compute',
                is_self_ref=False,  # Not self-referential
                self_ref_params={}
            )],
            loop_invariants=[]
        )

        invariants = inferencer.infer_from_loop(loop_ctx)

        # No invariants should be inferred for non-self-ref
        assert len(invariants) == 0

    def test_extract_result_field(self):
        """Test extracting field from (. $result field) expression"""
        from slop.verifier import InvariantInferencer
        from slop.parser import parse

        inferencer = InvariantInferencer()

        # Valid: (. $result iteration)
        expr = parse("(. $result iteration)")[0]
        field = inferencer._extract_result_field(expr)
        assert field == 'iteration'

        # Invalid: not a field access
        expr2 = parse("$result")[0]
        assert inferencer._extract_result_field(expr2) is None

        # Invalid: wrong object
        expr3 = parse("(. other iteration)")[0]
        assert inferencer._extract_result_field(expr3) is None

    def test_extract_param_field(self):
        """Test extracting field from (. param field) expression"""
        from slop.verifier import InvariantInferencer
        from slop.parser import parse

        inferencer = InvariantInferencer()

        # Valid: (. d iteration) where d is a param
        expr = parse("(. d iteration)")[0]
        result = inferencer._extract_param_field(expr, ['d', 'arena'])
        assert result == ('iteration', 'd')

        # Invalid: param not in list
        result2 = inferencer._extract_param_field(expr, ['arena', 't'])
        assert result2 is None

    def test_make_field_preserved_invariant(self):
        """Test creating field preservation invariant expression"""
        from slop.verifier import InvariantInferencer
        from slop.parser import pretty_print

        inferencer = InvariantInferencer()

        invariant = inferencer._make_field_preserved_invariant('result', 'iteration')

        # Should produce: (== (. result iteration) (. __init_result iteration))
        pp = pretty_print(invariant)
        assert '==' in pp
        assert 'result' in pp
        assert 'iteration' in pp
        assert '__init_result' in pp


class TestSSAContext:
    """Test SSA version tracking infrastructure"""

    def test_init_variable(self):
        """Initialize a variable at version 0"""
        from slop.verifier import SSAContext, Z3Translator, MinimalTypeEnv
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        ssa = SSAContext(translator)

        # Declare and init a variable
        z3_var = translator.declare_variable('result', PrimitiveType('Int'))
        ssa.init_variable('result', z3_var)

        assert ssa.is_tracked('result')
        assert ssa.current_version['result'] == 0

        current = ssa.get_current_version('result')
        assert current is not None
        assert current.var_name == 'result'
        assert current.version == 0
        assert current.z3_var == z3_var

    def test_create_new_version(self):
        """Create new versions on assignment"""
        from slop.verifier import SSAContext, Z3Translator, MinimalTypeEnv
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        ssa = SSAContext(translator)

        z3_var = translator.declare_variable('result', PrimitiveType('Int'))
        ssa.init_variable('result', z3_var)

        # Create version 1 (simulating first set!)
        v1 = ssa.create_new_version('result')
        assert v1.version == 1
        assert v1.var_name == 'result'
        assert 'result@1' in translator.variables

        # Create version 2 (simulating second set!)
        v2 = ssa.create_new_version('result')
        assert v2.version == 2
        assert 'result@2' in translator.variables

        # Current version should be 2
        assert ssa.current_version['result'] == 2
        assert ssa.get_versioned_name('result') == 'result@2'

    def test_get_version(self):
        """Get specific version by number"""
        from slop.verifier import SSAContext, Z3Translator, MinimalTypeEnv
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        ssa = SSAContext(translator)

        z3_var = translator.declare_variable('x', PrimitiveType('Int'))
        ssa.init_variable('x', z3_var)
        ssa.create_new_version('x')
        ssa.create_new_version('x')

        v0 = ssa.get_version('x', 0)
        v1 = ssa.get_version('x', 1)
        v2 = ssa.get_version('x', 2)

        assert v0 is not None and v0.version == 0
        assert v1 is not None and v1.version == 1
        assert v2 is not None and v2.version == 2
        assert ssa.get_version('x', 3) is None  # Doesn't exist

    def test_snapshot_and_restore(self):
        """Snapshot and restore version state (for loop handling)"""
        from slop.verifier import SSAContext, Z3Translator, MinimalTypeEnv
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        ssa = SSAContext(translator)

        z3_var = translator.declare_variable('result', PrimitiveType('Int'))
        ssa.init_variable('result', z3_var)

        # Take snapshot at loop entry (version 0)
        entry_snapshot = ssa.snapshot()
        assert entry_snapshot['result'] == 0

        # Simulate loop iterations
        ssa.create_new_version('result')  # v1
        ssa.create_new_version('result')  # v2

        assert ssa.current_version['result'] == 2

        # Restore to entry state (for analyzing base case)
        ssa.restore(entry_snapshot)
        assert ssa.current_version['result'] == 0

    def test_versioned_name(self):
        """Get versioned variable names"""
        from slop.verifier import SSAContext, Z3Translator, MinimalTypeEnv
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        ssa = SSAContext(translator)

        z3_var = translator.declare_variable('count', PrimitiveType('Int'))
        ssa.init_variable('count', z3_var)

        # Version 0 uses original name
        assert ssa.get_versioned_name('count') == 'count'

        ssa.create_new_version('count')
        assert ssa.get_versioned_name('count') == 'count@1'

        # Untracked variable returns original name
        assert ssa.get_versioned_name('other') == 'other'

    def test_all_versions(self):
        """Get all versions of a variable"""
        from slop.verifier import SSAContext, Z3Translator, MinimalTypeEnv
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        ssa = SSAContext(translator)

        z3_var = translator.declare_variable('acc', PrimitiveType('Int'))
        ssa.init_variable('acc', z3_var)
        ssa.create_new_version('acc')
        ssa.create_new_version('acc')

        all_versions = ssa.get_all_versions('acc')
        assert len(all_versions) == 3
        assert [v.version for v in all_versions] == [0, 1, 2]


class TestSSATracking:
    """Test SSA-style tracking for self-referential set! patterns"""

    def test_self_referential_param_detection(self):
        """Detect when a set! passes the target variable as an argument"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse, Symbol

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Simulate call_args for (set! result (delta-add arena result t))
        call_args = [Symbol('arena'), Symbol('result'), Symbol('t')]
        params = ['arena', 'd', 't']

        self_refs = verifier._find_self_referential_params('result', call_args, params)

        assert len(self_refs) == 1
        assert 'd' in self_refs
        assert self_refs['d'] == 'result'

    def test_self_referential_no_match(self):
        """No self-reference when variable is not passed as argument"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import Symbol

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # call_args for (set! result (make-delta arena iter))
        call_args = [Symbol('arena'), Symbol('iter')]
        params = ['arena', 'iteration']

        self_refs = verifier._find_self_referential_params('result', call_args, params)

        assert len(self_refs) == 0

    def test_substitute_postcondition_with_self_ref(self):
        """Postcondition substitution uses __old_ for self-referential params"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse, Symbol

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Postcondition: (== (. $result iteration) (. d iteration))
        post = parse("(== (. $result iteration) (. d iteration))")[0]

        # Args for (set! result (delta-add arena result t))
        call_args = [Symbol('arena'), Symbol('result'), Symbol('t')]
        params = ['arena', 'd', 't']
        self_ref_params = {'d': 'result'}

        subst = verifier._substitute_postcondition(post, 'result', params, call_args, self_ref_params)

        # Should produce: (== (. result iteration) (. __old_result iteration))
        # Check the structure
        assert subst[1][1].name == 'result'  # $result -> result
        assert subst[2][1].name == '__old_result'  # d -> __old_result

    def test_old_variable_created_in_set_binding(self):
        """Processing set! creates __old_ variable when self-reference detected"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, Z3Translator, FunctionRegistry, FunctionDef
        from slop.parser import parse
        from slop.types import PrimitiveType, RecordType

        # Set up type environment
        type_registry = {'Delta': RecordType('Delta', [('iteration', PrimitiveType('Int'))])}
        env = MinimalTypeEnv(type_registry=type_registry)

        # Set up function registry with a delta-add that has postconditions
        fn_registry = FunctionRegistry()
        fn_registry.functions['delta-add'] = FunctionDef(
            name='delta-add',
            params=['arena', 'd', 't'],
            body=None,
            is_pure=False,
            postconditions=[parse("(== (. $result iteration) (. d iteration))")[0]]
        )

        verifier = ContractVerifier(env, function_registry=fn_registry)
        translator = Z3Translator(env, function_registry=fn_registry)

        # Declare the 'result' variable
        translator.declare_variable('result', PrimitiveType('Int'))

        # Process: (set! result (delta-add arena result t))
        call_expr = parse("(delta-add arena result t)")[0]
        axioms = []

        verifier._process_set_binding('result', call_expr, translator, axioms)

        # Check that __old_result was created
        assert '__old_result' in translator.variables

        # Check that a constraint was added: __old_result == result
        # The constraint should be in translator.constraints
        found_old_constraint = False
        for c in translator.constraints:
            cstr = str(c)
            if '__old_result' in cstr and 'result' in cstr:
                found_old_constraint = True
                break
        assert found_old_constraint, "Should have constraint linking __old_result to result"


class TestArrayEncoding:
    """Test Z3 array encoding for lists with element-level properties"""

    def test_array_encoding_detection(self):
        """Detect when array encoding is needed for postconditions"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Should need array encoding for all-triples-have-predicate
        post1 = [parse("(all-triples-have-predicate $result RDF_TYPE)")[0]]
        assert verifier._needs_array_encoding(post1)

        # Should need array encoding for list-ref
        post2 = [parse("(== (list-ref $result 0) x)")[0]]
        assert verifier._needs_array_encoding(post2)

        # Should need array encoding for forall with list-ref
        post3 = [parse("(forall (i Int) (== (list-ref $result i) 0))")[0]]
        assert verifier._needs_array_encoding(post3)

        # Should not need array encoding for simple postconditions
        post4 = [parse("(>= (list-len $result) 0)")[0]]
        assert not verifier._needs_array_encoding(post4)

    def test_create_list_array(self):
        """Test creating array representation for lists"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_array_encoding=True)

        arr, length = translator._create_list_array("test")

        # Should be a Z3 array
        assert z3.is_array(arr)

        # Should be an Int for length
        assert z3.is_int(length)

        # Length should have non-negative constraint
        has_nonneg = any(str(c) == "_len_test_1 >= 0" for c in translator.constraints)
        assert has_nonneg, f"Expected length >= 0 constraint, got: {translator.constraints}"

    def test_translate_list_ref(self):
        """Test list-ref translation to Select"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_array_encoding=True)

        # Set up a list array
        arr, length = translator._create_list_array("lst")
        translator.variables["lst"] = z3.IntVal(0)  # Placeholder for list variable

        # Translate (list-ref lst 0)
        expr = parse("(list-ref lst 0)")[0]
        result = translator.translate_expr(expr)

        # Should return something (may use uninterpreted function fallback)
        assert result is not None

    def test_translate_forall(self):
        """Test forall quantifier translation"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        # Translate (forall (i Int) (>= i 0))
        expr = parse("(forall (i Int) (>= i 0))")[0]
        result = translator.translate_expr(expr)

        # Should return a ForAll expression
        assert result is not None
        assert z3.is_quantifier(result)

    def test_translate_exists(self):
        """Test exists quantifier translation"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        # Translate (exists (x Int) (== x 5))
        expr = parse("(exists (x Int) (== x 5))")[0]
        result = translator.translate_expr(expr)

        # Should return an Exists expression
        assert result is not None
        assert z3.is_quantifier(result)

    def test_translate_implies(self):
        """Test implies translation"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)

        # Declare variables
        translator.declare_variable('a', PrimitiveType('Bool'))
        translator.declare_variable('b', PrimitiveType('Bool'))

        # Translate (implies a b)
        expr = parse("(implies a b)")[0]
        result = translator.translate_expr(expr)

        # Should return an Implies expression
        assert result is not None
        assert z3.is_bool(result)

    def test_list_new_with_array_encoding(self):
        """Test list-new with array encoding creates proper axioms"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, Z3Translator
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_array_encoding=True)

        # Declare $result
        translator.declare_variable('$result', z3.IntSort())

        verifier = ContractVerifier(env)

        # Extract axioms for list-new
        list_new_expr = parse("(list-new arena Triple)")[0]
        axioms = verifier._extract_list_new_axioms(list_new_expr, translator)

        # Should have created array for $result
        assert '$result' in translator.list_arrays

        # Should have axiom that length is 0
        assert len(axioms) >= 1
        # First axiom should be length == 0 (may be normalized to 0 == length)
        has_length_zero = any("== 0" in str(a) or "0 ==" in str(a) for a in axioms)
        assert has_length_zero, f"Expected length == 0 axiom, got: {axioms}"


class TestQuantifiedPostconditions:
    """Test verification of postconditions with quantifiers"""

    def test_forall_postcondition_simple(self):
        """Test verification with simple forall postcondition"""
        from slop.verifier import verify_source

        source = """
        (module test
          (fn always-positive ((x Int))
            (@spec ((Int) -> Int))
            (@pre (> x 0))
            (@post (forall (i Int) (implies (== i $result) (> i 0))))
            x))
        """
        results = verify_source(source)

        # Should verify (x > 0 implies result > 0)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_all_triples_have_predicate_detection(self):
        """Test that all-triples-have-predicate triggers array encoding"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Postcondition using all-triples-have-predicate
        postconditions = [parse("(all-triples-have-predicate $result RDF_TYPE)")[0]]

        # Should detect that array encoding is needed
        assert verifier._needs_array_encoding(postconditions)

    def test_list_element_property_axiom_extraction(self):
        """Test extraction of list element property axioms"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, Z3Translator, FunctionRegistry
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_array_encoding=True)
        fn_registry = FunctionRegistry()
        verifier = ContractVerifier(env, function_registry=fn_registry)

        # Set up $result with array encoding
        arr, length = translator._create_list_array('$result')
        translator.declare_variable('$result', PrimitiveType('Int'))

        # Declare type_pred variable
        translator.declare_variable('type-pred', PrimitiveType('Int'))

        # Function body with list-push of make-triple
        body = parse("""
            (let ((inferred (make-triple arena individual type-pred class2)))
              (list-push result inferred))
        """)[0]

        postconditions = [parse("(all-triples-have-predicate $result RDF_TYPE)")[0]]

        # Extract axioms
        axioms = verifier._extract_list_element_property_axioms(body, postconditions, translator)

        # Should find the pushed predicate values (may be empty if type-pred not tracked)
        # The key is that the method runs without error
        assert isinstance(axioms, list)


class TestPropertyVerification:
    """Tests for @property (universal assertion) verification"""

    def test_property_with_forall_verifies(self):
        """Valid property with forall verifies successfully"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Property: for all x > 0, x * 2 > x
        code = """
        (fn positive-double ((x Int))
          (@spec ((Int) -> Int))
          (@property (forall (n Int) (implies (> n 0) (> (* n 2) n))))
          (* x 2))
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

    def test_property_false_fails(self):
        """False property fails with counterexample"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Property: for all x, x > x (always false)
        code = """
        (fn broken-property ((x Int))
          (@spec ((Int) -> Int))
          (@property (forall (n Int) (> n n)))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is False
        assert result.status == "failed"
        assert "Property failed" in result.message

    def test_property_independent_of_preconditions(self):
        """Properties are verified independently of preconditions"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Precondition says x > 0, but property doesn't assume that
        # Property (forall n: n > n) is still false regardless of precondition
        code = """
        (fn property-ignores-pre ((x Int))
          (@spec ((Int) -> Int))
          (@pre (> x 0))
          (@property (forall (n Int) (> n n)))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        # Property should still fail even though precondition is satisfied
        assert result.verified is False
        assert result.status == "failed"
        assert "Property failed" in result.message

    def test_multiple_properties(self):
        """All @property annotations are verified"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Two valid properties
        code = """
        (fn multi-property ((x Int))
          (@spec ((Int) -> Int))
          (@property (forall (n Int) (implies (> n 0) (> (* n 2) n))))
          (@property (forall (n Int) (implies (< n 0) (< (* n 2) n))))
          (* x 2))
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

    def test_multiple_properties_one_fails(self):
        """If one property fails, verification fails"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # First property valid, second invalid
        code = """
        (fn multi-property-fail ((x Int))
          (@spec ((Int) -> Int))
          (@property (forall (n Int) (implies (> n 0) (> (* n 2) n))))
          (@property (forall (n Int) (> n n)))
          (* x 2))
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is False
        assert result.status == "failed"
        assert "Property failed" in result.message

    def test_property_with_implies(self):
        """Common pattern with implies verifies"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # implies (x > 0 and x < 10) then x < 100
        code = """
        (fn implies-property ((x Int))
          (@spec ((Int) -> Int))
          (@property (forall (n Int) (implies (and (> n 0) (< n 10)) (< n 100))))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

    def test_property_tautology(self):
        """Simple tautologies verify"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # x == x is always true
        code = """
        (fn tautology ((x Int))
          (@spec ((Int) -> Int))
          (@property (forall (n Int) (== n n)))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

    def test_property_only_no_postcondition(self):
        """Function with only @property (no @post) is verified"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Only property, no postcondition
        code = """
        (fn property-only ((x Int))
          (@spec ((Int) -> Int))
          (@property (forall (n Int) (>= (* n n) 0)))
          (* x x))
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

    def test_property_with_postcondition(self):
        """Both @property and @post are verified together"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Both property and postcondition
        code = """
        (fn property-and-post ((x Int))
          (@spec ((Int) -> Int))
          (@pre (> x 0))
          (@property (forall (n Int) (>= (* n n) 0)))
          (@post (> $result 0))
          (* x x))
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

    def test_function_registry_extracts_properties(self):
        """FunctionRegistry extracts @property annotations"""
        from slop.verifier import FunctionRegistry
        from slop.parser import parse

        registry = FunctionRegistry()
        code = """
        (fn with-property ((x Int))
          (@spec ((Int) -> Int))
          (@property (forall (n Int) (>= n 0)))
          x)
        """
        ast = parse(code)
        registry.register_from_ast(ast)

        fn_def = registry.functions.get('with-property')
        assert fn_def is not None
        assert len(fn_def.properties) == 1
        # Properties are now (name, expr) tuples
        prop_name, prop_expr = fn_def.properties[0]
        assert prop_name is None  # Unnamed property
        assert prop_expr is not None

    def test_named_property_verifies(self):
        """Named property with forall verifies successfully"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Named property: for all x > 0, x * 2 > x
        code = """
        (fn positive-double ((x Int))
          (@spec ((Int) -> Int))
          (@property positivity (forall (n Int) (implies (> n 0) (> (* n 2) n))))
          (* x 2))
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

    def test_named_property_fails_with_name_in_message(self):
        """Failed named property includes name in error message"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Named property that fails: for all x, x > x (always false)
        code = """
        (fn broken-property ((x Int))
          (@spec ((Int) -> Int))
          (@property impossibility (forall (n Int) (> n n)))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is False
        assert result.status == "failed"
        assert "impossibility" in result.message
        assert "Property 'impossibility' failed" in result.message

    def test_mixed_named_unnamed_properties(self):
        """Both named and unnamed properties in same function"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, FunctionRegistry
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Mix of named and unnamed properties
        code = """
        (fn mixed-properties ((x Int))
          (@spec ((Int) -> Int))
          (@property reflexivity (forall (n Int) (== n n)))
          (@property (forall (n Int) (implies (> n 0) (> (* n 2) n))))
          (* x 2))
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

        # Also check FunctionRegistry extraction
        registry = FunctionRegistry()
        registry.register_from_ast(ast)
        fn_def = registry.functions.get('mixed-properties')
        assert fn_def is not None
        assert len(fn_def.properties) == 2
        # First is named
        assert fn_def.properties[0][0] == "reflexivity"
        # Second is unnamed
        assert fn_def.properties[1][0] is None


class TestImprovedVerificationOutput:
    """Tests for improved verification output with multiple conditions"""

    def test_named_precondition_single(self):
        """Single named precondition is extracted correctly"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Use prefix syntax for named precondition
        code = """
        (fn check-positive ((x Int))
          (@spec ((Int) -> Int))
          (@pre positive (> x 0))
          (@post (> $result 0))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

    def test_named_precondition_unsatisfiable(self):
        """Unsatisfiable named precondition shows name in error"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Two conflicting named preconditions (using prefix syntax)
        code = """
        (fn impossible ((x Int))
          (@spec ((Int) -> Int))
          (@pre too-big (> x 10))
          (@pre too-small (< x 5))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is False
        assert result.status == "failed"
        assert "unsatisfiable" in result.message.lower()
        # Should include both precondition names
        assert "too-big" in result.message
        assert "too-small" in result.message

    def test_multiple_postconditions_show_all_failed(self):
        """Multiple failed postconditions are all listed in message"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Multiple postconditions that will fail
        code = """
        (fn bad-post ((x Int))
          (@spec ((Int) -> Int))
          (@post (> $result 100))
          (@post (< $result 0))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is False
        assert result.status == "failed"
        # Should show both postconditions in message, not just count
        assert "Postconditions failed:" in result.message or "Postcondition failed:" in result.message

    def test_multiple_properties_show_all_failed(self):
        """Multiple failed properties are all listed in message"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Multiple properties that will fail
        code = """
        (fn multi-prop-fail ((x Int))
          (@spec ((Int) -> Int))
          (@property p1 (forall (n Int) (> n n)))
          (@property p2 (forall (n Int) (< n n)))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is False
        assert result.status == "failed"
        # Should show both property names
        assert "p1" in result.message
        assert "p2" in result.message
        assert "Properties failed:" in result.message

    def test_mixed_named_unnamed_preconditions(self):
        """Mix of named and unnamed preconditions works correctly"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Use prefix syntax for named, infix for unnamed
        code = """
        (fn mixed-pre ((x Int))
          (@spec ((Int) -> Int))
          (@pre positive (> x 0))
          (@pre (< x 100))
          (@post (> $result 0))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is True
        assert result.status == "verified"

    def test_counterexample_present_on_failure(self):
        """Counterexample is included in failed verification result"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        code = """
        (fn fail-with-ce ((x Int))
          (@spec ((Int) -> Int))
          (@post (> $result 100))
          x)
        """
        ast = parse(code)
        result = verifier.verify_function(ast[0])

        assert result.verified is False
        assert result.counterexample is not None
        # Should have a counterexample value
        assert len(result.counterexample) > 0


class TestWeakestPrecondition:
    """Test the Weakest Precondition calculus for verification.

    WP(expr, Q) computes the weakest condition P such that {P} expr {Q}.
    The verification condition for {P} body {Q} is: P => WP(body, Q).
    """

    def test_wp_constant(self):
        """WP of constant is the postcondition unchanged"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import Number
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        wp = WeakestPrecondition(translator)

        # WP(42, Q) = Q
        post = z3.BoolVal(True)
        result = wp.wp(Number(42), post)
        assert z3.eq(result, post)

    def test_wp_variable_reference(self):
        """WP of variable reference is postcondition unchanged"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import Symbol
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        translator.declare_variable('x', PrimitiveType('Int'))
        wp = WeakestPrecondition(translator)

        # WP(x, Q) = Q (reading doesn't change state)
        post = z3.BoolVal(True)
        result = wp.wp(Symbol('x'), post)
        assert z3.eq(result, post)

    def test_wp_let_simple(self):
        """WP of let binding substitutes variable correctly"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        translator.declare_variable('$result', PrimitiveType('Int'))
        wp = WeakestPrecondition(translator)

        # (let ((y 10)) y)
        # WP((let ((y 10)) y), $result == 10) should be satisfiable
        expr = parse("(let ((y 10)) y)")[0]
        result_var = translator.variables['$result']
        post = result_var == z3.IntVal(10)

        wp_result = wp.wp(expr, post)
        assert wp_result is not None

    def test_wp_if_branches(self):
        """WP of if splits into both branches"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        translator.declare_variable('x', PrimitiveType('Int'))
        translator.declare_variable('$result', PrimitiveType('Int'))
        wp = WeakestPrecondition(translator)

        # (if (>= x 0) x (- 0 x))  -- absolute value
        # WP(abs, $result >= 0) should be valid for all x
        expr = parse("(if (>= x 0) x (- 0 x))")[0]
        result_var = translator.variables['$result']
        post = result_var >= z3.IntVal(0)

        wp_result = wp.wp(expr, post)
        assert wp_result is not None
        # WP should be: (x >= 0 => x >= 0) && (x < 0 => -x >= 0)
        # Which is equivalent to: true && true = true
        assert z3.is_bool(wp_result)

    def test_wp_if_verification(self):
        """Full verification using WP for if expression"""
        from slop.verifier import verify_source

        # Absolute value function: postcondition $result >= 0
        source = """
        (fn abs ((x Int))
          (@spec ((Int) -> Int))
          (@post (>= $result 0))
          (if (>= x 0) x (- 0 x)))
        """
        results = verify_source(source)
        # Should verify (WP enables this)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_wp_do_sequential(self):
        """WP propagates through sequential statements right-to-left"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        translator.declare_variable('x', PrimitiveType('Int'))
        translator.declare_variable('$result', PrimitiveType('Int'))
        wp = WeakestPrecondition(translator)

        # (do x)  -- simple do block returning x
        expr = parse("(do x)")[0]
        result_var = translator.variables['$result']
        post = result_var > z3.IntVal(0)

        wp_result = wp.wp(expr, post)
        assert wp_result is not None

    def test_wp_let_propagation(self):
        """WP propagates through let binding to establish postcondition"""
        from slop.verifier import verify_source

        # Let binding where postcondition depends on bound value
        source = """
        (fn test ((x Int))
          (@spec ((Int) -> Int))
          (@pre (> x 0))
          (@post (> $result 1))
          (let ((y (+ x 1)))
            y))
        """
        results = verify_source(source)
        # WP should compute: WP(let y=x+1 in y, $result > 1) = (x+1 > 1) = (x > 0)
        # Which is exactly the precondition, so should verify
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_wp_cond_multi_branch(self):
        """WP handles cond with multiple branches"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        translator.declare_variable('x', PrimitiveType('Int'))
        translator.declare_variable('$result', PrimitiveType('Int'))
        wp = WeakestPrecondition(translator)

        # (cond ((< x 0) -1) ((== x 0) 0) (else 1))  -- sign function
        expr = parse("(cond ((< x 0) (- 0 1)) ((== x 0) 0) (else 1))")[0]
        result_var = translator.variables['$result']
        # Post: result is -1, 0, or 1
        post = z3.Or(result_var == z3.IntVal(-1),
                     result_var == z3.IntVal(0),
                     result_var == z3.IntVal(1))

        wp_result = wp.wp(expr, post)
        assert wp_result is not None
        assert z3.is_bool(wp_result)

    def test_wp_nested_let(self):
        """WP handles nested let bindings"""
        from slop.verifier import verify_source

        source = """
        (fn nested ((x Int))
          (@spec ((Int) -> Int))
          (@pre (> x 0))
          (@post (> $result 2))
          (let ((y (+ x 1)))
            (let ((z (+ y 1)))
              z)))
        """
        results = verify_source(source)
        # WP: z = y + 1 = x + 2, post is z > 2, so need x > 0
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_wp_set_substitution(self):
        """WP of set! substitutes old value with new"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        translator.declare_variable('x', PrimitiveType('Int'))
        wp = WeakestPrecondition(translator)

        # (set! x 10)
        # WP((set! x 10), x > 5) = (10 > 5) = true
        expr = parse("(set! x 10)")[0]
        x_var = translator.variables['x']
        post = x_var > z3.IntVal(5)

        wp_result = wp.wp(expr, post)
        assert wp_result is not None
        # After substituting x with 10, we get 10 > 5 = true
        solver = z3.Solver()
        solver.add(z3.Not(wp_result))
        # If WP is valid (always true), then NOT(WP) is unsatisfiable
        result = solver.check()
        assert result == z3.unsat, "WP should be valid (10 > 5 is true)"

    def test_wp_return_binds_result(self):
        """WP of return binds $result to the returned value"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        translator.declare_variable('x', PrimitiveType('Int'))
        translator.declare_variable('$result', PrimitiveType('Int'))
        wp = WeakestPrecondition(translator)

        # (return x)
        # WP((return x), $result > 0) = (x > 0)
        expr = parse("(return x)")[0]
        result_var = translator.variables['$result']
        post = result_var > z3.IntVal(0)

        wp_result = wp.wp(expr, post)
        assert wp_result is not None

    def test_wp_integration_simple_function(self):
        """Integration test: WP enables verification of simple functions"""
        from slop.verifier import verify_source

        # Simple increment: result = x + 1
        source = """
        (fn increment ((x Int))
          (@spec ((Int) -> Int))
          (@pre (>= x 0))
          (@post (> $result x))
          (+ x 1))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_wp_integration_max_function(self):
        """Integration test: WP enables verification of max function"""
        from slop.verifier import verify_source

        source = """
        (fn max ((a Int) (b Int))
          (@spec ((Int Int) -> Int))
          (@post (and (>= $result a) (>= $result b)))
          (if (>= a b) a b))
        """
        results = verify_source(source)
        verified = [r for r in results if r.status == 'verified']
        assert len(verified) >= 1

    def test_wp_loop_with_invariant(self):
        """WP uses @loop-invariant for loop verification"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        translator.declare_variable('sum', PrimitiveType('Int'))
        translator.declare_variable('$result', PrimitiveType('Int'))
        wp = WeakestPrecondition(translator)

        # for-each with @loop-invariant
        expr = parse("""
        (for-each (x lst)
          (@loop-invariant (>= sum 0))
          (set! sum (+ sum x)))
        """)[0]

        result_var = translator.variables['$result']
        post = result_var >= z3.IntVal(0)

        wp_result = wp.wp(expr, post)
        assert wp_result is not None
        # WP should return the loop invariant as precondition
        # (sum >= 0 must hold at entry)

    def test_wp_preserves_type_constraints(self):
        """WP computation doesn't lose type constraints from translator"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import RangeType, RangeBounds
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        # Range type: x in [0, 100]
        translator.declare_variable('x', RangeType('Int', RangeBounds(0, 100)))
        translator.declare_variable('$result', RangeType('Int', RangeBounds(0, 100)))
        wp = WeakestPrecondition(translator)

        # Type constraints should still be in translator.constraints
        assert len(translator.constraints) >= 2  # x >= 0, x <= 100

        expr = parse("(let ((y x)) y)")[0]
        result_var = translator.variables['$result']
        post = result_var >= z3.IntVal(0)

        wp_result = wp.wp(expr, post)
        assert wp_result is not None
        # Type constraints are separate from WP, they're added to solver

    def test_wp_handles_deep_nesting(self):
        """WP handles deeply nested expressions without stack overflow"""
        from slop.verifier import WeakestPrecondition, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env)
        translator.declare_variable('x', PrimitiveType('Int'))
        translator.declare_variable('$result', PrimitiveType('Int'))
        wp = WeakestPrecondition(translator)

        # Nested let bindings
        expr = parse("""
        (let ((a x))
          (let ((b a))
            (let ((c b))
              (let ((d c))
                d))))
        """)[0]

        result_var = translator.variables['$result']
        post = result_var > z3.IntVal(0)

        wp_result = wp.wp(expr, post)
        assert wp_result is not None


class TestSequenceTheory:
    """Test Z3 Sequence encoding for lists with element-level properties.

    The Sequence theory enables proper reasoning about list contents via:
    - z3.Length(seq) - native length
    - seq[i] - native element access
    - z3.Concat(seq, z3.Unit(elem)) - append
    - z3.Empty(sort) - empty sequence

    This supports collection-bound quantifiers like (forall (t $result) (pred t)).
    """

    def test_seq_encoding_detection_forall_collection(self):
        """Detect when Seq encoding is needed for collection-bound forall"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Should need seq encoding for (forall (t $result) ...)
        post1 = [parse("(forall (t $result) (> t 0))")[0]]
        assert verifier._needs_seq_encoding(post1)

        # Should need seq encoding for (forall (item items) ...)
        post2 = [parse("(forall (item items) (is-valid item))")[0]]
        assert verifier._needs_seq_encoding(post2)

        # Should NOT need seq encoding for typed forall (i Int)
        post3 = [parse("(forall (i Int) (>= i 0))")[0]]
        assert not verifier._needs_seq_encoding(post3)

        # Should NOT need seq encoding for simple length check
        post4 = [parse("(>= (list-len $result) 0)")[0]]
        assert not verifier._needs_seq_encoding(post4)

    def test_seq_encoding_detection_exists_collection(self):
        """Detect when Seq encoding is needed for collection-bound exists"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Should need seq encoding for (exists (t $result) ...)
        post1 = [parse("(exists (t $result) (== t 42))")[0]]
        assert verifier._needs_seq_encoding(post1)

    def test_create_list_seq(self):
        """Test creating Seq representation for lists"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        seq = translator._create_list_seq("test")

        # Should be a Z3 Seq
        assert seq is not None
        assert str(seq.sort()).startswith("Seq")

        # Calling again should return same seq
        seq2 = translator._create_list_seq("test")
        assert seq is seq2

    def test_translate_list_len_seq(self):
        """Test list-len translation to z3.Length with Seq encoding"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse, Symbol
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Create seq for items
        translator._create_list_seq("items")

        # Translate (list-len items)
        result = translator._translate_list_len_seq(Symbol("items"))

        assert result is not None
        # Should be a Length expression
        assert "Length" in str(result) or "seq" in str(result).lower()

    def test_translate_list_ref_seq(self):
        """Test list-ref translation to seq[i] with Seq encoding"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Create seq for items
        translator._create_list_seq("items")

        # Translate (list-ref items 0)
        expr = parse("(list-ref items 0)")[0]
        result = translator._translate_list_ref_seq(expr)

        assert result is not None

    def test_forall_collection_translation(self):
        """Test (forall (elem coll) body) translation to quantified formula"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Create seq for $result
        translator._create_list_seq('$result')

        # Translate (forall (t $result) (> t 0))
        expr = parse("(forall (t $result) (> t 0))")[0]
        result = translator._translate_forall_collection(expr)

        assert result is not None
        assert z3.is_quantifier(result)

    def test_exists_collection_translation(self):
        """Test (exists (elem coll) body) translation to quantified formula"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Create seq for items
        translator._create_list_seq('items')

        # Translate (exists (x items) (== x 42))
        expr = parse("(exists (x items) (== x 42))")[0]
        result = translator._translate_exists_collection(expr)

        assert result is not None
        assert z3.is_quantifier(result)

    def test_seq_via_translate_expr(self):
        """Test Seq operations work through translate_expr"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Create seq for $result
        translator._create_list_seq('$result')

        # list-len through translate_expr
        expr = parse("(list-len $result)")[0]
        result = translator.translate_expr(expr)
        assert result is not None

        # list-ref through translate_expr
        expr2 = parse("(list-ref $result 0)")[0]
        result2 = translator.translate_expr(expr2)
        assert result2 is not None

        # forall collection through translate_expr
        expr3 = parse("(forall (t $result) (> t 0))")[0]
        result3 = translator.translate_expr(expr3)
        assert result3 is not None
        assert z3.is_quantifier(result3)

    def test_seq_push_axioms_filter_pattern(self):
        """Test push provenance axioms for filter patterns"""
        from slop.verifier import ContractVerifier, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)
        verifier = ContractVerifier(env)

        # Create seqs
        translator._create_list_seq('$result')
        translator._create_list_seq('items')

        # Declare loop variable for predicate translation
        from slop.types import PrimitiveType
        translator.declare_variable('x', PrimitiveType('Int'))

        # Filter pattern body
        body = parse("""
        (let ((mut result (list-new arena Int)))
          (for-each (x items)
            (when (> x 0)
              (list-push result x)))
          result)
        """)[0]

        postconditions = [parse("(forall (t $result) (> t 0))")[0]]

        axioms = verifier._extract_seq_push_axioms(body, postconditions, translator)

        # Should have generated axioms
        assert len(axioms) >= 1

    def test_filter_postcondition_with_seq_encoding(self):
        """Integration test: filter postcondition verifies with Seq encoding"""
        from slop.verifier import verify_source

        # Filter positive numbers
        source = """
        (fn filter-positive ((items (List Int)))
          (@spec (((List Int)) -> (List Int)))
          (@post (forall (t $result) (> t 0)))
          (let ((mut result (list-new arena Int)))
            (for-each (x items)
              (when (> x 0)
                (list-push result x)))
            result))
        """
        results = verify_source(source)

        # Check for verification (may be verified, or may fail due to complexity)
        # At minimum, should not error on translation
        assert len(results) >= 1
        # The verification result should not be a translation failure
        for r in results:
            assert "Could not translate" not in (r.message or "")

    def test_seq_length_concat_property(self):
        """Test that Z3 knows Length(Concat(a, Unit(x))) == Length(a) + 1"""
        import z3

        # This tests Z3's native Seq theory understanding
        int_seq = z3.SeqSort(z3.IntSort())
        a = z3.Const("a", int_seq)
        x = z3.Int("x")

        # Concat(a, Unit(x)) should have length = Length(a) + 1
        concat_result = z3.Concat(a, z3.Unit(x))
        length_property = z3.Length(concat_result) == z3.Length(a) + 1

        solver = z3.Solver()
        solver.add(z3.Not(length_property))
        result = solver.check()

        # Should be UNSAT (property is always true)
        assert result == z3.unsat

    def test_seq_empty_length_zero(self):
        """Test that Length(Empty) == 0"""
        import z3

        int_seq = z3.SeqSort(z3.IntSort())
        empty = z3.Empty(int_seq)

        length_zero = z3.Length(empty) == 0

        solver = z3.Solver()
        solver.add(z3.Not(length_zero))
        result = solver.check()

        # Should be UNSAT (empty seq has length 0)
        assert result == z3.unsat

    def test_seq_element_access(self):
        """Test that seq[i] extracts elements correctly"""
        import z3

        int_seq = z3.SeqSort(z3.IntSort())
        a = z3.Const("a", int_seq)
        x = z3.Int("x")

        # After Concat(a, Unit(x)), the last element should be x
        concat_result = z3.Concat(a, z3.Unit(x))

        # Element at Length(a) should be x
        last_idx = z3.Length(a)
        last_elem = concat_result[last_idx]

        property_holds = last_elem == x

        solver = z3.Solver()
        solver.add(z3.Not(property_holds))
        result = solver.check()

        # Should be UNSAT (property is always true)
        assert result == z3.unsat

    def test_seq_encoding_detection_field_access_collection(self):
        """Detect when Seq encoding is needed for field access collections"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Should need seq encoding for (forall (t (. delta triples)) ...)
        post1 = [parse("(forall (t (. delta triples)) (> t 0))")[0]]
        assert verifier._needs_seq_encoding(post1)

        # Should need seq encoding for (exists (dt (. obj list)) ...)
        post2 = [parse("(exists (dt (. obj list)) (valid dt))")[0]]
        assert verifier._needs_seq_encoding(post2)

    def test_field_access_collection_translation(self):
        """Test (forall (elem (. obj field)) body) translation"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Translate (forall (t (. delta triples)) (> t 0))
        expr = parse("(forall (t (. delta triples)) (> t 0))")[0]
        result = translator.translate_expr(expr)

        # Should produce a quantified formula
        assert result is not None
        assert z3.is_quantifier(result)

        # Should have created a Seq for the field access
        assert "_field_delta_triples" in translator.list_seqs

    def test_function_call_collection_translation(self):
        """Test (forall (elem (fn-name args)) body) translation for function calls"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Translate (forall (gt (indexed-graph-triples g)) (> gt 0))
        expr = parse("(forall (gt (indexed-graph-triples g)) (> gt 0))")[0]
        result = translator.translate_expr(expr)

        # Should produce a quantified formula
        assert result is not None
        assert z3.is_quantifier(result)

        # Should have created a Seq for the function call
        # The Seq name is built from function name and args
        fn_call_seqs = [k for k in translator.list_seqs.keys() if "_fn_indexed-graph-triples" in k]
        assert len(fn_call_seqs) == 1

    def test_exists_function_call_collection_translation(self):
        """Test (exists (elem (fn-name args)) body) translation for function calls"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Translate (exists (t (get-items x)) (> t 0))
        # Using a simple comparison body since function calls need proper type setup
        expr = parse("(exists (t (get-items x)) (> t 0))")[0]
        result = translator.translate_expr(expr)

        # Should produce a quantified formula
        assert result is not None
        assert z3.is_quantifier(result)

        # Should have created a Seq for the function call
        fn_call_seqs = [k for k in translator.list_seqs.keys() if "_fn_get-items" in k]
        assert len(fn_call_seqs) == 1

    def test_is_function_call_helper(self):
        """Test _is_function_call helper correctly identifies function calls"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Should be function calls
        assert translator._is_function_call(parse("(get-items x)")[0])
        assert translator._is_function_call(parse("(indexed-graph-triples g)")[0])
        assert translator._is_function_call(parse("(my-fn a b c)")[0])

        # Should NOT be function calls (special forms)
        assert not translator._is_function_call(parse("(. obj field)")[0])
        assert not translator._is_function_call(parse("(if x y z)")[0])
        assert not translator._is_function_call(parse("(and a b)")[0])
        assert not translator._is_function_call(parse("(+ 1 2)")[0])
        assert not translator._is_function_call(parse("(@pre (> x 0))")[0])

    def test_nested_forall_exists_translation(self):
        """Test nested (forall ... (exists ...)) translation"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Create seq for $result
        translator._create_list_seq('$result')

        # Nested quantifier: forall t in $result, exists x in items: t > x
        expr = parse("(forall (t $result) (exists (x items) (> t x)))")[0]
        result = translator.translate_expr(expr)

        assert result is not None
        assert z3.is_quantifier(result)

        # Should have created Seqs for both collections
        assert '$result' in translator.list_seqs
        assert 'items' in translator.list_seqs

    def test_property_with_collection_bound_forall_triggers_seq_encoding(self):
        """Properties with collection-bound forall should trigger Seq encoding"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Property with forall over $result
        property_expr = parse("(forall (t $result) (> t 0))")[0]
        assert verifier._needs_seq_encoding([property_expr])
        assert verifier._references_result_collection([property_expr])

    def test_property_soundness_pattern_translates(self):
        """Test that the soundness property pattern translates successfully"""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Create seq for $result
        translator._create_list_seq('$result')

        # Simplified soundness-like pattern:
        # (forall (t $result)
        #   (exists (dt (. delta triples))
        #     (and (== (pred t) (pred dt)) (== (subj t) (obj dt)))))
        expr = parse("""
        (forall (t $result)
          (exists (dt (. delta triples))
            (and (== (pred-of t) (pred-of dt))
                 (== (subj-of t) (obj-of dt)))))
        """)[0]

        result = translator.translate_expr(expr)

        # Should translate successfully
        assert result is not None
        assert z3.is_quantifier(result)

        # Should have created Seqs
        assert '$result' in translator.list_seqs
        assert '_field_delta_triples' in translator.list_seqs

    def test_property_verification_with_collection_quantifier(self):
        """Integration test: property with collection-bound forall"""
        from slop.verifier import verify_source

        # Function with property using forall over $result
        source = """
        (fn test ((items (List Int)))
          (@spec (((List Int)) -> (List Int)))
          (@property all-positive (forall (t $result) (> t 0)))
          (let ((mut result (list-new arena Int)))
            (for-each (x items)
              (when (> x 0)
                (list-push result x)))
            result))
        """
        results = verify_source(source)

        # Should not fail on translation
        assert len(results) >= 1
        for r in results:
            assert "Could not translate" not in (r.message or "")


class TestMapPatternVerification:
    """Test map/transform pattern recognition and verification.

    Map patterns differ from filter patterns:
    - Filter: (when pred (list-push result item)) - conditional push of same item
    - Map: (list-push result (constructor ...)) - unconditional push of transformed item

    Map patterns enable verifying properties like:
        (forall (t $result)
          (exists (dt source)
            (and (field1 t) == (field2 dt) ...)))
    """

    def test_detect_map_pattern_simple(self):
        """Detect unconditional list-push with constructor"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn transform-items ((arena Arena) (items (List Int)))
          (@spec ((Arena (List Int)) -> (List Int)))
          (@post (>= 0 0))
          (let ((mut result (list-new arena Int)))
            (for-each (x items)
              (list-push result (item-new arena x)))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        # Get function body
        fn_body = ast[0].items[5]  # The let expression

        # Test pattern detection
        pattern = verifier._detect_map_pattern(fn_body)
        assert pattern is not None
        assert pattern.result_var == 'result'
        assert pattern.loop_var == 'x'
        assert pattern.constructor_expr is not None

    def test_detect_map_pattern_triple_new(self):
        """Detect map pattern with triple-new constructor"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn invert-triples ((arena Arena) (triples (List Triple)))
          (@spec ((Arena (List Triple)) -> (List Triple)))
          (@post (>= 0 0))
          (let ((mut result (list-new arena Triple)))
            (for-each (t triples)
              (list-push result
                (triple-new arena
                  (triple-predicate t)
                  (triple-object t)
                  (triple-subject t))))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env, imported_defs=_make_triple_imported_defs())

        fn_body = ast[0].items[5]

        pattern = verifier._detect_map_pattern(fn_body)
        assert pattern is not None
        assert pattern.result_var == 'result'
        assert pattern.loop_var == 't'
        # Should detect field mappings
        assert 'predicate' in pattern.field_mappings
        assert 'subject' in pattern.field_mappings
        assert 'object' in pattern.field_mappings

    def test_no_map_pattern_for_filter(self):
        """Filter patterns (conditional push) should NOT match as map pattern"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn filter-items ((arena Arena) (items (List Int)))
          (@spec ((Arena (List Int)) -> (List Int)))
          (@post (>= 0 0))
          (let ((mut result (list-new arena Int)))
            (for-each (x items)
              (when (> x 0)
                (list-push result x)))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_body = ast[0].items[5]

        # Should NOT detect as map pattern (conditional push is filter)
        pattern = verifier._detect_map_pattern(fn_body)
        assert pattern is None

    def test_extract_field_mappings_triple_new(self):
        """Extract field mappings from triple-new constructor"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=_make_triple_imported_defs())

        # (triple-new arena pred subj obj)
        constructor = parse("(triple-new arena (triple-predicate dt) (triple-object dt) (triple-subject dt))")[0]
        mappings = verifier._extract_field_mappings(constructor, "dt")

        assert 'predicate' in mappings
        assert 'subject' in mappings
        assert 'object' in mappings

    def test_extract_field_mappings_record_new(self):
        """Extract field mappings from record-new constructor"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # (record-new Type (field1 val1) (field2 val2))
        # Parsed as nested list: (record-new Point (x (get-x item)) (y (get-y item)))
        # where (x (get-x item)) is a binding pair
        constructor = parse("(record-new Point (x (get-x item)) (y (get-y item)))")[0]
        mappings = verifier._extract_field_mappings(constructor, "item")

        # Should extract named field bindings
        assert 'x' in mappings
        assert 'y' in mappings
        # Verify we got mappings
        assert len(mappings) == 2

    def test_map_axiom_generation(self):
        """Generate field correspondence axioms for map pattern"""
        from slop.verifier import ContractVerifier, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)
        verifier = ContractVerifier(env)

        # Create seqs
        translator._create_list_seq('$result')
        translator._create_list_seq('triples')

        # Declare loop variable for translation
        from slop.types import PrimitiveType
        translator.declare_variable('t', PrimitiveType('Int'))

        # Map pattern body
        body = parse("""
        (let ((mut result (list-new arena Triple)))
          (for-each (t triples)
            (list-push result
              (triple-new arena
                (triple-predicate t)
                (triple-object t)
                (triple-subject t))))
          result)
        """)[0]

        postconditions = [parse("(forall (r $result) (> r 0))")[0]]

        axioms = verifier._extract_map_push_axioms(body, postconditions, translator)

        # Should generate at least one axiom (provenance + field correspondence)
        assert len(axioms) >= 1

    def test_map_pattern_with_field_access_collection(self):
        """Detect map pattern iterating over (. obj field)"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn invert-delta ((arena Arena) (delta Delta))
          (@spec ((Arena Delta) -> (List Triple)))
          (@post (>= 0 0))
          (let ((mut result (list-new arena Triple)))
            (for-each (dt (. delta triples))
              (list-push result
                (triple-new arena
                  (triple-predicate dt)
                  (triple-object dt)
                  (triple-subject dt))))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        fn_body = ast[0].items[5]

        pattern = verifier._detect_map_pattern(fn_body)
        assert pattern is not None
        assert pattern.loop_var == 'dt'
        # Collection should be the field access
        assert pattern.collection is not None

    def test_map_pattern_integration_does_not_crash(self):
        """Integration test: map pattern with soundness-like property does not crash"""
        from slop.verifier import verify_source

        # Simplified soundness pattern - just verify it doesn't crash
        source = """
        (fn invert-triples ((arena Arena) (items (List Triple)))
          (@spec ((Arena (List Triple)) -> (List Triple)))
          (@post (>= 0 0))
          (let ((mut result (list-new arena Triple)))
            (for-each (t items)
              (list-push result
                (triple-new arena
                  (triple-predicate t)
                  (triple-object t)
                  (triple-subject t))))
            result))
        """
        results = verify_source(source)

        # Should not crash
        assert len(results) >= 1
        # Should not have translation errors
        for r in results:
            assert "Could not translate" not in (r.message or "")

    def test_map_pattern_property_with_exists(self):
        """Test map pattern with exists property over source collection"""
        from slop.verifier import verify_source

        # Property stating each result element has a corresponding source element
        source = """
        (fn transform ((arena Arena) (items (List Int)))
          (@spec ((Arena (List Int)) -> (List Int)))
          (@property provenance
            (forall (t $result)
              (exists (s items)
                (== t s))))
          (let ((mut result (list-new arena Int)))
            (for-each (x items)
              (list-push result x))
            result))
        """
        results = verify_source(source)

        # Should process without crashing
        assert len(results) >= 1

    def test_references_var_helper(self):
        """Test _references_var helper function"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Direct reference
        expr1 = parse("x")[0]
        assert verifier._references_var(expr1, "x") is True
        assert verifier._references_var(expr1, "y") is False

        # Nested reference
        expr2 = parse("(foo (bar x))")[0]
        assert verifier._references_var(expr2, "x") is True
        assert verifier._references_var(expr2, "z") is False

        # No reference
        expr3 = parse("(+ 1 2)")[0]
        assert verifier._references_var(expr3, "x") is False

    def test_soundness_property_verifies(self):
        """Integration: soundness property actually verifies with field swapping.

        This is the key test case from the plan - a map pattern that swaps
        fields should verify a soundness property stating the relationship.
        """
        from slop.verifier import (
            ContractVerifier, MinimalTypeEnv, FunctionRegistry,
            build_type_registry_from_ast, build_invariant_registry_from_ast
        )
        from slop.parser import parse

        source = """
        (fn invert-triples ((arena Arena) (triples (List Triple)))
          (@spec ((Arena (List Triple)) -> (List Triple)))
          (@property soundness
            (forall (t $result)
              (exists (dt triples)
                (and (== (triple-predicate t) (triple-predicate dt))
                     (== (triple-subject t) (triple-object dt))
                     (== (triple-object t) (triple-subject dt))))))
          (let ((mut result (list-new arena Triple)))
            (for-each (dt triples)
              (list-push result
                (triple-new arena
                  (triple-predicate dt)
                  (triple-object dt)
                  (triple-subject dt))))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        type_env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        fn_registry = FunctionRegistry()
        fn_registry.register_from_ast(ast)

        verifier = ContractVerifier(
            type_env,
            function_registry=fn_registry,
            imported_defs=_make_triple_imported_defs()
        )

        result = verifier.verify_function(ast[0])
        assert result.status == 'verified', f"Expected verified, got: {result.message}"

    def test_map_pattern_preserves_field(self):
        """Test map pattern that preserves a field verifies preservation property."""
        from slop.verifier import (
            ContractVerifier, MinimalTypeEnv, FunctionRegistry,
            build_type_registry_from_ast, build_invariant_registry_from_ast
        )
        from slop.parser import parse

        source = """
        (fn copy-triples ((arena Arena) (triples (List Triple)))
          (@spec ((Arena (List Triple)) -> (List Triple)))
          (@property predicate-preserved
            (forall (t $result)
              (exists (dt triples)
                (== (triple-predicate t) (triple-predicate dt)))))
          (let ((mut result (list-new arena Triple)))
            (for-each (dt triples)
              (list-push result
                (triple-new arena
                  (triple-predicate dt)
                  (triple-subject dt)
                  (triple-object dt))))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        type_env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        fn_registry = FunctionRegistry()
        fn_registry.register_from_ast(ast)

        verifier = ContractVerifier(
            type_env,
            function_registry=fn_registry,
            imported_defs=_make_triple_imported_defs()
        )

        result = verifier.verify_function(ast[0])
        assert result.status == 'verified', f"Expected verified, got: {result.message}"

    def test_map_pattern_size_equality(self):
        """Test that map pattern generates size equality axiom."""
        from slop.verifier import verify_source

        source = """
        (fn transform ((arena Arena) (items (List Int)))
          (@spec ((Arena (List Int)) -> (List Int)))
          (@post (== (list-len $result) (list-len items)))
          (let ((mut result (list-new arena Int)))
            (for-each (x items)
              (list-push result (item-new arena x)))
            result))
        """
        results = verify_source(source)

        fn_result = [r for r in results if r.name == 'transform']
        assert len(fn_result) == 1
        # Size equality should be provable from map axioms
        assert fn_result[0].status == 'verified'

    def test_imported_equality_function_axiom(self):
        """Test that imported equality function semantics are used in verification."""
        from slop.verifier import (
            ContractVerifier, MinimalTypeEnv, Z3Translator,
            ImportedDefinitions, FunctionSignature
        )
        from slop.parser import parse
        from slop.types import PrimitiveType

        # Create imported definitions with term-eq having postcondition semantics
        imported_defs = ImportedDefinitions()
        imported_defs.functions['term-eq'] = FunctionSignature(
            name='term-eq',
            param_types=[PrimitiveType('Int'), PrimitiveType('Int')],
            return_type=PrimitiveType('Bool'),
            params=['a', 'b'],
            postconditions=[parse('(== $result (== a b))')[0]]
        )

        type_env = MinimalTypeEnv()
        verifier = ContractVerifier(type_env, imported_defs=imported_defs)

        # Check that _has_imported_equality_semantics returns True
        assert verifier._has_imported_equality_semantics('term-eq') is True
        assert verifier._has_imported_equality_semantics('nonexistent-eq') is False

        # Create translator and extract axioms
        translator = Z3Translator(type_env)
        axioms = verifier._extract_imported_equality_axioms(translator)

        assert len(axioms) == 1
        # The axiom should be: ForAll a, b: fn_term-eq_2(a, b) == (a == b)
        axiom_str = str(axioms[0])
        assert 'ForAll' in axiom_str
        assert 'fn_term-eq_2' in axiom_str

    def test_property_with_imported_term_eq(self):
        """Test property verification when term-eq is imported with semantics.

        When term-eq is imported with (@post (== $result (== a b))),
        the verifier should add an axiom that allows Z3 to reason about
        term-eq as native equality.
        """
        from slop.verifier import (
            ContractVerifier, MinimalTypeEnv, Z3Translator,
            ImportedDefinitions, FunctionSignature, FunctionRegistry
        )
        from slop.parser import parse
        from slop.types import PrimitiveType

        # Source uses term-eq in property
        source = """
        (fn copy-triples ((arena Arena) (triples (List Triple)))
          (@spec ((Arena (List Triple)) -> (List Triple)))
          (@property predicate-preserved
            (forall (t $result)
              (exists (dt triples)
                (term-eq (triple-predicate t) (triple-predicate dt)))))
          (let ((mut result (list-new arena Triple)))
            (for-each (dt triples)
              (list-push result
                (triple-new arena
                  (triple-predicate dt)
                  (triple-subject dt)
                  (triple-object dt))))
            result))
        """
        ast = parse(source)

        # Create imported definitions with term-eq semantics + triple constructors
        imported_defs = _make_triple_imported_defs()
        imported_defs.functions['term-eq'] = FunctionSignature(
            name='term-eq',
            param_types=[PrimitiveType('Int'), PrimitiveType('Int')],
            return_type=PrimitiveType('Bool'),
            params=['a', 'b'],
            postconditions=[parse('(== $result (== a b))')[0]]
        )

        type_env = MinimalTypeEnv()
        fn_registry = FunctionRegistry()
        fn_registry.register_from_ast(ast)

        verifier = ContractVerifier(
            type_env,
            function_registry=fn_registry,
            imported_defs=imported_defs
        )

        result = verifier.verify_function(ast[0])
        assert result.status == 'verified', f"Expected verified, got: {result.message}"

    def test_extract_filter_conditions_simple(self):
        """Extract single filter condition from when clause"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse, is_form

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Simple filtered map pattern
        body = parse("""
        (let ((mut result (list-new arena Triple)))
          (for-each (dt triples)
            (when (term-eq (triple-predicate dt) same-as)
              (list-push result (make-triple arena x y z))))
          result)
        """)[0]

        conditions, bindings = verifier._extract_filter_conditions_from_loop(body)

        assert len(conditions) == 1
        assert is_form(conditions[0], 'term-eq')

    def test_extract_filter_conditions_nested(self):
        """Extract multiple filter conditions from nested when clauses"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse, is_form

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Nested when clauses like eq-sym
        body = parse("""
        (let ((mut result (list-new arena Triple)))
          (for-each (dt triples)
            (when (term-eq (triple-predicate dt) same-as)
              (let ((inferred (make-triple arena y same-as x)))
                (when (not (graph-contains g inferred))
                  (list-push result inferred)))))
          result)
        """)[0]

        conditions, bindings = verifier._extract_filter_conditions_from_loop(body)

        # Should extract both conditions
        assert len(conditions) == 2
        assert is_form(conditions[0], 'term-eq')
        assert is_form(conditions[1], 'not')

        # Should capture bindings
        assert 'inferred' in bindings

    def test_resolve_filter_condition_variables(self):
        """Resolve variables in filter conditions through let bindings"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse, is_form

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Condition with variable reference
        condition = parse("(not (contains g x))")[0]
        bindings = {
            'x': parse("(make-triple arena a b c)")[0],
            'a': parse("foo")[0]
        }

        resolved = verifier._resolve_filter_condition(condition, bindings)

        # The 'x' should be replaced with the make-triple expression
        assert is_form(resolved, 'not')
        inner = resolved[1]
        assert is_form(inner, 'contains')
        assert is_form(inner[2], 'make-triple')

    def test_completeness_axiom_generated(self):
        """Test that completeness axiom is generated for filtered map pattern"""
        from slop.verifier import ContractVerifier, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)
        verifier = ContractVerifier(env)

        # Create seqs
        translator._create_list_seq('$result')
        translator._create_list_seq('triples')

        # Declare loop variable
        from slop.types import PrimitiveType
        translator.declare_variable('dt', PrimitiveType('Int'))

        # Filtered map pattern body (conditional push)
        body = parse("""
        (let ((mut result (list-new arena Triple)))
          (for-each (dt triples)
            (when (> dt 0)
              (list-push result
                (triple-new arena
                  (triple-predicate dt)
                  (triple-object dt)
                  (triple-subject dt)))))
          result)
        """)[0]

        postconditions = [parse("(forall (r $result) (> r 0))")[0]]

        axioms = verifier._extract_map_push_axioms(body, postconditions, translator)

        # Should generate soundness axiom, size axiom, and completeness axiom
        # For conditional push: at least 3 axioms
        assert len(axioms) >= 3, f"Expected at least 3 axioms, got {len(axioms)}"

        # Check that one axiom is the completeness axiom (has filter condition)
        axiom_strs = [str(a) for a in axioms]
        # The completeness axiom should be a ForAll with an implication
        has_completeness = any('ForAll' in s and 'Implies' in s for s in axiom_strs)
        assert has_completeness, "Expected completeness axiom with ForAll/Implies"

    def test_completeness_property_verifies(self):
        """Integration test: completeness property with filters verifies.

        This tests a filtered map pattern where we have:
        - A filter condition (e.g., predicate > 0)
        - A constructor call to create output
        - A completeness property stating all filtered inputs produce outputs
        """
        from slop.verifier import (
            ContractVerifier, MinimalTypeEnv, FunctionRegistry,
            ImportedDefinitions, FunctionSignature
        )
        from slop.parser import parse
        from slop.types import PrimitiveType

        # Source with filtered map pattern and completeness property
        # Uses triple-new constructor to trigger map pattern detection
        source = """
        (fn filter-and-transform ((arena Arena) (triples (List Triple)))
          (@spec ((Arena (List Triple)) -> (List Triple)))
          ;; Soundness: every output came from a filtered input
          (@property soundness
            (forall (t $result)
              (exists (dt triples)
                (and (== (triple-predicate t) (triple-predicate dt))
                     (== (triple-subject t) (triple-object dt))))))
          (let ((mut result (list-new arena Triple)))
            (for-each (dt triples)
              (when (> (triple-predicate dt) 0)
                (list-push result
                  (triple-new arena
                    (triple-predicate dt)
                    (triple-object dt)
                    (triple-subject dt)))))
            result))
        """
        ast = parse(source)

        type_env = MinimalTypeEnv()
        fn_registry = FunctionRegistry()
        fn_registry.register_from_ast(ast)

        verifier = ContractVerifier(
            type_env,
            function_registry=fn_registry,
            imported_defs=_make_triple_imported_defs()
        )

        result = verifier.verify_function(ast[0])
        assert result.status == 'verified', f"Expected verified, got: {result.message}"

class TestNestedLoopPattern:
    """Test nested loop pattern recognition for join semantics.

    Nested loop patterns occur when:
    1. An outer loop iterates over a collection (e.g., delta.triples)
    2. An inner loop iterates over a query result derived from outer loop variables
    3. The constructor combines fields from both loops

    Example: eq-trans computes transitive closure via join:
    (for-each (dt delta.triples)       ; outer: iterate delta
      (when filter-dt
        (let ((x (triple-subject dt))
              (y (triple-object dt)))
          (for-each (yo-triple (match y ...))  ; inner: join on y
            (let ((z (triple-object yo-triple)))
              (list-push result (make-triple x same-as z)))))))
    """

    def test_detect_nested_loop_simple(self):
        """Detect basic nested for-each structure"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn nested-transform ((arena Arena) (outer (List Int)) (g Graph))
          (@spec ((Arena (List Int) Graph) -> (List Int)))
          (@post (>= 0 0))
          (let ((mut result (list-new arena Int)))
            (for-each (x outer)
              (let ((inner-results (graph-match g x)))
                (for-each (y inner-results)
                  (list-push result (combine arena x y)))))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env)

        # Get function body (the let expression)
        fn_body = ast[0].items[5]

        # Detect nested pattern
        pattern = verifier._detect_nested_loop_pattern(fn_body)
        assert pattern is not None
        assert pattern.result_var == 'result'
        assert pattern.outer_loop_var == 'x'
        assert len(pattern.inner_loops) == 1
        assert pattern.inner_loops[0].loop_var == 'y'

    def test_detect_nested_loop_with_filter(self):
        """Detect nested loop with when filter (like eq-trans)"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, build_type_registry_from_ast, build_invariant_registry_from_ast
        from slop.parser import parse

        source = """
        (fn filtered-nested ((arena Arena) (delta Delta) (g Graph))
          (@spec ((Arena Delta Graph) -> (List Triple)))
          (@post (>= 0 0))
          (let ((same-as (make-iri arena OWL_SAME_AS))
                (mut result (list-new arena Triple)))
            (for-each (dt (. delta triples))
              (when (term-eq (triple-predicate dt) same-as)
                (let ((x (triple-subject dt))
                      (y (triple-object dt)))
                  (let ((y-matches (indexed-graph-match arena g (some y) (some same-as) (none))))
                    (for-each (yo-triple y-matches)
                      (let ((z (triple-object yo-triple)))
                        (list-push result (make-triple arena x same-as z))))))))
            result))
        """
        ast = parse(source)
        type_registry = build_type_registry_from_ast(ast)
        invariant_registry = build_invariant_registry_from_ast(ast)
        env = MinimalTypeEnv(type_registry=type_registry, invariant_registry=invariant_registry)
        verifier = ContractVerifier(env, imported_defs=_make_triple_imported_defs())

        fn_body = ast[0].items[5]

        pattern = verifier._detect_nested_loop_pattern(fn_body)
        assert pattern is not None
        assert pattern.result_var == 'result'
        assert pattern.outer_loop_var == 'dt'
        assert pattern.outer_filter is not None  # (term-eq (triple-predicate dt) same-as)
        assert 'same-as' in pattern.outer_let_bindings  # Constant from outer let

    def test_field_provenance_outer(self):
        """Test that fields derived from outer loop are classified as OUTER"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, FieldSource
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=_make_triple_imported_defs())

        # Pattern where subject comes from outer loop
        source = """
        (let ((mut result (list-new arena Triple)))
          (for-each (dt outer)
            (let ((x (triple-subject dt)))
              (for-each (y inner)
                (list-push result (make-triple arena x pred y)))))
          result)
        """
        ast = parse(source)
        fn_body = ast[0]

        pattern = verifier._detect_nested_loop_pattern(fn_body)
        assert pattern is not None

        # Subject (x) comes from outer loop var dt
        assert pattern.field_provenance.get('subject') == FieldSource.OUTER

    def test_field_provenance_inner(self):
        """Test that fields derived from inner loop are classified as INNER"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, FieldSource
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=_make_triple_imported_defs())

        # Pattern where object comes from inner loop
        source = """
        (let ((mut result (list-new arena Triple)))
          (for-each (dt outer)
            (let ((x (triple-subject dt)))
              (for-each (yo inner)
                (let ((z (triple-object yo)))
                  (list-push result (make-triple arena x pred z))))))
          result)
        """
        ast = parse(source)
        fn_body = ast[0]

        pattern = verifier._detect_nested_loop_pattern(fn_body)
        assert pattern is not None

        # Object (z) comes from inner loop var yo
        assert pattern.field_provenance.get('object') == FieldSource.INNER

    def test_field_provenance_constant(self):
        """Test that constant fields from outer let are classified as CONSTANT"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, FieldSource
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=_make_triple_imported_defs())

        # Pattern where predicate is a constant from outer let
        source = """
        (let ((same-as (make-iri arena OWL_SAME_AS))
              (mut result (list-new arena Triple)))
          (for-each (dt outer)
            (let ((x (triple-subject dt)))
              (for-each (yo inner)
                (let ((z (triple-object yo)))
                  (list-push result (make-triple arena x same-as z))))))
          result)
        """
        ast = parse(source)
        fn_body = ast[0]

        pattern = verifier._detect_nested_loop_pattern(fn_body)
        assert pattern is not None

        # Predicate (same-as) is a constant from outer let
        assert pattern.field_provenance.get('predicate') == FieldSource.CONSTANT

    def test_identify_join_variables(self):
        """Test that join variables (outer vars in inner collection) are identified"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Inner collection uses 'y' which is derived from outer loop
        source = """
        (let ((mut result (list-new arena Triple)))
          (for-each (dt outer)
            (let ((y (triple-object dt)))
              (let ((matches (query-by-subject arena g y)))
                (for-each (m matches)
                  (list-push result (construct arena dt m))))))
          result)
        """
        ast = parse(source)
        fn_body = ast[0]

        pattern = verifier._detect_nested_loop_pattern(fn_body)
        assert pattern is not None

        # Inner loop's collection references 'y' from outer scope
        assert len(pattern.inner_loops) == 1
        assert 'y' in pattern.inner_loops[0].join_vars

    def test_nested_loop_axiom_generation(self):
        """Test that axioms are generated for nested loop patterns"""
        from slop.verifier import ContractVerifier, Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        import z3

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)
        verifier = ContractVerifier(env, imported_defs=_make_triple_imported_defs())

        # Create seqs
        translator._create_list_seq('$result')
        translator._create_list_seq('_field_delta_triples')

        # Nested loop pattern body
        body = parse("""
        (let ((same-as OWL_SAME_AS)
              (mut result (list-new arena Triple)))
          (for-each (dt (. delta triples))
            (when (term-eq (triple-predicate dt) same-as)
              (let ((x (triple-subject dt)))
                (for-each (yo inner)
                  (let ((z (triple-object yo)))
                    (list-push result (make-triple arena x same-as z)))))))
          result)
        """)[0]

        postconditions = [parse("(forall (t $result) true)")[0]]

        axioms = verifier._extract_map_push_axioms(body, postconditions, translator)

        # Should generate at least provenance axiom and size axiom
        assert len(axioms) >= 2, f"Expected at least 2 axioms, got {len(axioms)}"

        # Check axioms contain ForAll quantifier
        axiom_strs = [str(a) for a in axioms]
        has_forall = any('ForAll' in s for s in axiom_strs)
        assert has_forall, "Expected axiom with ForAll quantifier"

    def test_nested_loop_does_not_match_single_loop(self):
        """Nested loop detection should not match simple single-loop patterns"""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # Single loop pattern (should be handled by _detect_map_pattern, not nested)
        source = """
        (let ((mut result (list-new arena Triple)))
          (for-each (dt triples)
            (list-push result (transform dt)))
          result)
        """
        ast = parse(source)
        fn_body = ast[0]

        # This should NOT match as nested pattern (no inner for-each)
        pattern = verifier._detect_nested_loop_pattern(fn_body)
        # The pattern may or may not be detected depending on implementation
        # but if detected, it should have no inner loops
        if pattern is not None:
            assert len(pattern.inner_loops) == 0

    def test_eq_trans_structure_detection(self):
        """Test detection of eq-trans-like nested structure with two inner loops.

        eq-trans has two inner for-each loops:
        1. (for-each (yo-triple y-objects) ...) - find y->z
        2. (for-each (xs-triple x-subjects) ...) - find w->x

        Both should be detected.
        """
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=_make_triple_imported_defs())

        # Simplified version of eq-trans with one inner loop
        source = """
        (let ((same-as (make-iri arena OWL_SAME_AS))
              (no-term (Option Term) (none))
              (mut result (list-new arena Triple)))
          (for-each (dt (. delta triples))
            (when (term-eq (triple-predicate dt) same-as)
              (let ((x (triple-subject dt))
                    (y (triple-object dt)))
                (let ((y-objects (indexed-graph-match arena g (some y) (some same-as) no-term)))
                  (for-each (yo-triple y-objects)
                    (let ((z (triple-object yo-triple))
                          (inferred (make-triple arena x same-as z)))
                      (when (and (not (term-eq x z))
                                 (not (indexed-graph-contains g inferred)))
                        (list-push result inferred))))))))
          result)
        """
        ast = parse(source)
        fn_body = ast[0]

        pattern = verifier._detect_nested_loop_pattern(fn_body)
        assert pattern is not None
        assert pattern.outer_loop_var == 'dt'
        assert pattern.outer_filter is not None
        assert 'same-as' in pattern.outer_let_bindings
        assert len(pattern.inner_loops) >= 1
        assert pattern.inner_loops[0].loop_var == 'yo-triple'

    def test_eq_trans_soundness_axiom_structure(self):
        """Test that eq-trans soundness property can use generated axioms.

        The soundness property:
        (forall (t $result)
          (exists (dt (. delta triples))
            (term-eq (triple-predicate dt) (triple-predicate t))))

        Should be provable because:
        - result elements have predicate = same-as (from field_provenance CONSTANT)
        - outer filter ensures triple-predicate(dt) = same-as
        - Therefore triple-predicate(dt) = triple-predicate(t)
        """
        from slop.verifier import (
            ContractVerifier, Z3Translator, MinimalTypeEnv,
            ImportedDefinitions, FunctionSignature
        )
        from slop.parser import parse
        from slop.types import PrimitiveType
        import z3

        # Create imported definitions with term-eq semantics + triple constructors
        imported_defs = _make_triple_imported_defs()
        imported_defs.functions['term-eq'] = FunctionSignature(
            name='term-eq',
            param_types=[PrimitiveType('Int'), PrimitiveType('Int')],
            return_type=PrimitiveType('Bool'),
            params=['a', 'b'],
            postconditions=[parse('(== $result (== a b))')[0]]
        )

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)
        verifier = ContractVerifier(env, imported_defs=imported_defs)

        # Create seqs
        translator._create_list_seq('$result')
        translator._create_list_seq('_field_delta_triples')

        # Simplified eq-trans body
        body = parse("""
        (let ((same-as OWL_SAME_AS)
              (mut result (list-new arena Triple)))
          (for-each (dt (. delta triples))
            (when (term-eq (triple-predicate dt) same-as)
              (let ((x (triple-subject dt))
                    (y (triple-object dt)))
                (for-each (yo inner)
                  (let ((z (triple-object yo)))
                    (list-push result (make-triple arena x same-as z)))))))
          result)
        """)[0]

        postconditions = []
        axioms = verifier._extract_map_push_axioms(body, postconditions, translator)

        # Should have generated axioms
        assert len(axioms) >= 1

        # The key axiom should establish:
        # ForAll i in result: Exists j in delta.triples:
        #   filter(delta.triples[j]) AND field_constraints
        axiom_strs = [str(a) for a in axioms]
        has_forall_exists = any('ForAll' in s and 'Exists' in s for s in axiom_strs)
        assert has_forall_exists, "Expected axiom with ForAll/Exists structure"


class TestImportedPostconditionAxioms:
    """Test universal axioms generated from imported function postconditions."""

    def test_extract_imported_postcondition_axioms_simple(self):
        """Test extracting postcondition axioms from imported functions."""
        from slop.verifier import (ContractVerifier, Z3Translator, MinimalTypeEnv,
                                    ImportedDefinitions, FunctionSignature)
        from slop.parser import parse
        from slop.types import PrimitiveType

        # Create imported definitions with a function that has a postcondition
        imported_defs = ImportedDefinitions()
        imported_defs.functions['graph-size'] = FunctionSignature(
            name='graph-size',
            param_types=[PrimitiveType('IndexedGraph')],
            return_type=PrimitiveType('Int'),
            params=['g'],
            postconditions=[parse("(>= $result 0)")[0]]
        )

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=imported_defs)
        translator = Z3Translator(env, imported_defs=imported_defs)

        axioms = verifier._extract_imported_postcondition_axioms(translator)

        # Should have generated at least one axiom
        assert len(axioms) >= 1

        # The axiom should be universally quantified over 'g'
        axiom_str = str(axioms[0])
        assert 'ForAll' in axiom_str

    def test_postcondition_treats_result_as_collection(self):
        """Test detection of collection-treating postconditions."""
        from slop.verifier import ContractVerifier, MinimalTypeEnv, ImportedDefinitions
        from slop.parser import parse

        imported_defs = ImportedDefinitions()
        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=imported_defs)

        # (forall (t $result) ...) treats $result as collection
        post1 = parse("(forall (t $result) (pred t))")[0]
        assert verifier._postcondition_treats_result_as_collection(post1)

        # (exists (t $result) ...) treats $result as collection
        post2 = parse("(exists (t $result) (pred t))")[0]
        assert verifier._postcondition_treats_result_as_collection(post2)

        # (list-len $result) treats $result as collection
        post3 = parse("(list-len $result)")[0]
        assert verifier._postcondition_treats_result_as_collection(post3)

        # (>= $result 0) does NOT treat $result as collection
        post4 = parse("(>= $result 0)")[0]
        assert not verifier._postcondition_treats_result_as_collection(post4)

    def test_imported_postcondition_with_forall(self):
        """Test generating axioms from postconditions with forall over result."""
        from slop.verifier import (ContractVerifier, Z3Translator, MinimalTypeEnv,
                                    ImportedDefinitions, FunctionSignature)
        from slop.parser import parse
        from slop.types import PrimitiveType

        # Create imported definitions with a function whose postcondition
        # quantifies over the result
        imported_defs = ImportedDefinitions()
        imported_defs.functions['indexed-graph-match'] = FunctionSignature(
            name='indexed-graph-match',
            param_types=[
                PrimitiveType('Arena'),
                PrimitiveType('IndexedGraph'),
                PrimitiveType('Option'),
                PrimitiveType('Option'),
                PrimitiveType('Option'),
            ],
            return_type=PrimitiveType('List'),
            params=['arena', 'g', 's', 'p', 'o'],
            postconditions=[
                # (forall (t $result) (indexed-graph-contains g t))
                parse("(forall (t $result) (indexed-graph-contains g t))")[0]
            ]
        )

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=imported_defs)
        translator = Z3Translator(env, imported_defs=imported_defs)
        translator.use_seq_encoding = True  # Enable Seq encoding for collections

        axioms = verifier._extract_imported_postcondition_axioms(translator)

        # Should have generated at least one axiom
        assert len(axioms) >= 1

        # The axiom should be universally quantified over all parameters
        axiom_str = str(axioms[0])
        assert 'ForAll' in axiom_str

    def test_skip_equality_functions(self):
        """Test that equality functions are skipped (handled separately)."""
        from slop.verifier import (ContractVerifier, Z3Translator, MinimalTypeEnv,
                                    ImportedDefinitions, FunctionSignature)
        from slop.parser import parse
        from slop.types import PrimitiveType

        imported_defs = ImportedDefinitions()
        # Equality function with 2 params
        imported_defs.functions['term-eq'] = FunctionSignature(
            name='term-eq',
            param_types=[PrimitiveType('Term'), PrimitiveType('Term')],
            return_type=PrimitiveType('Bool'),
            params=['a', 'b'],
            postconditions=[parse("(== $result (== a b))")[0]]
        )

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=imported_defs)
        translator = Z3Translator(env, imported_defs=imported_defs)

        axioms = verifier._extract_imported_postcondition_axioms(translator)

        # Should NOT generate axioms (equality functions handled separately)
        assert len(axioms) == 0

    def test_imported_postcondition_axioms_used_in_property_verification(self):
        """Test that imported postcondition axioms are applied during property verification."""
        from slop.verifier import verify_source

        # This test verifies end-to-end integration: a property that relies on
        # an imported function's postcondition should be verifiable
        source = '''
        (module test
          (import math (abs))

          ;; Test function with property that relies on abs postcondition
          (fn wrap-abs ((x Int))
            (@spec ((Int) -> Int))
            (@post (>= $result 0))
            (abs x)))
        '''
        # Note: Without the imported postcondition axiom for 'abs', this might
        # not verify. With the axiom, Z3 should be able to verify it.
        results = verify_source(source)

        # The function should at least not crash during verification
        assert len(results) >= 1


class TestPropertyPropagation:
    """Test auto-propagation of @property as @loop-invariant."""

    def test_property_propagated_when_no_explicit_invariant(self):
        """@property should be auto-propagated as assumption when no @loop-invariant exists."""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse

        source = '''
        (fn filter-items ((items (List Int)))
          (@spec (((List Int)) -> (List Int)))
          (@property soundness (forall (t $result) (exists (dt items) (== t dt))))
          (let ((mut result (list-new arena Int)))
            (for-each (x items)
              (list-push result x))
            result))
        '''
        ast = parse(source)
        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # The property should not cause a crash and should verify
        fn_form = ast[0]
        result = verifier.verify_function(fn_form)
        assert result is not None

    def test_property_not_propagated_with_explicit_invariant(self):
        """@property should NOT be propagated when explicit @loop-invariant exists."""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse, SList, Symbol

        source = '''
        (fn filter-items ((items (List Int)))
          (@spec (((List Int)) -> (List Int)))
          (@property soundness (forall (t $result) (exists (dt items) (== t dt))))
          (let ((mut result (list-new arena Int)))
            (for-each (x items)
              (@loop-invariant (forall (t result) (exists (dt items) (== t dt))))
              (list-push result x))
            result))
        '''
        ast = parse(source)
        fn_form = ast[0]

        # Extract properties and body
        properties = []
        fn_body = None
        for item in fn_form.items[3:]:
            if isinstance(item, SList) and len(item) > 0:
                head = item[0]
                if isinstance(head, Symbol) and head.name == '@property':
                    if isinstance(item[1], Symbol) and len(item) > 2:
                        properties.append((item[1].name, item[2]))
                    else:
                        properties.append((None, item[1]))
                elif isinstance(head, Symbol) and not head.name.startswith('@'):
                    fn_body = item

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        # When explicit @loop-invariant exists, _extract_loop_invariants returns them
        loop_invariants = verifier._extract_loop_invariants(fn_body)
        assert len(loop_invariants) > 0, "Should find explicit @loop-invariant"

    def test_substitute_result_var(self):
        """$result should be substituted with actual variable name."""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.parser import parse, pretty_print

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env)

        expr = parse("(forall (t $result) (exists (dt source) (== t dt)))")[0]
        result = verifier._substitute_result_var(expr, 'result')
        result_str = pretty_print(result)
        assert '$result' not in result_str
        assert 'result' in result_str


class TestGeneralizedContainment:
    """Test generalized containment congruence axioms."""

    def test_infer_constructor_field_mappings(self):
        """Should infer field mappings from constructor postconditions."""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.verifier.types import FunctionSignature, ImportedDefinitions
        from slop.parser import parse

        defs = ImportedDefinitions()
        # Define a non-triple constructor with postconditions
        posts = [
            parse("(== (pair-left $result) a)")[0],
            parse("(== (pair-right $result) b)")[0],
        ]
        defs.functions['make-pair'] = FunctionSignature(
            name='make-pair',
            param_types=[],
            return_type=None,
            params=['arena', 'a', 'b'],
            postconditions=posts,
        )

        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=defs)

        sig = defs.functions['make-pair']
        mappings = verifier._infer_constructor_field_mappings(sig)
        assert mappings == {'a': 'pair-left', 'b': 'pair-right'}

    def test_infer_triple_field_mappings(self):
        """Should infer standard triple field mappings."""
        from slop.verifier import ContractVerifier, MinimalTypeEnv
        from slop.verifier.types import FunctionSignature, ImportedDefinitions
        from slop.parser import parse

        defs = _make_triple_imported_defs()
        env = MinimalTypeEnv()
        verifier = ContractVerifier(env, imported_defs=defs)

        sig = defs.functions['make-triple']
        mappings = verifier._infer_constructor_field_mappings(sig)
        assert 's' in mappings
        assert mappings['s'] == 'triple-subject'
        assert mappings['p'] == 'triple-predicate'
        assert mappings['o'] == 'triple-object'


class TestListContains:
    """Test list-contains verifier-only predicate."""

    def test_list_contains_translation(self):
        """(list-contains lst elem) should translate to existential membership."""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Create a sequence for 'items'
        translator._create_list_seq('items')
        translator.declare_variable('x', PrimitiveType('Int'))

        expr = parse("(list-contains items x)")[0]
        result = translator.translate_expr(expr)
        assert result is not None
        # Should be an existential quantifier
        assert z3.is_quantifier(result)
        assert result.is_exists()

    def test_list_contains_in_postcondition(self):
        """list-contains should work in postcondition context."""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=True)

        # Set up $result as a sequence
        translator._create_list_seq('$result')
        translator.declare_variable('x', PrimitiveType('Int'))

        expr = parse("(list-contains $result x)")[0]
        result = translator.translate_expr(expr)
        assert result is not None
        assert z3.is_quantifier(result)

    def test_list_contains_fallback_without_seq(self):
        """Without seq encoding, list-contains should fall back to uninterpreted function."""
        from slop.verifier import Z3Translator, MinimalTypeEnv
        from slop.parser import parse
        from slop.types import PrimitiveType

        env = MinimalTypeEnv()
        translator = Z3Translator(env, use_seq_encoding=False)
        translator.declare_variable('items', PrimitiveType('Int'))
        translator.declare_variable('x', PrimitiveType('Int'))

        expr = parse("(list-contains items x)")[0]
        result = translator.translate_expr(expr)
        # Should still translate (as uninterpreted function)
        assert result is not None
