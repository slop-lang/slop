"""Hole filler against the 0.4.0 language: forms, union constructors, prompts.

The validator's job is to turn away a fill the compiler would reject before
spending a checker run on it, and to pass every fill the compiler accepts.
These tests pin both directions for the forms that drifted: union
constructors, list/set literals, and the map/put/try forms that never
compiled.
"""
import pytest

from slop import paths
from slop.parser import parse, Symbol, SList
from slop.hole_filler import (
    VALID_EXPRESSION_FORMS, Hole, HoleFiller, build_prompt,
    _extract_function_calls, _extract_referenced_types, _extract_type_defs,
    _extract_param_names, _params_for_checker,
)
from slop.providers import MockProvider, ModelConfig, Tier

needs_native = pytest.mark.skipif(
    not (paths.find_native_binary('parser') and paths.find_native_binary('compiler')),
    reason="native toolchain not built (make install)")


SHAPE_CONTEXT = {
    'type_defs': [
        '(type Shape (union (dot) (circle Int) (rect Int Int)))',
        '(type Color (enum red green))',
        '(type Pt (record (x Int) (y Int)))',
    ],
    'params': '((arena Arena) (mut n Int))',
    'fn_name': 'make-shape',
}

UNION_TAGS = {'Shape': {'dot', 'circle', 'rect'}}


def expr(src):
    return parse(src)[0]


def calls(src, union_tags=None):
    return _extract_function_calls(expr(src), union_tags)


def make_filler():
    return HoleFiller({Tier.TIER_1: ModelConfig('mock', 'test')}, MockProvider())


def validate(src, type_src, context=SHAPE_CONTEXT):
    hole = Hole(type_expr=expr(type_src), prompt="fill it")
    return make_filler()._validate(expr(src), hole, context)


class TestValidExpressionForms:
    """The form table matches what the 0.4.0 toolchain compiles."""

    @pytest.mark.parametrize("form", ['set', 'list', 'union-new', 'record-new', 'when',
                                      'sizeof', 'addr', 'fn', '?', 'is-some', 'is-none',
                                      'list-set', '&', '|', '^', '<<', '>>'])
    def test_implemented_forms_present(self, form):
        assert form in VALID_EXPRESSION_FORMS

    @pytest.mark.parametrize("form", ['map', 'put', 'try', 'array', 'let*',
                                      'is-ok', 'is-error', 'string-slice', 'string-split',
                                      'bit-and', 'bit-or', 'bit-xor', 'bit-not'])
    def test_unimplemented_forms_absent(self, form):
        assert form not in VALID_EXPRESSION_FORMS


class TestExtractFunctionCalls:
    """Binding names, types and tags are not reported as calls."""

    def test_union_type_constructor_tag_not_a_call(self):
        assert calls('(Shape (circle (+ n 1)))', UNION_TAGS) == {'Shape', '+'}

    def test_union_tag_without_union_info_is_a_call(self):
        # Nothing says circle is a tag, so it is reported like any call
        assert 'circle' in calls('(Shape (circle 3))')

    def test_union_new_skips_type_and_tag(self):
        assert calls('(union-new Shape rect (f 1) 2)') == {'union-new', 'f'}

    def test_bare_tag_call_is_a_call(self):
        assert calls('(circle 3)', UNION_TAGS) == {'circle'}

    def test_arena_keyword_not_flagged(self):
        assert calls('(list-push xs v :arena a)') == {'list-push'}
        assert calls('(list Int 1 2 :arena a)') == {'list'}
        assert calls('(set Int 1 2 :arena (pick-arena))') == {'set', 'pick-arena'}

    def test_mut_let_binding(self):
        # Binding names and the mut marker are skipped; the value is scanned
        found = calls('(let ((mut x (Option Int) (lookup k)) (y 2) (mut z 0)) (use x))')
        assert found == {'let', 'lookup', 'use'}

    def test_typed_let_binding_type_not_scanned(self):
        assert calls('(let ((x (Ptr Thing) (make))) x)') == {'let', 'make'}

    def test_for_each_binders_skipped(self):
        assert calls('(for-each (item items) (process item))') == {'for-each', 'process'}
        assert calls('(for-each ((k v) m) (put-it k v))') == {'for-each', 'put-it'}

    def test_match_patterns_skipped(self):
        found = calls('(match s ((circle r) (area r)) ((rect w h) (* w h)) ((dot) 0))')
        assert found == {'match', 'area', '*'}

    def test_lambda_params_skipped(self):
        assert calls('(fn ((x Int) (y (Ptr T))) (+ x y))') == {'fn', '+'}

    def test_type_operands_skipped(self):
        assert calls('(cast (Ptr User) (arena-alloc arena (sizeof User)))') == \
            {'cast', 'arena-alloc', 'sizeof'}
        assert calls('(map-new arena String (List Int))') == {'map-new'}

    def test_let_bound_lambda_call(self):
        # The call to f is reported; _validate allows it as a local callable
        assert 'f' in calls('(let ((f (fn ((x Int)) x))) (f 2))')


@needs_native
class TestValidateForms:
    """_validate accepts what compiles and rejects what does not."""

    @pytest.mark.parametrize("src", ['(Shape (circle n))', '(Shape (rect n 2))',
                                     '(union-new Shape circle n)', '(union-new Shape rect n 2)',
                                     '(Shape dot)', '(Shape (dot))'])
    def test_union_constructors_validate(self, src):
        ok, err = validate(src, 'Shape')
        assert ok, err

    def test_bare_union_tag_rejected_with_hint(self):
        ok, err = validate('(circle n)', 'Shape')
        assert not ok
        assert "(Shape (circle ...))" in err

    def test_enum_value_called_rejected_with_hint(self):
        ok, err = validate('(red)', 'Color')
        assert not ok
        assert "write 'red" in err

    def test_quoted_enum_value_validates(self):
        ok, err = validate("'red", 'Color')
        assert ok, err

    def test_positional_record_constructor_validates(self):
        ok, err = validate('(Pt n 2)', 'Pt')
        assert ok, err

    def test_set_literal_validates(self):
        ok, err = validate('(set Int 1 2)', '(Set Int)')
        assert ok, err

    def test_list_literal_with_arena_option_validates(self):
        ok, err = validate('(list Int 1 2 :arena arena)', '(List Int)')
        assert ok, err

    @pytest.mark.parametrize("src,name", [('(map Int Int)', 'map'),
                                          ('(put p x 1)', 'put'),
                                          ('(try n (catch e 0))', 'try')])
    def test_noncompiling_forms_rejected_as_undefined(self, src, name):
        ok, err = validate(src, 'Int')
        assert not ok
        undefined = err.split("Undefined function(s): ")[1].split(".")[0]
        assert name in undefined.split(", ")

    def test_mode_param_in_scope(self):
        # (mut n Int) binds n, not a variable named mut of type n
        ok, err = validate('(+ n 1)', 'Int')
        assert ok, err

    def test_lambda_fill_is_not_a_definition(self):
        ok, err = validate('(let ((f (fn ((x Int)) (+ x 1)))) (f n))', 'Int')
        assert ok, err

    def test_named_fn_is_a_definition(self):
        ok, err = validate('(fn helper ((x Int)) x)', 'Int')
        assert not ok
        assert "Do not return a 'fn' form" in err


@needs_native
class TestTypeContext:
    def test_union_and_enum_definitions_read(self):
        info = _extract_type_defs(SHAPE_CONTEXT)
        assert info.unions['Shape'] == [('dot', []), ('circle', ['Int']), ('rect', ['Int', 'Int'])]
        assert info.enums == {'Color': ['red', 'green']}
        assert info.records == {'Pt': ['x', 'y']}
        assert info.constructors == {'Shape', 'Pt'}

    def test_param_names_with_modes(self):
        assert _extract_param_names('((in a Int) (mut b (List Int)) (c String))') == ['a', 'b', 'c']

    def test_params_for_checker_drops_modes(self):
        assert _params_for_checker('((in a Int) (mut b (List Int)) (c String))') == \
            '((a Int) (b (List Int)) (c String))'


@needs_native
class TestReferencedTypes:
    CONTEXT = {
        'type_defs': [
            '(type User (record (name String)))',
            '(type UserId (Int 1 ..))',
            '(type user-role (enum admin guest))',
        ],
    }

    def test_mode_params(self):
        context = dict(self.CONTEXT, params='((mut u User) (in role user-role))')
        hole = Hole(type_expr=Symbol('Int'), prompt='p', context=['u', 'role'])
        assert _extract_referenced_types(hole, context) == {'User', 'user-role'}

    def test_user_does_not_match_userid(self):
        hole = Hole(type_expr=expr('(Option UserId)'), prompt='p', context=['x'])
        assert _extract_referenced_types(hole, self.CONTEXT) == {'UserId'}

    def test_signature_token_match(self):
        context = dict(self.CONTEXT, fn_specs=[
            {'name': 'find-id', 'params': '((name String))', 'return_type': '(Option UserId)'}])
        hole = Hole(type_expr=Symbol('Int'), prompt='p', context=['find-id'])
        assert _extract_referenced_types(hole, context) == {'UserId'}


@needs_native
class TestPrompt:
    def test_unit_result_example(self):
        prompt = build_prompt(Hole(type_expr=Symbol('Int'), prompt='p'), SHAPE_CONTEXT)
        assert '(ok unit)' in prompt
        assert '(ok ())' not in prompt

    def test_union_guidance(self):
        prompt = build_prompt(Hole(type_expr=Symbol('Shape'), prompt='p'), SHAPE_CONTEXT)
        assert '## Union Variants' in prompt
        assert '(union-new Type tag v ...)' in prompt
        assert '(Shape (circle <Int>))' in prompt
        assert 'Shape: dot, (circle Int), (rect Int Int)' in prompt

    def test_enum_guidance_is_quoted_only(self):
        prompt = build_prompt(Hole(type_expr=Symbol('Color'), prompt='p'), SHAPE_CONTEXT)
        assert "Color: 'red, 'green" in prompt
        assert '(literal "pets")' not in prompt

    def test_no_map_literal_guidance(self):
        prompt = build_prompt(Hole(type_expr=Symbol('Int'), prompt='p'), SHAPE_CONTEXT)
        assert 'NO map literal' in prompt


class TestMockProvider:
    """MockProvider answers from the hole, not from the spec embedded around it."""

    def hole_prompt(self, description, type_src):
        # The shape of build_prompt's output, with spec text that mentions
        # hash, add and sum ahead of the hole section
        return ("You are filling a typed hole in SLOP code.\n\n"
                "(fn hash-password ...) add sum withdraw balance adult\n\n"
                "## Hole to Fill\n"
                f"Type: {type_src}\n"
                f"Description: {description}\n\n"
                "## Constraints\n- none\n\n"
                "Respond with ONLY the SLOP S-expression. No explanation.")

    def complete(self, prompt):
        return MockProvider().complete(prompt, ModelConfig('mock', 'mock'))

    def test_spec_text_does_not_drive_response(self):
        response = self.complete(self.hole_prompt("Count the items", "Int"))
        assert response == "0"

    @pytest.mark.parametrize("type_src,expected", [
        ("Bool", "false"),
        ("String", '""'),
        ("(Int 1 ..)", "1"),
        ("(Option Int)", "(none)"),
        ("(Result Unit ApiError)", "(ok unit)"),
        ("(Result Int String)", "(ok 0)"),
    ])
    def test_type_directed_default(self, type_src, expected):
        assert self.complete(self.hole_prompt("Do the thing", type_src)) == expected

    def test_withdraw_uses_set_not_put(self):
        response = self.complete(self.hole_prompt("Withdraw from the balance", "(Result (Ptr Account) Error)"))
        assert "(put " not in response
        assert "(set! account balance" in response

    def test_no_invented_functions(self):
        for description in ["Hash the password", "Something else entirely"]:
            response = self.complete(self.hole_prompt(description, "Int"))
            assert "crypto-hash-password" not in response
            assert "nil" not in response
