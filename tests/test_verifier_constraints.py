"""Side facts reach every solver; definedness is checked at its program point."""

import pytest

pytest.importorskip('z3')

from slop.verifier import verify_source


def verify(source, **kwargs):
    return verify_source(source, **kwargs)[-1]


@pytest.mark.parametrize('contract', ['(@post (!= n 0))', '(@post true)'])
def test_body_divisor_is_an_obligation(contract):
    result = verify(f'''(fn f ((n Int))
      (@spec ((Int) -> Int)) {contract} (/ 1 n))''')
    assert result.status == 'failed'
    assert 'definedness' in result.message
    assert result.counterexample['n'] == '0'


@pytest.mark.parametrize('body', [
    '(if (!= n 0) (/ 1 n) 0)',
    '(do (when (== n 0) (return 0)) (/ 1 n))',
    '(if (and (!= n 0) (> (/ 1 n) 0)) 1 0)',
])
def test_a_division_only_has_to_be_defined_where_it_runs(body):
    assert verify(f'''(fn f ((n Int))
      (@spec ((Int) -> Int)) (@post true) {body})''').status == 'verified'


@pytest.mark.parametrize('operator', ['/', '%'])
def test_precondition_establishes_definedness(operator):
    assert verify(f'''(fn f ((n Int))
      (@spec ((Int) -> Int)) (@pre (!= n 0))
      (@post true) ({operator} 7 n))''').status == 'verified'


def test_a_later_loop_exit_cannot_justify_an_earlier_division():
    result = verify('''(fn f ((n Int))
      (@spec ((Int) -> Int)) (@post true)
      (do (/ 1 n) (while (== n 0) (set! n 1)) n))''')
    assert result.status == 'failed'
    assert result.counterexample['n'] == '0'


def test_a_later_cast_cannot_justify_an_earlier_division():
    result = verify('''(module m
      (type Positive (Int 1 .. 100))
      (fn f ((n Int)) (@spec ((Int) -> Int)) (@post true)
        (do (/ 1 n) (cast Positive n))))''')
    assert result.status == 'failed'


def test_trusted_assumption_can_establish_definedness():
    assert verify('''(fn f ((n Int))
      (@spec ((Int) -> Int)) (@assume (!= n 0))
      (@post true) (/ 1 n))''').status == 'verified'


def test_assumption_side_condition_keeps_its_short_circuit_guard():
    result = verify('''(fn f ((n Int)) (@spec ((Int) -> Int))
      (@assume (or (== n 0) (== (/ 1 n) 1)))
      (@post true) (/ 1 n))''')
    assert result.status == 'failed'
    assert result.counterexample['n'] == '0'


def test_loop_invariant_can_establish_definedness():
    assert verify('''(fn f ((n Int))
      (@spec ((Int) -> Int)) (@pre (> n 0)) (@post true)
      (let ((mut i 0))
        (while (< i 3) (@loop-invariant (> n 0))
          (/ 1 n) (set! i (+ i 1))) 0))''').status == 'verified'


def test_division_after_break_is_not_a_concrete_failure():
    result = verify('''(fn f ((n Int))
      (@spec ((Int) -> Int)) (@post true)
      (do (while true (break) (/ 1 n)) 0))''')
    assert result.status == 'unknown'


def test_unmodelled_scope_cannot_drop_a_body_obligation():
    assert verify('''(fn f ((n Int))
      (@spec ((Int) -> Int)) (@post true)
      (with-arena 1024 (/ 1 n)))''').status == 'unknown'


def test_quoted_division_is_data():
    assert verify('''(fn f () (@spec (() -> Int)) (@post true)
      (do (quote (/ 1 0)) 7))''').status == 'verified'


def test_called_closure_with_a_division_is_unknown():
    assert verify('''(fn f ((n Int)) (@spec ((Int) -> Int)) (@post true)
      (let ((g (fn ((x Int)) (/ 1 x)))) (g n)))''').status == 'unknown'


def test_uncalled_closure_does_not_execute_its_division():
    assert verify('''(fn f ((n Int)) (@spec ((Int) -> Int)) (@post true)
      (let ((g (fn ((x Int)) (/ 1 x)))) 7))''').status == 'verified'


def test_called_closure_retains_captured_callable_obligations():
    assert verify('''(fn f ((n Int)) (@spec ((Int) -> Int)) (@post true)
      (let ((h (fn ((x Int)) (/ 1 x))) (g (fn () (h n))))
        (g)))''').status == 'unknown'


def test_precondition_definedness_is_part_of_legal_input():
    assert verify('''(fn f ((n Int)) (@spec ((Int) -> Int))
      (@pre (== (/ 1 n) 1)) (@post true) (/ 1 n))''').status == 'verified'


def test_input_invariant_definedness_is_part_of_legal_input():
    assert verify('''(module m
      (type R (record (n Int)) (@invariant (== (/ 1 n) 1)))
      (fn f ((r R)) (@spec ((R) -> Int)) (@post true)
        (/ 1 (. r n))))''').status == 'verified'


@pytest.mark.parametrize('divisor', [
    '(cast (Int 1 .. 100) n)', '(positive n)',
])
def test_an_unfollowed_divisor_is_not_a_concrete_counterexample(divisor):
    result = verify(f'''(module m
      (fn positive ((x Int)) (@spec ((Int) -> Int)) (@pure)
        (@post (> $result 0)) 1)
      (fn f ((n Int)) (@spec ((Int) -> Int)) (@post true) (/ 1 {divisor})))''')
    assert result.status in ('verified', 'unknown')


@pytest.mark.parametrize('annotation', ['@post', '@property length'])
def test_late_string_literal_facts_reach_the_solver(annotation):
    assert verify(f'''(module m
      (type R (record (text String)) (@invariant (== text "é")))
      (fn f ((r R)) (@spec ((R) -> Int))
        ({annotation} (== (string-len (. r text)) 2))
        0))''').status == 'verified'


def test_late_literal_fact_agrees_with_record_string_length():
    assert verify('''(module m
      (type R (record (text String)))
      (fn f () (@spec (() -> R))
        (@post (== (string-len (. $result text)) 2))
        (record-new R (text "é"))))''').status == 'verified'


def test_late_enum_field_bounds_reach_the_solver():
    assert verify('''(module m
      (type Color (enum red blue))
      (type Input (record (color Color)))
      (type Output (record (number Int)))
      (fn f ((input Input)) (@spec ((Input) -> Output))
        (@post (and (>= (. $result number) 0) (< (. $result number) 2)))
        (record-new Output (number (cast Int (. input color))))))''').status == 'verified'


def test_late_callee_range_bounds_reach_the_solver(tmp_path):
    (tmp_path / 'bounds.slop').write_text('''(module bounds (export bounded)
      (fn bounded ((x Int)) (@spec ((Int) -> (Int 1 .. 9)))
        (if (< x 1) 1 (if (> x 9) 9 x))))''')
    assert verify('''(module m
      (import bounds (bounded))
      (type R (record (n Int)))
      (fn f ((x Int)) (@spec ((Int) -> R))
        (@post (and (>= (. $result n) 1) (<= (. $result n) 9)))
        (record-new R (n (bounded x)))))''',
        filename=str(tmp_path / 'main.slop')).status == 'verified'


def test_late_tail_fact_does_not_constrain_an_early_result():
    result = verify('''(module m
      (type R (record (text String)))
      (fn f ((flag Bool) (old R)) (@spec ((Bool R) -> R))
        (@post (== (string-len (. $result text)) 2))
        (when flag (return old))
        (record-new R (text "é"))))''')
    assert result.status != 'verified'
