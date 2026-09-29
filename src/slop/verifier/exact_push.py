"""Exact model of a loop-free, push-built result (#170).

A body shaped

    (let ((mut r (list-new arena T)))
      ... list-push r e ... inside do / let / when / if / cond / match ...
      r)

with no loop anywhere denotes a list whose contents are a function of the
branch conditions alone: every push either happens or does not, once, in
program order. This mixin walks such a body and computes that list as a Z3
sequence - `If(g, Concat(s, Unit(e)), s)` at each push - and the verifier
asserts `$result`'s sequence equal to it. A contract quantifying over the
result, `(forall (m $result) ...)`, `(exists (m $result) ...)` or
`(list-contains $result x)`, can then be proved or refuted rather than
reported unknown.

The whole analysis is an all-or-nothing gate. Anything the walker does not
model exactly - a loop, an early return, a call made for its effect, a push
the walk did not visit, a term it cannot translate - abandons the model, and
the function is verified exactly as it was before this existed. Guessing would
be worse than unknown: a model that is wrong in the permissive direction lets
a false contract verify.
"""

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

import z3

from slop.parser import SList, Symbol, is_form
from slop.types import (
    PrimitiveType, RangeType, EnumType, RecordType, UnionType, OptionType, ResultType,
)

_MISSING = object()

# Forms that make the list's contents depend on more than branch conditions,
# or that this walker does not follow. Their presence anywhere abandons the
# model. Mutators of other collections are here too: a guard like
# `(set-has s x)` is an uninterpreted function of `s`, which is only sound if
# nothing in the body changes `s` between two readings.
_FORBIDDEN_FORMS = (
    'while', 'for-each', 'for', 'loop', 'return', 'break', 'continue',
    'fn', 'lambda', 'spawn', 'c-inline', 'try', '?',
    'list-set', 'list-pop', 'list-clear', 'list-remove', 'list-insert',
    'set-put', 'set-remove', 'set-clear', 'map-put', 'map-remove', 'map-clear',
    'deref', 'with-arena', 'arena-free',
    '/', '%', 'mod', 'div',
)

# Builtins that read a collection's current state. Sound to treat as
# uninterpreted functions only while nothing mutates that state - guaranteed
# for the body itself by _FORBIDDEN_FORMS, and for callees by requiring every
# user function the body calls to be @pure whenever one of these appears.
_STATE_READS = frozenset((
    'set-has', 'map-has', 'map-get', 'list-len', 'list-get',
    'set-elements', 'map-keys', 'map-len', 'set-len',
))

# Heads that are syntax or builtins which mutate nothing. Any other head is a
# call to a function; one not declared @pure is taken to mutate what it can reach.
_NEUTRAL_HEADS = frozenset((
    'let', 'do', 'when', 'if', 'cond', 'match', 'set!', 'list-push', 'list-new', 'mut',
    'record-new', 'union-new', 'some', 'none', 'ok', 'error', 'quote', 'cast', '.',
    '+', '-', '*', '==', '!=', '<', '>', '<=', '>=', 'and', 'or', 'not', 'min', 'max',
    'string-eq', 'string-len',
)) | _STATE_READS

# Forms that are statements, never terms.
_STATEMENT_FORMS = frozenset(('let', 'do', 'when', 'match', 'set!', 'list-push', 'list-new'))

_OPTION_RESULT_CONSTRUCTORS = frozenset(('some', 'none', 'ok', 'error'))

_MAX_PUSHES = 32
_MAX_BRANCHES = 64


class _Bail(Exception):
    """The body is not one this walker models exactly."""


@dataclass
class ExactPushModel:
    result_name: str
    seq: Any                    # z3 SeqRef
    axioms: List[Any]           # z3 BoolRefs: constructor fields, callee posts, side conditions
    push_count: int


@dataclass
class _State:
    env: Dict[str, Any]         # walker-bound name -> z3 term
    seq: Any                    # the result list so far


class ExactPushModelMixin:
    """Walks a loop-free push-built body into an exact sequence (see module doc)."""

    # ------------------------------------------------------------------
    # Entry point
    # ------------------------------------------------------------------

    def _exact_push_model(self, body, translator) -> Optional[ExactPushModel]:
        """The exact model of `body`'s result, or None if the body does not qualify.

        None leaves the translator exactly as it was found: every variable,
        constraint and pin this adds is removed again.
        """
        result_name = self._exact_push_shape(body, translator)
        if result_name is None:
            return None

        saved_vars = dict(translator.variables)
        saved_constraints = len(translator.constraints)
        saved_flags = (translator._versions_frozen, translator._prefer_initial_versions,
                       translator._prefer_final_versions)
        # Names a `set!` replaced are frozen once the body is translated, and a
        # frozen name translates to nothing. The walker gives every name its
        # value at each program point itself, so the freeze does not apply here.
        translator._versions_frozen = False
        translator._prefer_initial_versions = False
        translator._prefer_final_versions = False
        translator._pinned_terms = {}

        self._xp_tr = translator
        self._xp_result = result_name
        self._xp_axioms: List[Any] = []
        self._xp_pushes = 0
        self._xp_branches = 0
        # Names the walker bound itself - let locals and match payloads - so a
        # `set!` can be told from one of a parameter.
        self._xp_bound: List[str] = []
        try:
            empty = z3.Empty(z3.SeqSort(z3.IntSort()))
            state = self._xp_stmt(body, _State({}, empty), z3.BoolVal(True))
            if self._xp_pushes != self._count_push_to_var([body], result_name):
                raise _Bail("a push the walk did not visit")
            return ExactPushModel(result_name, state.seq, self._xp_axioms, self._xp_pushes)
        except _Bail:
            return None
        finally:
            translator.variables.clear()
            translator.variables.update(saved_vars)
            self._xp_truncate_constraints(saved_constraints)
            (translator._versions_frozen, translator._prefer_initial_versions,
             translator._prefer_final_versions) = saved_flags
            translator._pinned_terms = {}

    def _xp_truncate_constraints(self, start: int) -> None:
        """Drop translator constraints from `start` on, with their definedness marks.

        definedness_constraints holds *indices* into the constraint list, so an
        index left behind after a truncation would mark whatever constraint is
        appended there next.
        """
        tr = self._xp_tr if hasattr(self, '_xp_tr') else None
        if tr is None:
            return
        del tr.constraints[start:]
        tr.definedness_constraints.difference_update(
            {i for i in tr.definedness_constraints if i >= start})

    # ------------------------------------------------------------------
    # The syntactic gate
    # ------------------------------------------------------------------

    def _exact_push_shape(self, body, translator) -> Optional[str]:
        """The result list's name if `body` has the qualifying shape, else None."""
        ret = self._get_return_expr(body)
        if not isinstance(ret, Symbol):
            return None
        name = ret.name
        init, _scope = self._binding_in_scope_at_tail(body, name)
        if not is_form(init, 'list-new'):
            return None
        if self._count_bindings_of(body, name) != 1:
            return None
        if self._contains_any_form(body, _FORBIDDEN_FORMS):
            return None
        # The list is only ever pushed to, bound, and returned. Anything else -
        # handing it to a call, aliasing it, reading its length in a guard -
        # is a use this walker does not model.
        if self._uses_outside(body, Symbol(name), self._xp_use_is_modelled):
            return None
        if self._calls_impure_and_reads_state(body, translator):
            return None
        if self._redefines_a_builtin_used_here(body, translator):
            return None
        return name

    _SPECIAL_HEADS = frozenset(('list-push', 'list-new', 'when', 'if', 'cond', 'match', 'let',
                                'do', 'set!', 'record-new', 'union-new', 'quote', 'cast', '.'))

    def _redefines_a_builtin_used_here(self, body, translator) -> bool:
        """True if the body uses a builtin or special form's name that the
        program also defines as a function.

        The walker and the translator read such a head as the builtin; which
        one the compiled program calls is the language's business (#110), and
        a model built on the wrong guess verifies false claims (Codex, fourth
        review: a user `list-push` that pushes nothing, a @pure user
        `string-len`). Refusing the body is the one answer right either way.
        """
        registry = translator.function_registry
        user = set(registry.functions) if registry is not None else set()
        user |= set(translator.imported_defs.functions)
        reserved = _NEUTRAL_HEADS | self._SPECIAL_HEADS

        def walk(node) -> bool:
            if isinstance(node, SList) and len(node) > 0:
                head = node[0]
                if isinstance(head, Symbol) and head.name in reserved and head.name in user:
                    return True
                return any(walk(item) for item in node.items)
            return False

        return walk(body)

    @staticmethod
    def _xp_use_is_modelled(parent_head, index, returns_value) -> bool:
        if parent_head == 'list-push' and index == 1:
            return True
        if parent_head == 'mut' and index == 1:
            return True
        return returns_value

    def _calls_impure_and_reads_state(self, body, translator) -> bool:
        """True if the body calls a non-@pure function and also reads state.

        A callee that is not @pure may mutate a collection it can reach, and a
        state read like `(set-has s x)` is an uninterpreted function of `s` -
        the same term before the call and after it. Refusing the combination
        is what keeps that reading sound. A head this cannot place - not a
        builtin, not a function it has the signature of - counts as impure.
        """
        heads = [call[0].name for call in self._xp_call_nodes(body)]
        reads_state = any(h in _STATE_READS and self._xp_is_builtin(h, translator) for h in heads)
        impure_call = any(not self._xp_callee_is_pure(h, translator) for h in heads)
        return reads_state and impure_call

    @staticmethod
    def _xp_evaluated_parts(node) -> List[Any]:
        """The sub-expressions a term form evaluates, read by its syntax.

        A record-new's `(to x)` is a field name and a value, not a call to `to`;
        a union-new's type and tag are names; `(. obj f)` evaluates only `obj`;
        a cond clause is a test and a result, and `else` is no call.
        """
        if not isinstance(node, SList) or len(node) == 0:
            return []
        head = node[0]
        if not isinstance(head, Symbol):
            return list(node.items)
        name = head.name
        if name == 'quote':
            return []
        if name == 'record-new':
            return [item[1] for item in node.items[2:] if isinstance(item, SList) and len(item) >= 2]
        if name == 'union-new':
            return list(node.items[3:])
        if name == '.':
            return [node[1]] if len(node) >= 2 else []
        if name == 'cast':
            return list(node.items[2:])
        if name == 'cond':
            parts = []
            for clause in node.items[1:]:
                if isinstance(clause, SList):
                    for i, item in enumerate(clause.items):
                        if i == 0 and isinstance(item, Symbol) and item.name == 'else':
                            continue
                        parts.append(item)
            return parts
        return list(node.items[1:])

    def _xp_call_nodes(self, expr) -> List[Any]:
        """Every call-shaped node under `expr`, reading each form by its syntax.

        A naive walk takes a let binding `(fire false)`, a match pattern
        `(sub-name b a)` or a record field `(to x)` for a call to `fire`,
        `sub-name` or `to` - and a user function of that name would then have
        its contract applied to the wrong thing.
        """
        out: List[Any] = []

        def walk(node):
            if not isinstance(node, SList) or len(node) == 0:
                return
            head = node[0]
            if not isinstance(head, Symbol):
                for item in node.items:
                    walk(item)
                return
            name = head.name
            if name == 'quote':
                return
            if name == 'let' and len(node) >= 2 and isinstance(node[1], SList):
                for binding in node[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        walk(binding[-1])
                for item in node.items[2:]:
                    walk(item)
                return
            if name == 'match' and len(node) >= 2:
                walk(node[1])
                for clause in node.items[2:]:
                    if isinstance(clause, SList):
                        for item in clause.items[1:]:
                            walk(item)
                return
            if name == 'cond':
                for clause in node.items[1:]:
                    if isinstance(clause, SList):
                        for item in clause.items:
                            walk(item)
                return
            if name == 'record-new':
                for item in node.items[2:]:
                    if isinstance(item, SList) and len(item) >= 2:
                        walk(item[1])
                return
            if name == 'union-new':
                for item in node.items[3:]:
                    walk(item)
                return
            if name == '.':
                if len(node) >= 2:
                    walk(node[1])
                return
            out.append(node)
            for item in node.items[1:]:
                walk(item)

        walk(expr)
        return out

    @staticmethod
    def _xp_is_builtin(name: str, translator) -> bool:
        """A head on the neutral list that no user function redefines."""
        if name not in _NEUTRAL_HEADS:
            return False
        registry = translator.function_registry
        if registry is not None and name in registry.functions:
            return False
        return name not in translator.imported_defs.functions

    @staticmethod
    def _xp_callee_is_pure(name: str, translator) -> bool:
        """True for a neutral builtin or a function declared @pure; False otherwise.

        A head this knows nothing about is NOT pure. Taking an unlisted builtin
        for one made two `(arena-new 32)` calls a single value (Codex, second
        review): allocations, clocks and random sources must not collapse.
        """
        # A user definition wins over the builtin list: a module may define its
        # own function under a builtin's name (Codex, third review of #170).
        registry = translator.function_registry
        if registry is not None and name in registry.functions:
            return registry.functions[name].is_pure
        imported = translator.imported_defs.functions.get(name)
        if imported is not None:
            return getattr(imported, 'is_pure', False)
        return name in _NEUTRAL_HEADS

    # ------------------------------------------------------------------
    # Statements
    # ------------------------------------------------------------------

    def _xp_stmt(self, stmt, st: _State, pc) -> _State:
        if not isinstance(stmt, SList):
            return st           # a symbol or literal in statement position does nothing
        if len(stmt) == 0:
            return st
        head = stmt[0]
        name = head.name if isinstance(head, Symbol) else None

        if name == 'do':
            for item in stmt.items[1:]:
                st = self._xp_stmt(item, st, pc)
            return st
        if name == 'let':
            return self._xp_let(stmt, st, pc)
        if name == 'when':
            if len(stmt) < 2:
                raise _Bail("malformed when")
            guard = self._xp_guard(stmt[1], st, pc)
            taken = st
            for item in stmt.items[2:]:
                taken = self._xp_stmt(item, taken, z3.And(pc, guard))
            return self._xp_merge(guard, taken, st)
        if name == 'if':
            if len(stmt) < 3:
                raise _Bail("malformed if")
            guard = self._xp_guard(stmt[1], st, pc)
            then_st = self._xp_stmt(stmt[2], st, z3.And(pc, guard))
            else_st = (self._xp_stmt(stmt[3], st, z3.And(pc, z3.Not(guard)))
                       if len(stmt) >= 4 else st)
            return self._xp_merge(guard, then_st, else_st)
        if name == 'cond':
            return self._xp_cond(stmt, st, pc)
        if name == 'match':
            return self._xp_match(stmt, st, pc)
        if name == 'set!':
            return self._xp_set(stmt, st, pc)
        if name == 'list-push':
            return self._xp_push(stmt, st, pc)
        # Any other call in statement position is made for its effect, which
        # this walker does not model.
        raise _Bail(f"statement {name!r}")

    def _xp_let(self, stmt, st: _State, pc) -> _State:
        if len(stmt) < 2 or not isinstance(stmt[1], SList):
            raise _Bail("malformed let")
        env = dict(st.env)
        seq = st.seq
        introduced: List[str] = []
        for binding in stmt[1].items:
            if not isinstance(binding, SList) or len(binding) < 2:
                raise _Bail("malformed binding")
            bname = self._binding_name(binding)
            if bname is None:
                raise _Bail("unnamed binding")
            init = binding[-1]
            if bname == self._xp_result:
                if not is_form(init, 'list-new'):
                    raise _Bail("result bound to something other than list-new")
                seq = z3.Empty(z3.SeqSort(z3.IntSort()))
                continue
            # let* semantics: each initializer sees the bindings before it.
            env[bname] = self._xp_term(init, env, pc)
            introduced.append(bname)
            self._xp_bound.append(bname)
        inner = _State(env, seq)
        for item in stmt.items[2:]:
            inner = self._xp_stmt(item, inner, pc)
        # The let's own names go out of scope; a `set!` it made to an outer
        # local survives.
        out_env = dict(inner.env)
        for bname in introduced:
            if bname in st.env:
                out_env[bname] = st.env[bname]
            else:
                out_env.pop(bname, None)
        # An outer name the let shadowed keeps its outer value; one it did not
        # shadow but assigned through keeps the assignment.
        for bname, value in st.env.items():
            if bname not in introduced:
                out_env[bname] = inner.env.get(bname, value)
        return _State(out_env, inner.seq)

    def _xp_cond(self, stmt, st: _State, pc) -> _State:
        clauses = []
        earlier = []
        default = st
        for clause in stmt.items[1:]:
            if not isinstance(clause, SList) or len(clause) < 1:
                raise _Bail("malformed cond clause")
            test = clause[0]
            if isinstance(test, Symbol) and test.name == 'else':
                guard_pc = z3.And(pc, *[z3.Not(t) for t in earlier]) if earlier else pc
                default = st
                for item in clause.items[1:]:
                    default = self._xp_stmt(item, default, guard_pc)
                break
            term = self._xp_guard(test, st, pc)
            guard = z3.And(term, *[z3.Not(t) for t in earlier]) if earlier else term
            branch = st
            for item in clause.items[1:]:
                branch = self._xp_stmt(item, branch, z3.And(pc, guard))
            clauses.append((guard, branch))
            earlier.append(term)
        result = default
        for guard, branch in reversed(clauses):
            result = self._xp_merge(guard, branch, result)
        return result

    def _xp_match(self, stmt, st: _State, pc) -> _State:
        tr = self._xp_tr
        if len(stmt) < 3:
            raise _Bail("malformed match")
        scrutinee = self._xp_term(stmt[1], st.env, pc)
        is_enum = tr._is_enum_match(stmt)
        if is_enum:
            tag_term = scrutinee
        else:
            tag_func = tr.variables.get('union_tag')
            if not isinstance(tag_func, z3.FuncDeclRef):
                tag_func = z3.Function('union_tag', z3.IntSort(), z3.IntSort())
                tr.variables['union_tag'] = tag_func
            tag_term = tag_func(scrutinee)

        arms: List[Tuple[Any, _State]] = []
        tests: List[Any] = []
        seen_tags = set()
        clauses = stmt.items[2:]
        for position, clause in enumerate(clauses):
            if not isinstance(clause, SList) or len(clause) < 1:
                raise _Bail("malformed match arm")
            pattern = clause[0]
            body_items = clause.items[1:]
            if isinstance(pattern, Symbol) and pattern.name == '_':
                if position != len(clauses) - 1:
                    raise _Bail("wildcard arm is not last")
                guard = z3.And(*[z3.Not(t) for t in tests]) if tests else z3.BoolVal(True)
                arms.append((guard, self._xp_arm(body_items, st, st.env, z3.And(pc, guard))))
                continue
            tag, binders = self._xp_pattern(pattern)
            if tag in seen_tags:
                raise _Bail("duplicate match arm")
            seen_tags.add(tag)
            if tag not in tr.enum_values and f"'{tag}" not in tr.enum_values:
                # constructor_tag would fall back to a hash, which is neither
                # stable nor distinct from the real indexes.
                raise _Bail(f"unknown tag {tag!r}")
            test = tag_term == z3.IntVal(tr.constructor_tag(tag))
            arm_env = dict(st.env)
            for index, binder in enumerate(binders):
                if binder == '_':
                    continue
                if is_enum:
                    raise _Bail("enum arm with a payload")
                sort = tr.payload_sort(tag, index)
                if sort is None:
                    raise _Bail(f"payload {index} of {tag!r} has no known sort")
                arm_env[binder] = tr.union_payload_accessor(tag, index, sort)(scrutinee)
                self._xp_bound.append(binder)
            arms.append((test, self._xp_arm(body_items, st, arm_env, z3.And(pc, test), binders)))
            tests.append(test)

        # No arm matched: nothing happened. Folding from the last arm keeps the
        # first matching arm's effect, and the arms' tests are disjoint anyway.
        result = st
        for guard, arm_state in reversed(arms):
            result = self._xp_merge(guard, arm_state, result)
        return result

    def _xp_arm(self, body_items, st: _State, arm_env, pc, binders=()) -> _State:
        inner = _State(arm_env, st.seq)
        for item in body_items:
            inner = self._xp_stmt(item, inner, pc)
        # Payload names are the arm's own; outer names keep any assignment.
        out_env = {}
        for bname, value in st.env.items():
            out_env[bname] = value if bname in binders else inner.env.get(bname, value)
        return _State(out_env, inner.seq)

    @staticmethod
    def _xp_pattern(pattern) -> Tuple[str, List[str]]:
        """(tag, binder names) for a match pattern."""
        if isinstance(pattern, Symbol):
            return pattern.name.lstrip("'"), []
        if is_form(pattern, 'quote') and len(pattern) >= 2 and isinstance(pattern[1], Symbol):
            return pattern[1].name, []
        if isinstance(pattern, SList) and len(pattern) >= 1:
            head = pattern[0]
            if isinstance(head, Symbol):
                tag = head.name.lstrip("'")
            elif is_form(head, 'quote') and len(head) >= 2 and isinstance(head[1], Symbol):
                tag = head[1].name
            else:
                raise _Bail("unrecognised pattern")
            binders = []
            for binder in pattern.items[1:]:
                if not isinstance(binder, Symbol):
                    raise _Bail("nested pattern")
                binders.append(binder.name)
            return tag, binders
        raise _Bail("unrecognised pattern")

    def _xp_set(self, stmt, st: _State, pc) -> _State:
        if len(stmt) != 3 or not isinstance(stmt[1], Symbol):
            raise _Bail("set! of a non-name")
        target = stmt[1].name
        if target == self._xp_result or target not in st.env or target not in self._xp_bound:
            raise _Bail("set! of the result, a parameter or an unknown name")
        value = self._xp_term(stmt[2], st.env, pc)
        if value.sort() != st.env[target].sort():
            raise _Bail("set! changes a name's sort")
        env = dict(st.env)
        env[target] = value
        return _State(env, st.seq)

    def _xp_push(self, stmt, st: _State, pc) -> _State:
        if len(stmt) != 3 or not isinstance(stmt[1], Symbol) or stmt[1].name != self._xp_result:
            raise _Bail("push to a list other than the result")
        self._xp_pushes += 1
        if self._xp_pushes > _MAX_PUSHES:
            raise _Bail("too many pushes")
        element = self._xp_term(stmt[2], st.env, pc)
        if element.sort() != z3.IntSort():
            raise _Bail("element is not an Int-sorted term")
        return _State(st.env, z3.Concat(st.seq, z3.Unit(element)))

    def _xp_merge(self, guard, taken: _State, other: _State) -> _State:
        self._xp_branches += 1
        if self._xp_branches > _MAX_BRANCHES:
            raise _Bail("too many branches")
        if set(taken.env) != set(other.env):
            raise _Bail("branches disagree on the names in scope")
        env = {}
        for bname, a in taken.env.items():
            b = other.env[bname]
            if a.eq(b):
                env[bname] = a
            elif a.sort() != b.sort():
                raise _Bail("branches disagree on a name's sort")
            else:
                env[bname] = z3.If(guard, a, b)
        seq = taken.seq if taken.seq.eq(other.seq) else z3.If(guard, taken.seq, other.seq)
        return _State(env, seq)

    # ------------------------------------------------------------------
    # Terms
    # ------------------------------------------------------------------

    def _xp_guard(self, expr, st: _State, pc):
        term = self._xp_term(expr, st.env, pc)
        if term.sort() != z3.BoolSort():
            # A fresh Bool would be sound, but it turns a claim this could
            # decide into a spurious failure. Unknown is the honest answer.
            raise _Bail("guard is not Bool")
        return term

    def _xp_term(self, expr, env: Dict[str, Any], pc):
        """Translate a pure term under the walker's bindings and path condition."""
        self._xp_check_pure(expr)
        tr = self._xp_tr
        saved = {}
        for bname, value in env.items():
            saved[bname] = tr.variables.get(bname, _MISSING)
            tr.variables[bname] = value
        start = len(tr.constraints)
        try:
            self._xp_pin(expr, pc)
            term = tr.translate_expr(expr)
            if term is None:
                raise _Bail("term does not translate")
            self._xp_instantiate_calls(expr, pc)
        finally:
            # Side conditions raised while translating - a range bound on a
            # call's result, say - hold where the term is evaluated, which is
            # under this path condition. Constraints the translator appends this
            # late reach no solver on their own. A DEFINEDNESS condition is an
            # obligation, not a fact: assuming a divisor is nonzero because a
            # division appears would be assuming the program is safe.
            for index in range(start, len(tr.constraints)):
                if index not in tr.definedness_constraints:
                    self._xp_axioms.append(z3.Implies(pc, tr.constraints[index]))
            self._xp_truncate_constraints(start)
            for bname, previous in saved.items():
                if previous is _MISSING:
                    tr.variables.pop(bname, None)
                else:
                    tr.variables[bname] = previous
        return term

    def _xp_check_pure(self, expr):
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                if head.name in _STATEMENT_FORMS:
                    raise _Bail(f"{head.name} in a term")
                if head.name == 'quote':
                    return
            for item in expr.items:
                self._xp_check_pure(item)

    def _xp_pin(self, expr, pc):
        """Give each constructor in `expr` a fresh constant carrying its fields.

        Bottom-up, so an outer record's field axiom reads the inner constructor's
        pinned constant. Translating the constructor again returns the same
        constant - which is what makes the element stored in the sequence the
        one the axioms describe.
        """
        tr = self._xp_tr
        if not isinstance(expr, SList) or len(expr) == 0:
            return
        head = expr[0]
        for item in self._xp_evaluated_parts(expr):
            self._xp_pin(item, pc)
        if not isinstance(head, Symbol) or head.name in ('quote', 'cond', 'if', 'cast', '.'):
            return
        if head.name == 'record-new':
            for item in expr.items[2:]:
                if isinstance(item, SList) and len(item) >= 2 and tr.translate_expr(item[1]) is None:
                    raise _Bail("a record field does not translate")
            const = z3.FreshConst(z3.IntSort(), 'record')
            self._xp_axioms.extend(self._extract_record_field_axioms(
                expr, tr, base_accessor=const, path_cond=pc, bindings={}))
            tr._pinned_terms[id(expr)] = const
        elif head.name == 'union-new':
            if len(expr) < 3 or not isinstance(expr[2], Symbol):
                raise _Bail("malformed union-new")
            self._xp_pin_variant(expr, expr[2].name, expr.items[3:], pc)
        elif head.name in _OPTION_RESULT_CONSTRUCTORS:
            self._xp_pin_variant(expr, head.name, expr.items[1:], pc)
        elif not self._xp_is_builtin(head.name, tr):
            self._xp_pin_call(expr, head.name)

    def _xp_pin_call(self, call, fn_name: str):
        """Decide how a call is modelled, pinning it where the default is wrong.

        A @pure callee is an uninterpreted function: the same arguments give
        the same term, which is what purity means. Any other callee may return
        something different each time - two calls to a counter must not be one
        value - so its call gets a fresh constant of its own, and its contract
        is instantiated on that constant. That is only sound if the call cannot
        change state the caller reads afterwards, so every parameter must be a
        plain value: no list, set, map or pointer anywhere inside it, and no
        mut or out mode. A callee this cannot see the signature of does not
        qualify.
        """
        tr = self._xp_tr
        if self._xp_callee_is_pure(fn_name, tr):
            return
        if not self._xp_params_are_values(fn_name):
            raise _Bail(f"call to {fn_name!r}, which may change state")
        natural = tr.translate_expr(call)
        if natural is None:
            raise _Bail(f"call to {fn_name!r} does not translate")
        tr._pinned_terms[id(call)] = z3.FreshConst(natural.sort(), 'call')

    def _xp_params_are_values(self, fn_name: str) -> bool:
        tr = self._xp_tr
        registry = tr.function_registry
        types: List[Any] = []
        modes: List[Optional[str]] = []
        if registry is not None and fn_name in registry.functions:
            from .type_builder import _parse_type_expr_simple
            fn_def = registry.functions[fn_name]
            if len(fn_def.param_type_exprs) != len(fn_def.params):
                return False
            for expr in fn_def.param_type_exprs:
                if expr is None:
                    return False
                types.append(_parse_type_expr_simple(expr, tr.type_env.type_registry))
            modes = list(fn_def.param_modes)
        elif fn_name in tr.imported_defs.functions:
            sig = tr.imported_defs.functions[fn_name]
            if len(sig.param_types) != len(sig.params):
                return False
            types = list(sig.param_types)
            modes = list(getattr(sig, 'param_modes', [])) or [None] * len(types)
        else:
            return False
        # A mut parameter is a local copy of a value type (#180): the callee
        # changing it never reaches the caller. `out` no longer compiles, but
        # a source written for an older slop may still say it.
        if any(mode == 'out' for mode in modes):
            return False
        return all(self._xp_is_value_type(t, set()) for t in types)

    def _xp_is_value_type(self, typ, seen) -> bool:
        """True if a value of `typ` reaches no mutable storage."""
        tr = self._xp_tr
        if isinstance(typ, PrimitiveType):
            if typ.name in ('Int', 'I8', 'I16', 'I32', 'I64', 'U8', 'U16', 'U32', 'U64',
                            'Float', 'F32', 'F64', 'Bool', 'String', 'Unit', 'Arena'):
                return True
            target = tr.type_env.type_registry.get(typ.name) or tr.imported_defs.types.get(typ.name)
            if target is None or target is typ:
                return False
            return self._xp_is_value_type(target, seen)
        if isinstance(typ, (RangeType, EnumType)):
            return True
        if id(typ) in seen:
            return True     # a recursive type is as mutable as its other parts
        seen = seen | {id(typ)}
        if isinstance(typ, RecordType):
            return all(self._xp_is_value_type(t, seen) for t in typ.fields.values())
        if isinstance(typ, UnionType):
            payloads = []
            for tag in typ.variants:
                recorded = typ.payload_types.get(tag)
                if recorded is None:
                    first = typ.variants[tag]
                    recorded = (first,) if first is not None else ()
                payloads.extend(recorded)
            return all(p is None or self._xp_is_value_type(p, seen) for p in payloads)
        if isinstance(typ, OptionType):
            return self._xp_is_value_type(typ.inner, seen)
        if isinstance(typ, ResultType):
            return all(self._xp_is_value_type(getattr(typ, f), seen)
                       for f in ('ok_type', 'err_type') if hasattr(typ, f))
        return False        # lists, maps, sets, pointers, channels, functions

    def _xp_pin_variant(self, node, tag: str, payloads, pc):
        tr = self._xp_tr
        if tag not in tr.enum_values and f"'{tag}" not in tr.enum_values:
            raise _Bail(f"unknown constructor {tag!r}")
        const = z3.FreshConst(z3.IntSort(), 'variant')
        tag_func = tr.variables.get('union_tag')
        if not isinstance(tag_func, z3.FuncDeclRef):
            tag_func = z3.Function('union_tag', z3.IntSort(), z3.IntSort())
            tr.variables['union_tag'] = tag_func
        self._xp_axioms.append(z3.Implies(pc, tag_func(const) == z3.IntVal(tr.constructor_tag(tag))))
        for index, payload in enumerate(payloads):
            value = tr.translate_expr(payload)
            sort = tr.payload_sort(tag, index)
            if value is None or sort is None or value.sort() != sort:
                # The accessor a contract's match reads is at the declared
                # sort; a payload that does not reach it at that sort would
                # leave the two describing different things.
                raise _Bail("a payload does not translate at its declared sort")
            accessor = tr.union_payload_accessor(tag, index, sort)
            self._xp_axioms.append(z3.Implies(pc, accessor(const) == value))
        tr._pinned_terms[id(node)] = const

    def _xp_instantiate_calls(self, expr, pc):
        """Each user call's postconditions, under this path condition and its @pre."""
        for call in self._xp_call_nodes(expr):
            if not self._xp_is_builtin(call[0].name, self._xp_tr):
                self._xp_callee_posts(call, call[0].name, pc)

    def _xp_callee_posts(self, call, fn_name: str, pc, keep_post=None):
        """Assume the callee's @post and @property of this call, under `pc` and its @pre.

        `keep_post(post)` may refuse a postcondition this caller cannot read
        soundly; every one is kept when it is None.
        """
        tr = self._xp_tr
        params = None
        posts: List[Any] = []
        pres: List[Any] = []
        registry = tr.function_registry
        # A @property holds of every call, with no precondition, so it is
        # assumed like a postcondition - under the same guard, which only
        # weakens it. A callee states a fact as a property when a @post would
        # also become a runtime check it cannot compile (#171).
        if registry is not None and fn_name in registry.functions:
            fn_def = registry.functions[fn_name]
            params, pres = fn_def.params, getattr(fn_def, 'preconditions', [])
            posts = list(fn_def.postconditions) + [expr for _, expr in fn_def.properties]
        elif fn_name in tr.imported_defs.functions:
            sig = tr.imported_defs.functions[fn_name]
            params, pres = sig.params, getattr(sig, 'preconditions', [])
            posts = list(sig.postconditions) + list(getattr(sig, 'properties', []))
        if not params or not posts or len(params) != len(call.items) - 1:
            return
        call_term = tr.translate_expr(call)
        if call_term is None:
            return
        param_map = {'$result': call_term}
        for param, arg in zip(params, call.items[1:]):
            arg_term = tr.translate_expr(arg)
            if arg_term is None:
                return
            param_map[param] = arg_term
        allowed = set(param_map)
        pre_terms = []
        for pre in pres:
            if not self._xp_closed_over(pre, allowed):
                return      # an assumption we cannot state: skip every post
            start = len(tr.constraints)
            term = tr._translate_with_substitution(pre, param_map)
            # What translating the callee's contract raised - a definedness
            # condition above all - is not ours to assume.
            self._xp_truncate_constraints(start)
            if term is None or term.sort() != z3.BoolSort():
                return
            pre_terms.append(term)
        guard = z3.And(pc, *pre_terms) if pre_terms else pc
        for post in posts:
            if not self._xp_closed_over(post, allowed):
                continue    # a post about something other than the call: not ours to assume
            if keep_post is not None and not keep_post(post):
                continue
            start = len(tr.constraints)
            term = tr._translate_with_substitution(post, param_map)
            self._xp_truncate_constraints(start)
            if term is None or term.sort() != z3.BoolSort():
                continue
            self._xp_axioms.append(z3.Implies(guard, term))

    def _xp_closed_over(self, expr, allowed) -> bool:
        """True if every free name in `expr` is in `allowed`.

        Function heads and field names are not free names. Anything else a
        callee's contract mentions - a global, another parameter's alias -
        would be read in the caller's scope, where it means something else.
        """
        tr = self._xp_tr

        def free(node, bound, position_is_field=False) -> bool:
            if isinstance(node, Symbol):
                n = node.name
                if position_is_field or n in bound or n in ('true', 'false', 'nil', '_'):
                    return True
                if n.startswith("'") or n in tr.enum_values:
                    return True
                return False
            if isinstance(node, SList) and len(node) > 0:
                head = node[0]
                if isinstance(head, Symbol) and head.name == 'quote':
                    return True
                if is_form(node, '.') and len(node) >= 3:
                    return free(node[1], bound) and all(free(i, bound, True) for i in node.items[2:])
                # Names a match arm or a quantifier binds are the contract's
                # own, not free names of the caller's.
                if is_form(node, 'match') and len(node) >= 2:
                    if not free(node[1], bound):
                        return False
                    for clause in node.items[2:]:
                        if not isinstance(clause, SList) or len(clause) < 1:
                            return False
                        pattern = clause[0]
                        binders = set()
                        if isinstance(pattern, SList):
                            binders = {p.name for p in pattern.items[1:] if isinstance(p, Symbol)}
                        if not all(free(item, bound | binders) for item in clause.items[1:]):
                            return False
                    return True
                if (isinstance(head, Symbol) and head.name in ('forall', 'exists')
                        and len(node) >= 3 and isinstance(node[1], SList) and len(node[1]) >= 1
                        and isinstance(node[1][0], Symbol)):
                    binding = node[1]
                    source_ok = True
                    if len(binding) >= 2 and not (isinstance(binding[1], Symbol) and binding[1].name[:1].isupper()):
                        source_ok = free(binding[1], bound)
                    return source_ok and all(free(i, bound | {binding[0].name}) for i in node.items[2:])
                items = node.items[1:] if isinstance(head, Symbol) else node.items
                return all(free(i, bound) for i in items)
            return True

        return free(expr, set(allowed))
