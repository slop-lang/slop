"""Checking explicit @loop-invariant annotations.

An invariant is a claim that holds every time the loop is about to run its
body, and so also where the loop ends. It used to be taken on trust: asserted
about the value each name was left with, never checked. An invariant that
restated a postcondition proved that postcondition from itself.

This mixin checks each one the usual way, by induction over the iterations:

- base case: it holds where the loop is entered, given the function's @pre and
  what the code before the loop did;
- inductive step: from an arbitrary iteration where it holds (and, for a
  `while`, the condition does), one run of the body leaves it holding.

The check walks the function forward, like the exact push model
(exact_push.py) it borrows its term handling from: every name has a term at
each program point, a list the function builds and never lets out of its hands
is an exact sequence (`If(g, Concat(s, Unit(e)), s)` at each push), and a
call's contract is assumed about a constant of the call's own.

What the walk cannot model it does not guess at. A value it could not follow
is *opaque*; a check that fails only through an opaque value, or that needs
something the walk gave up on, answers "could not check" - unknown - rather
than "failed", and the invariant is not assumed. Only a proved invariant is
used by the rest of the verifier, and only where the reasoning that proved it
still holds (see `_ip_assumable`).

State. The translator reads a collection as an uninterpreted function of the
handle that names it: `(list-len xs)` is one term before a call that pushes to
`xs` and after it. So a read of collection state - a length, a membership, a
quantifier over a list the function does not track, a field through a pointer,
a @pure call handed a collection - is only meaningful while nothing has
changed any collection since the function was entered. The walk keeps a
`dirty` note of the first thing that may have; after it, such a read in the
body is an opaque value and in an invariant makes the invariant uncheckable.
"""

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

import z3

from slop.parser import SList, Symbol, Number, String, is_form, pretty_print
from slop.types import (
    PrimitiveType, RangeType, RecordType, ListType,
)

from .exact_push import _Bail, _STATE_READS, _NEUTRAL_HEADS, _OPTION_RESULT_CONSTRUCTORS, _MISSING
from .translator import Z3Translator
from .type_builder import _parse_type_expr_simple

_LOOP_HEADS = ('for-each', 'while', 'for')

# Builtins that change a collection in place.
_MUTATORS = frozenset((
    'list-push', 'list-set', 'list-pop', 'list-clear', 'list-remove', 'list-insert',
    'set-put', 'set-remove', 'set-clear', 'map-put', 'map-remove', 'map-clear',
    'arena-free',
))

# Builtins that make a new, empty collection or arena: fresh, and they change
# nothing that already exists.
_ALLOCATORS = frozenset(('list-new', 'set-new', 'map-new', 'arena-new'))

# Reads of collection state, beyond the builtins exact_push lists: verifier
# predicates over a list's elements, and a raw dereference.
_EXTRA_STATE_READS = frozenset((
    'list-ref', 'list-contains', 'deref', 'all-triples-have-predicate',
    'all-elements-satisfy', 'any-element-satisfies',
))

# Forms the walk does not follow at all.
_UNMODELLED_FORMS = frozenset(('with-arena', 'spawn', 'try', '?', 'lambda', 'loop'))

_OPAQUE = 'opaque'


class _NoTranslation(_Bail):
    """A term the translator has no reading for."""


class _Unchecked(Exception):
    """An invariant cannot be checked; the argument says why."""


@dataclass
class InvariantOutcome:
    expr: Any                   # the invariant's condition
    loop: Any                   # the loop it belongs to
    status: str = 'pending'     # proved | failed | unknown | timeout
    message: str = ''
    counterexample: Optional[Dict[str, str]] = None
    assumable: bool = False     # proved, and still true where the main verifier would use it
    reads_state: bool = False   # reads collection state (see module doc)

    @property
    def text(self) -> str:
        return pretty_print(self.expr)


@dataclass
class InvariantReport:
    outcomes: List[InvariantOutcome] = field(default_factory=list)
    misplaced: List[Any] = field(default_factory=list)

    @property
    def failed(self) -> List[InvariantOutcome]:
        return [o for o in self.outcomes if o.status == 'failed']

    @property
    def unchecked(self) -> List[InvariantOutcome]:
        return [o for o in self.outcomes if o.status in ('unknown', 'timeout')]

    @property
    def assumable(self) -> List[InvariantOutcome]:
        return [o for o in self.outcomes if o.assumable]


@dataclass
class _IState:
    env: Dict[str, Any]         # name -> term
    types: Dict[str, Any]       # name -> static Type, or None
    seqs: Dict[str, Any]        # tracked list name -> its sequence
    alive: Any                  # Bool: no `return` has been taken
    dirty: Optional[str]        # the first thing that may have changed a collection

    def but(self, **changes) -> '_IState':
        values = dict(env=dict(self.env), types=dict(self.types), seqs=dict(self.seqs),
                      alive=self.alive, dirty=self.dirty)
        values.update(changes)
        return _IState(**values)


class InvariantProverMixin:
    """Checks explicit loop invariants (see module doc)."""

    # ------------------------------------------------------------------
    # Entry point
    # ------------------------------------------------------------------

    def _check_loop_invariants(self, params, preconditions, body, sites,
                               in_callbacks) -> InvariantReport:
        report = InvariantReport()
        self._ip_outcomes: Dict[int, InvariantOutcome] = {}
        self._ip_sites: Dict[int, List[Any]] = {}
        for loop, conditions in sites:
            self._ip_sites[id(loop)] = conditions
            for condition in conditions:
                outcome = InvariantOutcome(condition, loop)
                self._ip_outcomes[id(condition)] = outcome
                report.outcomes.append(outcome)
        for form in in_callbacks:
            report.outcomes.append(InvariantOutcome(
                form[1] if len(form) >= 2 else form, None, 'unknown',
                self._ip_unchecked_message(form[1] if len(form) >= 2 else form,
                                           "inside a callback the verifier does not follow")))
        if not self._ip_outcomes:
            return report

        tr = Z3Translator(self.type_env, self.filename, self.function_registry,
                          self.imported_defs, use_array_encoding=False, use_seq_encoding=True)
        tr.use_quantifier_patterns = False
        saved = {name: getattr(self, name, _MISSING)
                 for name in ('_xp_tr', '_xp_axioms', '_xp_bound')}
        self._xp_tr = tr
        self._xp_axioms: List[Any] = []
        self._xp_bound: List[str] = []
        self._ip_time_spent = False
        self._ip_loop_depth: Dict[int, int] = {}
        self._ip_depth = 0
        self._ip_consistent_upto = -1
        # Hypotheses of the iterations being walked - an invariant assumed at
        # the top of the body, the loop's condition, what is known of its
        # element - asserted only in checks made while that iteration is walked.
        self._ip_local: List[Any] = []
        try:
            env, types = self._ip_declare_parameters(tr, params)
            self._ip_params = set(env)
            self._ip_assigned = self._ip_assigned_names(body)
            self._ip_tracked = self._ip_tracked_lists(body, set(env))
            given = []
            for _, pre in preconditions:
                term = tr.translate_expr(pre)
                if term is None or not z3.is_bool(term):
                    self._ip_give_up(f"the precondition {pretty_print(pre)} does not translate")
                    return self._ip_finish(report, body)
                given.append(term)
            for _, inv in self._collect_parameter_invariants(params):
                term = tr.translate_expr(inv)
                if term is not None and z3.is_bool(term):
                    given.append(term)
            self._ip_context = ([c for i, c in enumerate(tr.constraints)
                                 if i not in tr.definedness_constraints]
                                + given + list(self._extract_record_field_range_axioms(tr)))
            state = _IState(env, types, {}, z3.BoolVal(True), None)
            try:
                self._ip_stmt(body, state, z3.BoolVal(True))
            except _Bail as bail:
                self._ip_give_up(str(bail))
            return self._ip_finish(report, body)
        finally:
            for name, value in saved.items():
                if value is _MISSING:
                    if hasattr(self, name):
                        delattr(self, name)
                else:
                    setattr(self, name, value)

    def _ip_finish(self, report: InvariantReport, body) -> InvariantReport:
        for outcome in report.outcomes:
            if outcome.status == 'pending':
                outcome.status = 'unknown'
                outcome.message = self._ip_unchecked_message(
                    outcome.expr, "the loop is not reached by the analysis")
        for outcome in report.outcomes:
            if outcome.status == 'proved' and outcome.loop is not None:
                outcome.assumable = self._ip_assumable(outcome, body)
        return report

    def _ip_give_up(self, reason: str) -> None:
        for outcome in self._ip_outcomes.values():
            if outcome.status == 'pending':
                outcome.status = 'unknown'
                outcome.message = self._ip_unchecked_message(outcome.expr, reason)

    @staticmethod
    def _ip_unchecked_message(expr, reason: str) -> str:
        return f"could not check loop invariant: {pretty_print(expr)} ({reason})"

    def _ip_declare_parameters(self, tr, params) -> Tuple[Dict[str, Any], Dict[str, Any]]:
        env: Dict[str, Any] = {}
        types: Dict[str, Any] = {}
        for param in params:
            if not (isinstance(param, SList) and len(param) >= 2):
                continue
            first = param[0]
            if isinstance(first, Symbol) and first.name in ('in', 'out', 'mut'):
                name = param[1].name if isinstance(param[1], Symbol) else None
                type_expr = param[2] if len(param) > 2 else None
            else:
                name = first.name if isinstance(first, Symbol) else None
                type_expr = param[1]
            if name is None or type_expr is None:
                continue
            typ = _parse_type_expr_simple(type_expr, self.type_env.type_registry)
            env[name] = tr.declare_variable(name, typ)
            types[name] = typ
        return env, types

    # ------------------------------------------------------------------
    # Syntactic facts about the body
    # ------------------------------------------------------------------

    def _ip_assigned_names(self, body) -> set:
        names = set()

        def walk(node):
            if not isinstance(node, SList) or len(node) == 0:
                return
            if is_form(node, 'quote'):
                return
            if is_form(node, 'set!') and len(node) >= 2 and isinstance(node[1], Symbol):
                names.add(node[1].name)
            for item in node.items:
                walk(item)

        walk(body)
        return names

    def _ip_tracked_lists(self, body, params: set) -> set:
        """Lists the walk can follow exactly: made here, used only in ways it models.

        A list is tracked when a single `let` binds it to `list-new` of an
        Int-sorted element type, nothing else binds its name, it is not a
        parameter's name, and every use is a push to it, its length, a loop
        over it that does not also push to it, a quantifier or membership test
        in an invariant, or the value the function returns. A list handed to a
        call, aliased or reassigned may change where the walk cannot see.
        """
        candidates = {}

        def find(node):
            if not isinstance(node, SList) or len(node) == 0:
                return
            if is_form(node, 'quote'):
                return
            if is_form(node, 'let') or is_form(node, 'let*'):
                if len(node) >= 2 and isinstance(node[1], SList):
                    for binding in node[1].items:
                        if isinstance(binding, SList) and len(binding) >= 2:
                            name = self._binding_name(binding)
                            init = binding[-1]
                            if name and is_form(init, 'list-new') and self._ip_int_elements(init):
                                candidates[name] = candidates.get(name, 0) + 1
            for item in node.items:
                find(item)

        find(body)
        tracked = set()
        for name, bindings in candidates.items():
            if bindings != 1 or name in params or self._count_bindings_of(body, name) != 1:
                continue
            if self._ip_uses_are_modelled(body, name):
                tracked.add(name)
        return tracked

    def _ip_int_elements(self, list_new) -> bool:
        if len(list_new) < 3:
            return False
        typ = _parse_type_expr_simple(list_new[-1], self.type_env.type_registry)
        if isinstance(typ, PrimitiveType) and typ.name in ('Bool', 'Float', 'F32', 'F64'):
            return False
        return True

    def _ip_uses_are_modelled(self, body, name: str) -> bool:
        ok = True

        def walk(node, parent, index, returns_value, loop_pushes):
            nonlocal ok
            if not ok:
                return
            if isinstance(node, Symbol):
                if node.name != name:
                    return
                if parent in ('list-push', 'list-len') and index == 1:
                    return
                if parent in ('mut', '@binding'):
                    return
                if parent == 'list-contains' and index == 1:
                    return
                if parent in ('@quantifier-source', '@for-each-source') and not loop_pushes:
                    return
                if returns_value:
                    return
                ok = False
                return
            if not isinstance(node, SList) or len(node) == 0:
                return
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head == 'quote':
                return
            if head in ('let', 'let*') and len(node) >= 2 and isinstance(node[1], SList):
                for binding in node[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        if self._binding_name(binding) == name:
                            walk(binding[-1], None, -1, False, loop_pushes)
                        else:
                            for item in binding.items[1:]:
                                walk(item, None, -1, False, loop_pushes)
                last = len(node) - 1
                for i, item in enumerate(node.items[2:], start=2):
                    walk(item, head, i, returns_value and i == last, loop_pushes)
                return
            if head in ('forall', 'exists') and len(node) >= 3 and isinstance(node[1], SList):
                binder = node[1]
                if len(binder) >= 2:
                    walk(binder[1], '@quantifier-source', 1, False, False)
                for item in node.items[2:]:
                    walk(item, head, 2, False, loop_pushes)
                return
            if head == 'for-each' and len(node) >= 2 and isinstance(node[1], SList):
                binder = node[1]
                pushes = self._count_push_to_var(list(node.items[2:]), name) > 0
                if len(binder) >= 2:
                    walk(binder[1], '@for-each-source', 1, False, pushes)
                for item in node.items[2:]:
                    walk(item, head, 2, False, loop_pushes)
                return
            last = len(node) - 1
            block = head in ('do',)
            for i, item in enumerate(node.items):
                walk(item, head, i, returns_value and block and i == last, loop_pushes)

        walk(body, None, -1, True, False)
        return ok

    def _ip_loop_writes(self, loop) -> Tuple[set, set, bool]:
        """(names a `set!` in the loop assigns, tracked lists it pushes, whether it has c-inline)."""
        return self._ip_writes(loop.items[2:])

    def _ip_writes(self, items) -> Tuple[set, set, bool]:
        """(names a `set!` under `items` assigns, tracked lists pushed, whether there is c-inline)."""
        names, pushed = set(), set()
        cinline = False

        def walk(node):
            nonlocal cinline
            if not isinstance(node, SList) or len(node) == 0:
                return
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head == 'quote':
                return
            if head == 'c-inline':
                cinline = True
            if head == 'set!' and len(node) >= 2 and isinstance(node[1], Symbol):
                names.add(node[1].name)
            if head == 'list-push' and len(node) >= 2 and isinstance(node[1], Symbol):
                if node[1].name in self._ip_tracked:
                    pushed.add(node[1].name)
            for item in node.items:
                walk(item)

        for item in items:
            walk(item)
        return names, pushed, cinline

    def _ip_own_break(self, items) -> bool:
        """A break or continue that leaves this loop, not one nested inside it."""
        def walk(node):
            if not isinstance(node, SList) or len(node) == 0:
                return False
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head in ('break', 'continue'):
                return True
            if head in _LOOP_HEADS or head in ('fn', 'quote'):
                return False
            return any(walk(item) for item in node.items)
        return any(walk(item) for item in items)

    def _ip_contains_return(self, items) -> bool:
        return any(self._contains_any_form(item, ('return',)) for item in items)

    # ------------------------------------------------------------------
    # Calls: what they read and what they may change
    # ------------------------------------------------------------------

    def _ip_signature(self, name: str):
        """(param types, modes, return type, is_pure, known) for a user or imported function."""
        tr = self._xp_tr
        registry = tr.function_registry
        if registry is not None and name in registry.functions:
            fn_def = registry.functions[name]
            types = [(_parse_type_expr_simple(t, self.type_env.type_registry) if t is not None else None)
                     for t in fn_def.param_type_exprs]
            ret = getattr(fn_def, 'return_type_expr', None)
            ret_type = _parse_type_expr_simple(ret, self.type_env.type_registry) if ret is not None else None
            return types, list(fn_def.param_modes), ret_type, fn_def.is_pure, True
        sig = tr.imported_defs.functions.get(name)
        if sig is not None:
            modes = list(getattr(sig, 'param_modes', [])) or [None] * len(sig.param_types)
            return (list(sig.param_types), modes, getattr(sig, 'return_type', None),
                    getattr(sig, 'is_pure', False), True)
        return [], [], None, False, False

    def _ip_is_user_function(self, name: str) -> bool:
        tr = self._xp_tr
        registry = tr.function_registry
        return ((registry is not None and name in registry.functions)
                or name in tr.imported_defs.functions)

    def _ip_call_effect(self, call) -> Optional[str]:
        """What a call in the body may change, as a description; None if nothing."""
        head = call[0].name if isinstance(call[0], Symbol) else None
        if head is None:
            return "a call through a computed function"
        where = f"{head} (line {getattr(call, 'line', '?')})"
        if head == 'list-push' and len(call) >= 2 and isinstance(call[1], Symbol) \
                and call[1].name in self._ip_tracked:
            return None
        if self._ip_is_user_function(head):
            if self._xp_callee_is_pure(head, self._xp_tr):
                return None
            types, modes, _, _, _ = self._ip_signature(head)
            if any(mode == 'out' for mode in modes):
                return where
            if self._xp_params_are_values(head):
                return None
            return where
        if head in _MUTATORS:
            return where
        if head in _ALLOCATORS or head in _NEUTRAL_HEADS or head in _EXTRA_STATE_READS:
            return None
        if head in ('record-new', 'union-new', 'fn', 'quote', 'cast', 'forall', 'exists',
                    'implies', 'if', 'cond', 'when', 'match', 'do', 'let', 'let*', 'set!',
                    'return', 'break', 'continue', '@loop-invariant', 'and', 'or', 'not'):
            return None
        if head.startswith('@'):
            return None
        return where

    def _ip_first_effect(self, items) -> Optional[str]:
        """The first thing under `items` that may change a collection, if any."""
        for item in items:
            if self._contains_any_form(item, ('c-inline',)):
                return "c-inline"
            for call in self._ip_call_nodes_all(item):
                effect = self._ip_call_effect(call)
                if effect is not None:
                    return effect
        return None

    def _ip_call_nodes_all(self, expr) -> List[Any]:
        """Call-shaped nodes, statements included, read by syntax (skipping lambdas' params)."""
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
            if name == 'quote' or name.startswith('@'):
                return
            if name in ('let', 'let*') and len(node) >= 2 and isinstance(node[1], SList):
                for binding in node[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        walk(binding[-1])
                for item in node.items[2:]:
                    walk(item)
                return
            if name in ('for-each',) and len(node) >= 2 and isinstance(node[1], SList):
                binder = node[1]
                if len(binder) >= 2:
                    source = binder[1]
                    # A desugared callback's source is the call minus its
                    # lambda; the iteration itself changes nothing.
                    if not self._ip_is_callback_source(source):
                        walk(source)
                for item in node.items[2:]:
                    walk(item)
                return
            if name in ('forall', 'exists') and len(node) >= 3:
                for item in node.items[2:]:
                    walk(item)
                return
            if name in ('if', 'when', 'cond', 'match', 'do', 'while', 'set!', 'return', 'fn'):
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
                start = 2 if name == 'set!' else 1
                for item in node.items[start:]:
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
            if name == 'c-inline':
                out.append(node)
                return
            out.append(node)
            for item in node.items[1:]:
                walk(item)

        walk(expr)
        return out

    def _ip_is_callback_source(self, source) -> bool:
        if not (isinstance(source, SList) and len(source) >= 1 and isinstance(source[0], Symbol)):
            return False
        sig = self._xp_tr.imported_defs.functions.get(source[0].name)
        return sig is not None and bool(getattr(sig, 'callback_assumptions', None))

    def _ip_static_type(self, expr, st: _IState):
        if isinstance(expr, Symbol):
            return st.types.get(expr.name)
        if isinstance(expr, Number):
            return PrimitiveType('Int')
        if not (isinstance(expr, SList) and len(expr) >= 1 and isinstance(expr[0], Symbol)):
            return None
        head = expr[0].name
        if head == 'record-new' and len(expr) >= 2:
            return _parse_type_expr_simple(expr[1], self.type_env.type_registry)
        if head == '.' and len(expr) >= 3 and isinstance(expr[2], Symbol):
            base = self._ip_resolve(self._ip_static_type(expr[1], st))
            if isinstance(base, RecordType):
                return base.fields.get(expr[2].name)
            return None
        if self._ip_is_user_function(head):
            return self._ip_signature(head)[2]
        return None

    def _ip_resolve(self, typ):
        """Follow a named type to its definition."""
        seen = 0
        while isinstance(typ, PrimitiveType) and seen < 8:
            target = (self.type_env.type_registry.get(typ.name)
                      or self._xp_tr.imported_defs.types.get(typ.name))
            if target is None or target is typ:
                return typ
            typ = target
            seen += 1
        return typ

    def _ip_state_reads(self, expr, st: _IState) -> List[str]:
        """Reads of collection state in `expr` (see module doc).

        A field read is one unless the record it reads from is known to be a
        value - so the names a quantifier or a match arm binds carry the type
        they are bound at.
        """
        reads: List[str] = []
        tracked = set(st.seqs)

        def type_of(node, bound):
            if isinstance(node, Symbol) and node.name in bound:
                return bound[node.name]
            if is_form(node, '.') and len(node) >= 3 and isinstance(node[2], Symbol):
                base = self._ip_resolve(type_of(node[1], bound))
                return base.fields.get(node[2].name) if isinstance(base, RecordType) else None
            return self._ip_static_type(node, st)

        def walk(node, bound):
            if isinstance(node, Symbol):
                n = node.name
                if '.' in n.strip('.') and n.split('.')[0] not in bound:
                    reads.append(f"the field path {n}")
                return
            if not isinstance(node, SList) or len(node) == 0:
                return
            head = node[0]
            if not isinstance(head, Symbol):
                for item in node.items:
                    walk(item, bound)
                return
            name = head.name
            if name == 'quote':
                return
            if name in ('forall', 'exists') and len(node) >= 3 and isinstance(node[1], SList):
                binder = node[1]
                inner = bound
                element = None
                if len(binder) >= 2:
                    source = binder[1]
                    if isinstance(source, Symbol) and source.name[:1].isupper():
                        element = _parse_type_expr_simple(source, self.type_env.type_registry)
                    else:
                        if not (isinstance(source, Symbol) and source.name in tracked):
                            reads.append(f"a quantifier over {pretty_print(source)}")
                        walk(source, bound)
                        collection = self._ip_resolve(type_of(source, bound))
                        element = getattr(collection, 'element_type', None)
                if len(binder) >= 1 and isinstance(binder[0], Symbol):
                    inner = dict(bound)
                    inner[binder[0].name] = element
                for item in node.items[2:]:
                    walk(item, inner)
                return
            if name == 'match' and len(node) >= 3:
                walk(node[1], bound)
                scrutinee = self._ip_resolve(type_of(node[1], bound))
                for clause in node.items[2:]:
                    if not isinstance(clause, SList) or len(clause) < 1:
                        continue
                    inner = dict(bound)
                    pattern = clause[0]
                    if isinstance(pattern, SList) and len(pattern) >= 2 and isinstance(pattern[0], Symbol):
                        tag = pattern[0].name.lstrip("'")
                        for binder in pattern.items[1:]:
                            if isinstance(binder, Symbol):
                                inner[binder.name] = self._ip_payload_type(scrutinee, tag)
                    for item in clause.items[1:]:
                        walk(item, inner)
                return
            if name in ('list-len', 'list-contains') and len(node) >= 2 \
                    and isinstance(node[1], Symbol) and node[1].name in tracked:
                for item in node.items[2:]:
                    walk(item, bound)
                return
            if name in _STATE_READS or name in _EXTRA_STATE_READS:
                reads.append(name)
            elif name == '.':
                if len(node) >= 2:
                    base = self._ip_resolve(type_of(node[1], bound))
                    if not isinstance(base, RecordType):
                        reads.append(f"the field {pretty_print(node)}")
                    walk(node[1], bound)
                return
            elif self._ip_is_user_function(name):
                if self._xp_callee_is_pure(name, self._xp_tr) and not self._xp_params_are_values(name):
                    reads.append(f"{name}, which is handed a collection")
            for item in node.items[1:]:
                walk(item, bound)

        walk(expr, {})
        return reads

    def _ip_post_is_one_state(self, fn_name: str):
        """A filter for a callee's postconditions: keep those that read no collection state.

        A postcondition relating the state before the call to the state after
        it reads both through the same terms here, and so says something else.
        A @pure callee changes nothing, so its every postcondition is kept.
        """
        tr = self._xp_tr
        if self._xp_callee_is_pure(fn_name, tr):
            return None
        registry = tr.function_registry
        param_types: Dict[str, Any] = {}
        ret_type = None
        if registry is not None and fn_name in registry.functions:
            fn_def = registry.functions[fn_name]
            for param, texpr in zip(fn_def.params, fn_def.param_type_exprs):
                param_types[param] = (_parse_type_expr_simple(texpr, self.type_env.type_registry)
                                      if texpr is not None else None)
            ret = getattr(fn_def, 'return_type_expr', None)
            ret_type = _parse_type_expr_simple(ret, self.type_env.type_registry) if ret is not None else None
        elif fn_name in tr.imported_defs.functions:
            sig = tr.imported_defs.functions[fn_name]
            param_types = dict(zip(sig.params, sig.param_types))
            ret_type = getattr(sig, 'return_type', None)
        param_types['$result'] = ret_type
        probe = _IState({}, param_types, {}, None, None)

        def keep(post) -> bool:
            return not self._ip_state_reads(post, probe)
        return keep

    # ------------------------------------------------------------------
    # Terms
    # ------------------------------------------------------------------

    def _ip_opaque(self, sort):
        return z3.FreshConst(sort, _OPAQUE)

    def _ip_eval(self, expr, st: _IState, pc, invariant=False, sort=None):
        """Translate a term at this program point. Returns (term, state after it).

        For an invariant, a read the walk cannot vouch for raises _Unchecked;
        in the body it becomes an opaque value instead - as does a term the
        translator cannot read at all, when `sort` says what it would be.
        """
        try:
            return self._ip_eval_term(expr, st, pc, invariant)
        except _NoTranslation:
            if invariant or sort is None:
                raise
            effect = self._ip_first_effect([expr])
            return self._ip_opaque(sort), st.but(dirty=st.dirty or effect)

    def _ip_eval_term(self, expr, st: _IState, pc, invariant):
        if isinstance(expr, SList) and len(expr) > 0 and isinstance(expr[0], Symbol) \
                and expr[0].name in _UNMODELLED_FORMS:
            raise _Bail(f"{expr[0].name} is not modelled")
        if self._contains_any_form(expr, tuple(_UNMODELLED_FORMS) + ('return', 'c-inline')):
            raise _Bail("a term with control flow the analysis does not follow")
        self._ip_check_pure(expr)
        effect = None
        for call in self._ip_call_nodes_all(expr):
            if isinstance(call[0], Symbol) and call[0].name in _MUTATORS:
                raise _Bail(f"{call[0].name} in a term")
            effect = effect or self._ip_call_effect(call)
        reads = self._ip_state_reads(expr, st)
        stale = st.dirty or (effect if reads else None)
        if reads and stale:
            if invariant:
                raise _Unchecked(f"it reads {reads[0]}, which {stale} may change")
            term = self._ip_translate(expr, st, pc, instantiate=False, pin=False)
            return self._ip_opaque(term.sort()), st.but(dirty=st.dirty or effect)
        term = self._ip_translate(expr, st, pc, instantiate=True, pin=True, invariant=invariant)
        return term, (st.but(dirty=effect) if effect and not st.dirty else st)

    def _ip_check_pure(self, expr):
        """Refuse statement forms inside a term; a fresh collection is fine."""
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                if head.name in ('let', 'let*', 'do', 'when', 'match', 'set!', 'list-push'):
                    raise _Bail(f"{head.name} in a term")
                if head.name == 'quote':
                    return
            for item in expr.items:
                self._ip_check_pure(item)

    def _ip_translate(self, expr, st: _IState, pc, instantiate=True, pin=True, invariant=False):
        tr = self._xp_tr
        saved_vars = {}
        saved_seqs = {}
        for name, value in st.env.items():
            saved_vars[name] = tr.variables.get(name, _MISSING)
            tr.variables[name] = value
        for name, seq in st.seqs.items():
            saved_seqs[name] = tr.list_seqs.get(name, _MISSING)
            tr.list_seqs[name] = seq
        start = len(tr.constraints)
        self._ip_obligations = []
        tr._pinned_terms = {}
        try:
            if pin:
                self._ip_pin(expr, pc)
            try:
                self._ip_expand_quantifiers(expr, st, {})
                term = tr.translate_expr(expr)
            except z3.Z3Exception as error:
                if invariant:
                    raise _Unchecked(f"{pretty_print(expr)} does not translate ({error})")
                raise _Bail(f"a term does not translate ({error})")
            except _NoTranslation as error:
                if invariant:
                    raise _Unchecked(str(error))
                raise
            if term is None:
                if invariant:
                    raise _Unchecked(f"{pretty_print(expr)} does not translate here")
                raise _NoTranslation(f"{pretty_print(expr)} does not translate")
            if instantiate:
                for call in self._xp_call_nodes(expr):
                    head = call[0].name
                    if not self._xp_is_builtin(head, tr) and self._ip_is_user_function(head):
                        self._xp_callee_posts(call, head, pc,
                                              keep_post=self._ip_post_is_one_state(head))
        finally:
            for index in range(start, len(tr.constraints)):
                if index in tr.definedness_constraints:
                    self._ip_obligations.append(tr.constraints[index])
                else:
                    self._xp_axioms.append(z3.Implies(pc, tr.constraints[index]))
            del tr.constraints[start:]
            tr.definedness_constraints.difference_update(
                {i for i in tr.definedness_constraints if i >= start})
            tr._pinned_terms = {}
            for name, previous in saved_vars.items():
                if previous is _MISSING:
                    tr.variables.pop(name, None)
                else:
                    tr.variables[name] = previous
            for name, previous in saved_seqs.items():
                if previous is _MISSING:
                    tr.list_seqs.pop(name, None)
                else:
                    tr.list_seqs[name] = previous
        return term

    def _ip_expand_quantifiers(self, expr, st: _IState, bound: Dict[str, Any]) -> None:
        """Translate quantifiers over tracked lists by the list's structure.

        A tracked list's sequence is built from pushes and branches:
        `Concat(s, Unit(e))`, `If(g, a, b)`, the empty sequence, and at the
        bottom a sequence the walk knows nothing more about. A claim about
        every element of it is the claim about each part, and about `e`
        itself - no quantifier over a concatenation, where Z3's instantiation
        is hit and miss. Each such quantifier's node is pinned to that
        translation, so the translator returns it in place.
        """
        tr = self._xp_tr
        if not isinstance(expr, SList) or len(expr) == 0:
            return
        head = expr[0].name if isinstance(expr[0], Symbol) else None
        if head == 'quote':
            return
        if head in ('forall', 'exists') and len(expr) >= 3 and isinstance(expr[1], SList) \
                and len(expr[1]) == 2 and isinstance(expr[1][0], Symbol) \
                and isinstance(expr[1][1], Symbol) and expr[1][1].name in st.seqs \
                and expr[1][1].name not in bound:
            var = expr[1][0].name
            body = expr[2] if len(expr) == 3 else SList([Symbol('and')] + list(expr.items[2:]))
            term = self._ip_expand(head, var, body, st.seqs[expr[1][1].name], st, bound)
            tr._pinned_terms[id(expr)] = term
            return
        if head in ('forall', 'exists') and len(expr) >= 3 and isinstance(expr[1], SList) \
                and len(expr[1]) >= 1 and isinstance(expr[1][0], Symbol):
            # Another quantifier binds a name of its own: a tracked quantifier
            # inside it is translated along with it, where that name is bound.
            return
        for item in expr.items[1:]:
            self._ip_expand_quantifiers(item, st, bound)

    def _ip_expand(self, kind: str, var: str, body, seq, st: _IState, bound: Dict[str, Any]):
        if z3.is_app_of(seq, z3.Z3_OP_SEQ_CONCAT):
            parts = [self._ip_expand(kind, var, body, child, st, bound) for child in seq.children()]
            return z3.And(*parts) if kind == 'forall' else z3.Or(*parts)
        if z3.is_app_of(seq, z3.Z3_OP_SEQ_UNIT):
            return self._ip_body_at(var, seq.arg(0), body, st, bound)
        if z3.is_app_of(seq, z3.Z3_OP_ITE):
            return z3.If(seq.arg(0), self._ip_expand(kind, var, body, seq.arg(1), st, bound),
                         self._ip_expand(kind, var, body, seq.arg(2), st, bound))
        if z3.is_app_of(seq, z3.Z3_OP_SEQ_EMPTY):
            return z3.BoolVal(kind == 'forall')
        index = z3.FreshInt('i')
        inside = z3.And(index >= 0, index < z3.Length(seq))
        claim = self._ip_body_at(var, seq[index], body, st, bound)
        if kind == 'forall':
            return z3.ForAll([index], z3.Implies(inside, claim))
        return z3.Exists([index], z3.And(inside, claim))

    def _ip_body_at(self, var: str, element, body, st: _IState, bound: Dict[str, Any]):
        """`body` with `var` bound to `element`."""
        tr = self._xp_tr
        inner = dict(bound)
        inner[var] = element
        self._ip_expand_quantifiers(body, st, inner)
        saved = {name: tr.variables.get(name, _MISSING) for name in inner}
        tr.variables.update(inner)
        try:
            term = tr.translate_expr(body)
        finally:
            for name, previous in saved.items():
                if previous is _MISSING:
                    tr.variables.pop(name, None)
                else:
                    tr.variables[name] = previous
        if term is None or not z3.is_bool(term):
            raise _NoTranslation(f"{pretty_print(body)} does not translate")
        return term

    def _ip_pin(self, expr, pc):
        """Constructors get constants carrying their fields; calls get constants of their own.

        A call to a function not declared @pure may return something different
        each time, so it is a fresh constant rather than an uninterpreted
        function of its arguments; a head the verifier knows nothing about is
        opaque.
        """
        tr = self._xp_tr
        if not isinstance(expr, SList) or len(expr) == 0:
            return
        head = expr[0]
        if isinstance(head, Symbol) and head.name in ('forall', 'exists'):
            return
        for item in self._xp_evaluated_parts(expr):
            self._ip_pin(item, pc)
        if not isinstance(head, Symbol) or head.name in ('quote', 'cond', 'if', 'cast', '.'):
            return
        name = head.name
        if name == 'record-new':
            for item in expr.items[2:]:
                if isinstance(item, SList) and len(item) >= 2 and tr.translate_expr(item[1]) is None:
                    raise _Bail("a record field does not translate")
            const = z3.FreshConst(z3.IntSort(), 'record')
            self._xp_axioms.extend(self._extract_record_field_axioms(
                expr, tr, base_accessor=const, path_cond=pc, bindings={}))
            tr._pinned_terms[id(expr)] = const
        elif name == 'union-new':
            if len(expr) < 3 or not isinstance(expr[2], Symbol):
                raise _Bail("malformed union-new")
            self._xp_pin_variant(expr, expr[2].name, expr.items[3:], pc)
        elif name in _OPTION_RESULT_CONSTRUCTORS:
            self._xp_pin_variant(expr, name, expr.items[1:], pc)
        elif name in _ALLOCATORS:
            natural = tr.translate_expr(expr)
            sort = natural.sort() if natural is not None else z3.IntSort()
            tr._pinned_terms[id(expr)] = z3.FreshConst(sort, 'alloc')
        elif self._xp_is_builtin(name, tr) or name in _EXTRA_STATE_READS \
                or name in ('and', 'or', 'not', 'implies'):
            return
        elif self._ip_is_user_function(name):
            if self._xp_callee_is_pure(name, tr):
                return
            natural = tr.translate_expr(expr)
            if natural is None:
                raise _Bail(f"call to {name!r} does not translate")
            tr._pinned_terms[id(expr)] = z3.FreshConst(natural.sort(), 'call')
        else:
            natural = tr.translate_expr(expr)
            sort = natural.sort() if natural is not None else z3.IntSort()
            tr._pinned_terms[id(expr)] = self._ip_opaque(sort)

    def _ip_formula(self, condition, st: _IState, pc):
        """An invariant at this program point: (term, definedness obligations)."""
        if self._ip_mentions(condition, '$result'):
            raise _Unchecked("it names $result, which the loop does not have yet")
        for source in self._ip_quantifier_sources(condition):
            if isinstance(source, Symbol) and source.name in st.seqs:
                continue
            root = self._ip_root_name(source)
            if root is None:
                raise _Unchecked(f"it quantifies over {pretty_print(source)}, which is not a named collection")
            if root in self._ip_assigned or root not in self._ip_params:
                raise _Unchecked(f"it quantifies over {pretty_print(source)}, "
                                 "whose name does not always denote the same collection")
        impure = self._ip_impure_call_in_quantifier(condition)
        if impure is not None:
            raise _Unchecked(f"it calls {impure}, which is not @pure, inside a quantifier")
        term, _ = self._ip_eval(condition, st, pc, invariant=True)
        if not z3.is_bool(term):
            raise _Unchecked("it is not a Boolean condition")
        return term, list(self._ip_obligations)

    def _ip_impure_call_in_quantifier(self, expr) -> Optional[str]:
        """A call inside a quantifier is an uninterpreted function of its
        arguments, which is only right for a function that is one."""
        def walk(node, inside):
            if not isinstance(node, SList) or len(node) == 0:
                return None
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head == 'quote':
                return None
            if head in ('forall', 'exists'):
                for item in node.items[2:]:
                    found = walk(item, True)
                    if found:
                        return found
                return None
            if inside and head is not None and self._ip_is_user_function(head) \
                    and not self._xp_callee_is_pure(head, self._xp_tr):
                return head
            for item in node.items[1:]:
                found = walk(item, inside)
                if found:
                    return found
            return None
        return walk(expr, False)

    def _ip_quantifier_sources(self, expr) -> List[Any]:
        out = []

        def walk(node):
            if not isinstance(node, SList) or len(node) == 0:
                return
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head == 'quote':
                return
            if head in ('forall', 'exists') and len(node) >= 3 and isinstance(node[1], SList) \
                    and len(node[1]) >= 2:
                source = node[1][1]
                if not (isinstance(source, Symbol) and source.name[:1].isupper()):
                    out.append(source)
            if head in ('list-contains', 'list-len') and len(node) >= 2:
                out.append(node[1])
            for item in node.items:
                walk(item)

        walk(expr)
        return out

    @staticmethod
    def _ip_root_name(expr) -> Optional[str]:
        """The name at the root of `x` or `(. x f)`; None for anything deeper."""
        if isinstance(expr, Symbol):
            return None if '.' in expr.name.strip('.') else expr.name
        if is_form(expr, '.') and len(expr) == 3 and isinstance(expr[1], Symbol) \
                and isinstance(expr[2], Symbol):
            return expr[1].name
        return None

    @staticmethod
    def _ip_mentions(expr, name: str) -> bool:
        if isinstance(expr, Symbol):
            return expr.name == name
        if isinstance(expr, SList):
            return any(InvariantProverMixin._ip_mentions(item, name) for item in expr.items)
        return False

    # ------------------------------------------------------------------
    # Statements
    # ------------------------------------------------------------------

    def _ip_stmt(self, stmt, st: _IState, pc) -> _IState:
        if not isinstance(stmt, SList) or len(stmt) == 0:
            return st
        head = stmt[0]
        name = head.name if isinstance(head, Symbol) else None
        if name is None:
            raise _Bail("a call through a computed function")
        if name.startswith('@'):
            return st
        if name == 'do':
            for item in stmt.items[1:]:
                st = self._ip_stmt(item, st, pc)
            return st
        if name in ('let', 'let*'):
            return self._ip_let(stmt, st, pc)
        if name == 'when':
            if len(stmt) < 2:
                raise _Bail("malformed when")
            guard, st = self._ip_guard(stmt[1], st, pc)
            taken = st
            for item in stmt.items[2:]:
                taken = self._ip_stmt(item, taken, z3.And(pc, guard))
            return self._ip_merge(guard, taken, st)
        if name == 'if':
            if len(stmt) < 3:
                raise _Bail("malformed if")
            guard, st = self._ip_guard(stmt[1], st, pc)
            then_st = self._ip_stmt(stmt[2], st, z3.And(pc, guard))
            else_st = (self._ip_stmt(stmt[3], st, z3.And(pc, z3.Not(guard)))
                       if len(stmt) >= 4 else st)
            return self._ip_merge(guard, then_st, else_st)
        if name == 'cond':
            return self._ip_cond(stmt, st, pc)
        if name == 'match':
            return self._ip_match(stmt, st, pc)
        if name == 'set!':
            return self._ip_set(stmt, st, pc)
        if name == 'list-push':
            return self._ip_push(stmt, st, pc)
        if name in _LOOP_HEADS:
            return self._ip_loop(stmt, st, pc)
        if name == 'return':
            if len(stmt) >= 2:
                _, st = self._ip_eval(stmt[1], st, pc, sort=z3.IntSort())
            return st.but(alive=z3.BoolVal(False))
        if name == 'c-inline':
            # C can write any local and any collection it reaches.
            env = {n: self._ip_opaque(v.sort()) for n, v in st.env.items()}
            seqs = {n: self._ip_opaque(s.sort()) for n, s in st.seqs.items()}
            return st.but(env=env, seqs=seqs, dirty=st.dirty or "c-inline")
        if name in ('break', 'continue'):
            # Only in a loop without invariants (one with them is refused in
            # _ip_loop); nothing below needs the rest of the iteration skipped.
            return st
        if name in _MUTATORS:
            for item in stmt.items[1:]:
                _, st = self._ip_eval(item, st, pc, sort=z3.IntSort())
            return st.but(dirty=st.dirty or self._ip_call_effect(stmt))
        if name in _UNMODELLED_FORMS or name == 'fn':
            raise _Bail(f"{name} is not modelled")
        # A call made for its effect.
        _, st = self._ip_eval(stmt, st, pc, sort=z3.IntSort())
        return st

    def _ip_let(self, stmt, st: _IState, pc) -> _IState:
        if len(stmt) < 2 or not isinstance(stmt[1], SList):
            raise _Bail("malformed let")
        inner = st
        introduced: List[str] = []
        for binding in stmt[1].items:
            if not isinstance(binding, SList) or len(binding) < 2:
                raise _Bail("malformed binding")
            bname = self._binding_name(binding)
            if bname is None:
                raise _Bail("unnamed binding")
            init = binding[-1]
            type_expr = None
            if isinstance(binding[0], Symbol) and binding[0].name == 'mut':
                if len(binding) >= 4:
                    type_expr = binding[2]
            elif isinstance(binding[0], Symbol) and len(binding) >= 3:
                type_expr = binding[1]
            if self._ip_has_statements(init):
                inner = self._ip_opaque_initializer(init, type_expr, bname, inner)
                introduced.append(bname)
                continue
            if bname in self._ip_tracked and is_form(init, 'list-new'):
                env = dict(inner.env)
                env[bname] = z3.FreshConst(z3.IntSort(), 'list')
                seqs = dict(inner.seqs)
                seqs[bname] = z3.Empty(z3.SeqSort(z3.IntSort()))
                types = dict(inner.types)
                types[bname] = ListType(_parse_type_expr_simple(init[-1], self.type_env.type_registry))
                inner = inner.but(env=env, seqs=seqs, types=types)
            else:
                typ = (_parse_type_expr_simple(type_expr, self.type_env.type_registry)
                       if type_expr is not None else self._ip_static_type(init, inner))
                term, inner = self._ip_eval(init, inner, pc,
                                            sort=self._ip_sort_of(self._ip_resolve(typ)))
                env = dict(inner.env)
                env[bname] = term
                types = dict(inner.types)
                types[bname] = typ
                inner = inner.but(env=env, types=types)
            introduced.append(bname)
        for item in stmt.items[2:]:
            inner = self._ip_stmt(item, inner, pc)
        env, types, seqs = dict(inner.env), dict(inner.types), dict(inner.seqs)
        for bname in introduced:
            if bname in st.env:
                env[bname] = st.env[bname]
                types[bname] = st.types.get(bname)
            else:
                env.pop(bname, None)
                types.pop(bname, None)
            if bname in st.seqs:
                seqs[bname] = st.seqs[bname]
            elif bname not in st.env:
                seqs.pop(bname, None)
        return inner.but(env=env, types=types, seqs=seqs)

    def _ip_opaque_initializer(self, init, type_expr, bname: str, st: _IState) -> _IState:
        """Bind `bname` to an initializer the walk does not follow.

        Its value is opaque, and so is everything it may change: the names it
        assigns, the lists it pushes to, every local if it has c-inline, and
        collection state if it calls anything that might. Invariants of loops
        inside it are not checked.
        """
        self._ip_unknown_within(init, f"it is in the initializer of {bname}, "
                                      "which the analysis does not follow")
        names, pushed, cinline = self._ip_writes([init])
        names = set(st.env) if cinline else {n for n in names if n in st.env}
        if cinline:
            pushed = set(st.seqs)
        state = self._ip_havoc(st, names, pushed, opaque=True)
        effect = self._ip_first_effect([init])
        typ = (_parse_type_expr_simple(type_expr, self.type_env.type_registry)
               if type_expr is not None else None)
        env = dict(state.env)
        env[bname] = self._ip_opaque(self._ip_sort_of(self._ip_resolve(typ)))
        types = dict(state.types)
        types[bname] = typ
        return state.but(env=env, types=types, dirty=st.dirty or effect)

    def _ip_has_statements(self, expr) -> bool:
        return self._contains_any_form(
            expr, ('do', 'let', 'let*', 'when', 'set!', 'list-push', 'for-each', 'while',
                   'for', 'return', 'c-inline') + tuple(_MUTATORS))

    def _ip_guard(self, expr, st: _IState, pc):
        term, st = self._ip_eval(expr, st, pc, sort=z3.BoolSort())
        if not z3.is_bool(term):
            return self._ip_opaque(z3.BoolSort()), st
        return term, st

    def _ip_cond(self, stmt, st: _IState, pc) -> _IState:
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
                    default = self._ip_stmt(item, default, guard_pc)
                break
            term, st = self._ip_guard(test, st, pc)
            guard = z3.And(term, *[z3.Not(t) for t in earlier]) if earlier else term
            branch = st
            for item in clause.items[1:]:
                branch = self._ip_stmt(item, branch, z3.And(pc, guard))
            clauses.append((guard, branch))
            earlier.append(term)
        else:
            # No `else`: when no test holds, nothing runs after the tests did.
            default = st
        result = default
        for guard, branch in reversed(clauses):
            result = self._ip_merge(guard, branch, result)
        return result

    def _ip_match(self, stmt, st: _IState, pc) -> _IState:
        tr = self._xp_tr
        if len(stmt) < 3:
            raise _Bail("malformed match")
        scrutinee, st = self._ip_eval(stmt[1], st, pc, sort=z3.IntSort())
        is_enum = tr._is_enum_match(stmt)
        if is_enum:
            tag_term = scrutinee
        else:
            tag_func = tr.variables.get('union_tag')
            if not isinstance(tag_func, z3.FuncDeclRef):
                tag_func = z3.Function('union_tag', z3.IntSort(), z3.IntSort())
                tr.variables['union_tag'] = tag_func
            tag_term = tag_func(scrutinee)
        scrutinee_type = self._ip_resolve(self._ip_static_type(stmt[1], st))

        arms = []
        tests = []
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
                arms.append((guard, self._ip_arm(body_items, st, {}, {}, z3.And(pc, guard))))
                continue
            tag, binders = self._xp_pattern(pattern)
            if tag in seen_tags:
                raise _Bail("duplicate match arm")
            seen_tags.add(tag)
            if tag not in tr.enum_values and f"'{tag}" not in tr.enum_values:
                raise _Bail(f"unknown tag {tag!r}")
            test = tag_term == z3.IntVal(tr.constructor_tag(tag))
            bound_terms, bound_types = {}, {}
            for index, binder in enumerate(binders):
                if binder == '_':
                    continue
                if is_enum:
                    raise _Bail("enum arm with a payload")
                sort = tr.payload_sort(tag, index)
                if sort is None:
                    raise _Bail(f"payload {index} of {tag!r} has no known sort")
                bound_terms[binder] = tr.union_payload_accessor(tag, index, sort)(scrutinee)
                bound_types[binder] = self._ip_payload_type(scrutinee_type, tag)
            arms.append((test, self._ip_arm(body_items, st, bound_terms, bound_types,
                                            z3.And(pc, test))))
            tests.append(test)

        result = st
        for guard, arm_state in reversed(arms):
            result = self._ip_merge(guard, arm_state, result)
        return result

    def _ip_payload_type(self, scrutinee_type, tag: str):
        if scrutinee_type is None:
            return None
        if tag == 'some':
            return getattr(scrutinee_type, 'inner', None)
        if tag == 'ok':
            return getattr(scrutinee_type, 'ok_type', None)
        if tag == 'error':
            return getattr(scrutinee_type, 'err_type', None)
        payloads = getattr(scrutinee_type, 'payload_types', None) or {}
        recorded = payloads.get(tag)
        if recorded:
            return recorded[0]
        variants = getattr(scrutinee_type, 'variants', None) or {}
        value = variants.get(tag) if isinstance(variants, dict) else None
        return value

    def _ip_arm(self, body_items, st: _IState, bound_terms, bound_types, pc) -> _IState:
        env = dict(st.env)
        env.update(bound_terms)
        types = dict(st.types)
        types.update(bound_types)
        inner = st.but(env=env, types=types)
        for item in body_items:
            inner = self._ip_stmt(item, inner, pc)
        out_env, out_types = {}, {}
        for bname, value in st.env.items():
            if bname in bound_terms:
                out_env[bname] = value
                out_types[bname] = st.types.get(bname)
            else:
                out_env[bname] = inner.env.get(bname, value)
                out_types[bname] = inner.types.get(bname, st.types.get(bname))
        return inner.but(env=out_env, types=out_types)

    def _ip_set(self, stmt, st: _IState, pc) -> _IState:
        if len(stmt) != 3 or not isinstance(stmt[1], Symbol):
            raise _Bail("an assignment to something other than a name")
        target = stmt[1].name
        if target not in st.env or target in st.seqs:
            raise _Bail(f"an assignment to {target}, which the analysis does not follow")
        value, st = self._ip_eval(stmt[2], st, pc, sort=st.env[target].sort())
        if value.sort() != st.env[target].sort():
            raise _Bail("an assignment changes a name's sort")
        env = dict(st.env)
        env[target] = value
        return st.but(env=env)

    def _ip_push(self, stmt, st: _IState, pc) -> _IState:
        if len(stmt) != 3:
            raise _Bail("malformed list-push")
        target = stmt[1]
        element, st = self._ip_eval(stmt[2], st, pc, sort=z3.IntSort())
        if isinstance(target, Symbol) and target.name in st.seqs:
            if element.sort() != z3.IntSort():
                raise _Bail("a pushed element is not an Int-sorted term")
            seqs = dict(st.seqs)
            seqs[target.name] = z3.Concat(st.seqs[target.name], z3.Unit(element))
            return st.but(seqs=seqs)
        return st.but(dirty=st.dirty or self._ip_call_effect(stmt))

    def _ip_merge(self, guard, taken: _IState, other: _IState) -> _IState:
        if set(taken.env) != set(other.env) or set(taken.seqs) != set(other.seqs):
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
        seqs = {}
        for bname, a in taken.seqs.items():
            b = other.seqs[bname]
            seqs[bname] = a if a.eq(b) else z3.If(guard, a, b)
        alive = taken.alive if taken.alive.eq(other.alive) else z3.If(guard, taken.alive, other.alive)
        types = dict(other.types)
        for bname, typ in taken.types.items():
            if types.get(bname) is None:
                types[bname] = typ
        return _IState(env, types, seqs, alive, taken.dirty or other.dirty)

    # ------------------------------------------------------------------
    # Loops
    # ------------------------------------------------------------------

    def _ip_loop(self, loop, st: _IState, pc) -> _IState:
        kind = loop[0].name
        conditions = self._ip_sites.get(id(loop), [])
        outcomes = [self._ip_outcomes[id(c)] for c in conditions]
        self._ip_loop_depth[id(loop)] = self._ip_depth
        body_items = [i for i in loop.items[2:] if not is_form(i, '@loop-invariant')]
        names, pushed, cinline = self._ip_loop_writes(loop)
        names = set(st.env) if cinline else {n for n in names if n in st.env}
        if cinline:
            pushed = set(st.seqs)

        reason = None
        if conditions:
            if cinline:
                reason = "the loop body has c-inline, which the analysis does not model"
            elif self._ip_own_break(body_items):
                reason = "break or continue in the loop body"
            elif kind == 'for':
                reason = "for loops are not checked"
        header = self._ip_header(loop, st, pc)
        if header is None and conditions and reason is None:
            reason = "the loop's header is not one the analysis follows"
        if header is not None and header[0] in ('each', 'for') and reason is None \
                and any(self._ip_mentions(c, header[1]) for c in conditions):
            # On entry and after the loop the name means something else, or
            # nothing; an invariant is about the state between iterations.
            reason = f"it names the loop variable {header[1]}"
        # What the loop iterates is evaluated once, before the first iteration.
        bounds = None
        if header is not None and header[0] == 'each':
            source = header[2]
            if isinstance(source, SList) and not is_form(source, '.') \
                    and not self._ip_is_callback_source(source):
                _, st = self._ip_eval(source, st, pc, sort=z3.IntSort())
        elif header is not None and header[0] == 'for':
            lo, st = self._ip_eval(header[2], st, pc)
            hi, st = self._ip_eval(header[3], st, pc)
            bounds = (lo, hi)

        # Base case.
        if conditions and reason is None:
            try:
                goals = [self._ip_formula(c, st, pc) for c in conditions]
            except _Unchecked as unchecked:
                reason = str(unchecked)
            else:
                for outcome, condition in zip(outcomes, conditions):
                    outcome.reads_state = bool(self._ip_state_reads(condition, st))
                for outcome, (goal, obligations) in zip(outcomes, goals):
                    self._ip_decide(outcome, z3.Implies(z3.And(pc, st.alive), z3.And(goal, *obligations)),
                                    st, "not established on entry")
        if reason is not None:
            for outcome in outcomes:
                self._ip_set_unknown(outcome, reason)

        checking = bool(conditions) and all(o.status == 'pending' for o in outcomes)

        # Inductive step, from an arbitrary iteration. Its hypotheses are
        # asserted outright in the checks made while it is walked (see
        # _ip_local); axioms recorded meanwhile carry its guard.
        body_effect = self._ip_first_effect(body_items)
        step = self._ip_havoc(st, names, pushed, opaque=not checking)
        step = step.but(alive=z3.BoolVal(True), dirty=st.dirty or body_effect)
        step_pc = z3.And(pc, z3.FreshBool('iteration'))
        local_start = len(self._ip_local)
        try:
            step, facts = self._ip_enter_iteration(header, bounds, st, step, step_pc)
            self._ip_local.extend(facts)
        except _Unchecked as unchecked:
            if checking:
                for outcome in outcomes:
                    self._ip_set_unknown(outcome, str(unchecked))
                checking = False
        if checking:
            try:
                self._ip_local.extend(self._ip_formula(c, step, step_pc)[0] for c in conditions)
            except _Unchecked as unchecked:
                for outcome in outcomes:
                    self._ip_set_unknown(outcome, str(unchecked))
                checking = False

        self._ip_depth += 1
        end = None
        try:
            end = step
            for item in body_items:
                end = self._ip_stmt(item, end, step_pc)
        except _Bail as bail:
            self._ip_unknown_within(loop, str(bail))
            checking = False
            end = None
        finally:
            self._ip_depth -= 1

        try:
            if checking and end is not None:
                self._ip_step_end(outcomes, conditions, end, step_pc)
        finally:
            del self._ip_local[local_start:]
        if conditions and any(o.status == 'failed' for o in outcomes):
            for outcome in outcomes:
                if outcome.status in ('pending', 'proved'):
                    self._ip_set_unknown(outcome, "another invariant of the same loop does not hold")

        proved = bool(conditions) and all(o.status == 'proved' for o in outcomes)

        # After the loop.
        after = self._ip_havoc(st, names, pushed, opaque=not proved)
        after = after.but(dirty=st.dirty or body_effect)
        if end is not None and self._ip_contains_return(body_items):
            after = after.but(alive=z3.And(st.alive, z3.FreshBool('alive')))
        if proved:
            for condition in conditions:
                try:
                    term, _ = self._ip_formula(condition, after, pc)
                except _Unchecked:
                    continue
                self._xp_axioms.append(z3.Implies(pc, term))
        if kind == 'while' and not self._ip_own_break(body_items) \
                and not self._ip_contains_return(body_items) and len(loop) >= 2:
            try:
                cond, after = self._ip_eval(loop[1], after, pc, sort=z3.BoolSort())
                if z3.is_bool(cond):
                    self._xp_axioms.append(z3.Implies(pc, z3.Not(cond)))
            except _Bail:
                pass
        return after

    def _ip_step_end(self, outcomes, conditions, end: _IState, step_pc) -> None:
        """Check each invariant where one iteration's body ends; mark the survivors proved."""
        try:
            goals = [self._ip_formula(c, end, step_pc) for c in conditions]
        except _Unchecked as unchecked:
            for outcome in outcomes:
                self._ip_set_unknown(outcome, str(unchecked))
            return
        for outcome, (goal, obligations) in zip(outcomes, goals):
            if outcome.status != 'pending':
                continue
            self._ip_decide(outcome, z3.Implies(z3.And(step_pc, end.alive),
                                                z3.And(goal, *obligations)),
                            end, "not preserved")
        for outcome in outcomes:
            if outcome.status == 'pending':
                outcome.status = 'proved'

    def _ip_header(self, loop, st: _IState, pc):
        """What the loop iterates: ('while', cond-expr), ('each', var, source), ('for', var, lo, hi)."""
        kind = loop[0].name
        if kind == 'while':
            return ('while', loop[1]) if len(loop) >= 2 else None
        if len(loop) < 2 or not isinstance(loop[1], SList):
            return None
        binder = loop[1]
        if kind == 'for':
            if len(binder) == 3 and isinstance(binder[0], Symbol):
                return ('for', binder[0].name, binder[1], binder[2])
            return None
        if len(binder) != 2 or not isinstance(binder[0], Symbol):
            return None
        return ('each', binder[0].name, binder[1])

    def _ip_enter_iteration(self, header, bounds, entry: _IState, step: _IState, pc):
        """Bind the loop variable for an arbitrary iteration; add what is known about it."""
        if header is None:
            raise _Unchecked("the loop's header is not one the analysis follows")
        if header[0] == 'while':
            cond, step = self._ip_eval(header[1], step, pc, sort=z3.BoolSort())
            if not z3.is_bool(cond):
                raise _Unchecked("the loop condition is not Boolean")
            return step, [cond]
        if header[0] == 'for':
            var = header[1]
            lo, hi = bounds
            index = z3.FreshInt(var)
            env = dict(step.env)
            env[var] = index
            types = dict(step.types)
            types[var] = PrimitiveType('Int')
            return step.but(env=env, types=types), [lo <= index, index < hi]
        _, var, source = header
        element_type = None
        source_type = self._ip_resolve(self._ip_static_type(source, entry))
        if isinstance(source_type, ListType):
            element_type = source_type.element_type if hasattr(source_type, 'element_type') else None
        element = z3.FreshConst(self._ip_sort_of(element_type), var)
        facts = []
        if isinstance(source, Symbol) and source.name in entry.seqs:
            facts.extend(self._ip_member(element, entry.seqs[source.name]))
        elif self._ip_is_callback_source(source):
            facts.extend(self._ip_callback_facts(source, element, entry, step, pc))
        else:
            if step.dirty is None:
                root = self._ip_root_name(source)
                if root is not None and root in self._ip_params and root not in self._ip_assigned:
                    seq = self._xp_tr._get_or_create_collection_seq(source)
                    if seq is not None and seq.sort() == z3.SeqSort(element.sort()):
                        facts.extend(self._ip_member(element, seq))
        env = dict(step.env)
        env[var] = element
        types = dict(step.types)
        types[var] = element_type
        return step.but(env=env, types=types), facts

    @staticmethod
    def _ip_member(element, seq):
        index = z3.FreshInt('idx')
        return [index >= 0, index < z3.Length(seq), element == seq[index]]

    @staticmethod
    def _ip_sort_of(typ):
        if isinstance(typ, PrimitiveType):
            if typ.name == 'Bool':
                return z3.BoolSort()
            if typ.name in ('Float', 'F32', 'F64'):
                return z3.RealSort()
        return z3.IntSort()

    def _ip_callback_facts(self, source, element, entry: _IState, step: _IState, pc) -> List[Any]:
        """What a desugared callback's @callback-assume says about each element it is handed."""
        tr = self._xp_tr
        sig = tr.imported_defs.functions.get(source[0].name)
        args = list(source.items[1:])
        facts = []
        for assumption in getattr(sig, 'callback_assumptions', []) or []:
            callback_param = getattr(assumption, 'callback_param', None)
            params = [p for p in sig.params if p != callback_param]
            if len(params) != len(args):
                continue
            expr = getattr(assumption, 'assumption', None)
            if expr is None:
                continue
            probe_types = dict(zip(sig.params, sig.param_types))
            probe = _IState({}, probe_types, {}, None, None)
            if step.dirty is not None and self._ip_state_reads(expr, probe):
                continue    # a fact about the state the walk can no longer vouch for
            param_map = {'$callback-arg': element}
            try:
                for param, arg in zip(params, args):
                    param_map[param], entry = self._ip_eval(arg, entry, pc)
            except _Bail:
                continue
            if not self._xp_closed_over(expr, set(param_map)):
                continue
            saved = {n: tr.variables.get(n, _MISSING) for n in param_map}
            start = len(tr.constraints)
            try:
                tr.variables.update(param_map)
                term = tr.translate_expr(expr)
            except z3.Z3Exception:
                term = None
            finally:
                del tr.constraints[start:]
                tr.definedness_constraints.difference_update(
                    {i for i in tr.definedness_constraints if i >= start})
                for n, previous in saved.items():
                    if previous is _MISSING:
                        tr.variables.pop(n, None)
                    else:
                        tr.variables[n] = previous
            if term is not None and z3.is_bool(term):
                facts.append(term)
        return facts

    def _ip_havoc(self, st: _IState, names, pushed, opaque: bool) -> _IState:
        tr = self._xp_tr
        env = dict(st.env)
        for name in names:
            old = env[name]
            fresh = self._ip_opaque(old.sort()) if opaque else z3.FreshConst(old.sort(), name)
            env[name] = fresh
            typ = self._ip_resolve(st.types.get(name))
            if isinstance(typ, RangeType) and fresh.sort() == z3.IntSort():
                bounds = typ.bounds
                if bounds.min_val is not None:
                    self._xp_axioms.append(fresh >= bounds.min_val)
                if bounds.max_val is not None:
                    self._xp_axioms.append(fresh <= bounds.max_val)
            elif isinstance(typ, PrimitiveType) and typ.name.startswith('U') and fresh.sort() == z3.IntSort():
                self._xp_axioms.append(fresh >= 0)
        seqs = dict(st.seqs)
        for name in pushed:
            if name in seqs:
                sort = seqs[name].sort()
                seqs[name] = self._ip_opaque(sort) if opaque else z3.FreshConst(sort, name)
        return st.but(env=env, seqs=seqs)

    def _ip_unknown_within(self, loop, reason: str) -> None:
        """Every invariant of `loop` and of loops inside it not yet decided is unknown."""
        def walk(node):
            if not isinstance(node, SList):
                return
            for condition in self._ip_sites.get(id(node), []):
                self._ip_set_unknown(self._ip_outcomes[id(condition)], reason)
            for item in node.items:
                walk(item)
        walk(loop)

    def _ip_set_unknown(self, outcome: InvariantOutcome, reason: str, status: str = 'unknown') -> None:
        if outcome.status in ('pending', 'proved'):
            outcome.status = status
            outcome.message = self._ip_unchecked_message(outcome.expr, reason)
            outcome.counterexample = None

    # ------------------------------------------------------------------
    # Solving
    # ------------------------------------------------------------------

    def _ip_decide(self, outcome: InvariantOutcome, claim, st: _IState, failure: str) -> None:
        """Check `claim` under everything the walk has established; record a failure."""
        if outcome.status != 'pending':
            return
        if self._ip_time_spent:
            self._ip_set_unknown(outcome, "not checked: the time budget went on an earlier check")
            return
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)
        facts = list(self._ip_context) + list(self._xp_axioms)
        for fact in facts:
            solver.add(fact)
        for fact in self._ip_local:
            solver.add(fact)
        solver.add(z3.Not(claim))
        result = solver.check()
        if result == z3.unsat:
            if len(facts) != self._ip_consistent_upto:
                if self._axioms_are_contradictory(facts):
                    self._ip_set_unknown(outcome, "the verification context is inconsistent")
                    return
                self._ip_consistent_upto = len(facts)
            return      # holds; the caller decides what that makes the invariant
        if result == z3.sat:
            model = solver.model()
            if self._ip_depends_on_opaque(claim, facts + list(self._ip_local)):
                self._ip_set_unknown(outcome, "it depends on something the analysis could not follow")
                return
            outcome.status = 'failed'
            outcome.message = f"loop invariant {failure}: {outcome.text}"
            outcome.counterexample = self._ip_counterexample(outcome.expr, st, model)
            return
        self._ip_time_spent = True
        self._ip_set_unknown(outcome, "the solver timed out", status='timeout')

    def _ip_depends_on_opaque(self, claim, facts) -> bool:
        """True if the claim, or a fact linked to it through shared constants,
        mentions a value the walk could not follow. A counterexample through
        one is no evidence (#69)."""
        def own(consts):
            # A path condition's guard is shared by everything under it and
            # says nothing about values.
            return {c for c in consts if not c.startswith(('iteration!', 'alive!'))}
        names = own(self._ip_constants(claim))
        linked = [(f, own(self._ip_constants(f))) for f in facts]
        grew = True
        while grew:
            grew = False
            for fact, consts in linked:
                if consts & names and not consts <= names:
                    names |= consts
                    grew = True
        return any(name.startswith(_OPAQUE) for name in names)

    @staticmethod
    def _ip_constants(term) -> set:
        seen, out = set(), set()
        stack = [term]
        while stack:
            node = stack.pop()
            key = node.get_id()
            if key in seen:
                continue
            seen.add(key)
            if z3.is_const(node) and node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                out.add(node.decl().name())
            stack.extend(node.children())
        return out

    @staticmethod
    def _ip_has_opaque(term) -> bool:
        seen = set()
        stack = [term]
        while stack:
            node = stack.pop()
            key = node.get_id()
            if key in seen:
                continue
            seen.add(key)
            if z3.is_const(node) and node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                if node.decl().name().startswith(_OPAQUE):
                    return True
            stack.extend(node.children())
        return False

    def _ip_counterexample(self, expr, st: _IState, model) -> Dict[str, str]:
        names = set()

        def walk(node):
            if isinstance(node, Symbol):
                names.add(node.name)
            elif isinstance(node, SList):
                for item in node.items:
                    walk(item)

        walk(expr)
        out = {}
        for name in sorted(names):
            term = st.seqs.get(name)
            if term is None:
                term = st.env.get(name)
            if term is None:
                continue
            try:
                out[name] = str(model.eval(term, model_completion=True))
            except z3.Z3Exception:
                continue
        return out

    # ------------------------------------------------------------------
    # Where a proved invariant may be used
    # ------------------------------------------------------------------

    def _ip_assumable(self, outcome: InvariantOutcome, body) -> bool:
        """True if the main verifier may assert this invariant where its loop ends.

        It is asserted about each name's value at that point, but a list the
        walk tracked has one sequence for the whole function, and a read of
        collection state one term for it: those are only right about the
        loop's exit if nothing after the loop changes them.
        """
        loop = outcome.loop
        if self._ip_loop_depth.get(id(loop)) != 0:
            return False
        if self._needs_array_encoding([outcome.expr]):
            return False
        after = self._ip_after(body, loop)
        tracked_read = {s.name for s in self._ip_quantifier_sources(outcome.expr)
                        if isinstance(s, Symbol) and s.name in self._ip_tracked}
        for node in after:
            if is_form(node, 'list-push') and len(node) >= 2 and isinstance(node[1], Symbol) \
                    and node[1].name in tracked_read:
                return False
        if outcome.reads_state:
            if any(self._ip_call_effect(n) is not None for n in after if isinstance(n, SList)
                   and len(n) > 0 and isinstance(n[0], Symbol) and n[0].name != 'c-inline') \
                    or any(is_form(n, 'c-inline') for n in after):
                return False
        return True

    def _ip_after(self, body, loop) -> List[Any]:
        """Call-shaped nodes that run after `loop`, in pre-order."""
        out: List[Any] = []
        state = {'past': False}

        def walk(node):
            if node is loop:
                state['past'] = True
                return
            if not isinstance(node, SList) or len(node) == 0:
                return
            if state['past']:
                out.extend(self._ip_call_nodes_all(node))
                return
            for item in node.items:
                walk(item)

        walk(body)
        return out
