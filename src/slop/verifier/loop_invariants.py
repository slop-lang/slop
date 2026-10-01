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
    PrimitiveType, RangeType, RecordType, ListType, EnumType,
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
    'all-elements-satisfy', 'any-element-satisfies', '@',
))

# Builtins exact_push refuses - division, whose model has no program points
# for a divisor's obligation, and string-concat - which change nothing and
# read no collection state. The main verifier's string axioms describe the
# latter (_generate_string_operation_axioms), and so do this check's.
_PURE_OPERATORS = frozenset(('/', '%', 'mod', 'div', 'string-concat'))


def _is_annotation(name: str) -> bool:
    """`@loop-invariant` and its kind, but not `@`, which indexes a collection."""
    return name.startswith('@') and len(name) > 1

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
    exits_before: bool = False  # a `return` can run before the loop: assume it only where none did
    asserted: bool = False      # the main verifier stated it
    unused: str = ''            # why a proved invariant is not stated, if it is not
    # A postcondition or property checked at a `return` the main model leaves
    # to the walk (ContractVerifier._exit_plan): `site` is that return.
    kind: str = 'invariant'     # invariant | post | property
    site: Any = None
    name: Optional[str] = None  # a named property's name
    visited: bool = False       # the walk reached the return and checked it

    @property
    def text(self) -> str:
        return pretty_print(self.expr)

    @property
    def what(self) -> str:
        """How a message names the claim."""
        if self.kind == 'post':
            return 'postcondition'
        if self.kind == 'property':
            return f"property '{self.name}'" if self.name else 'property'
        return 'loop invariant'

    @property
    def where(self) -> str:
        return f" at the return on line {getattr(self.site, 'line', '?')}" if self.site is not None else ''


@dataclass
class InvariantReport:
    outcomes: List[InvariantOutcome] = field(default_factory=list)
    misplaced: List[Any] = field(default_factory=list)
    # Postconditions and properties at the returns the walk checks.
    exits: List[InvariantOutcome] = field(default_factory=list)

    @property
    def exits_failed(self) -> List[InvariantOutcome]:
        return [o for o in self.exits if o.status == 'failed']

    @property
    def exits_unchecked(self) -> List[InvariantOutcome]:
        return [o for o in self.exits if o.status in ('unknown', 'timeout')]

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
                               in_callbacks, exits=None) -> InvariantReport:
        """Check the invariants at `sites`, and the contract at each walked return.

        `exits`, if given, is a dict: `walked` (ids of the returns the main
        model leaves out - ContractVerifier._exit_plan), `returns` (those
        nodes), `posts`, `properties` ((name, expr) pairs) and `return_type`.
        Every postcondition and property is checked where each walked return
        leaves the function, with $result bound to the value it returns.
        """
        report = InvariantReport()
        exits = exits or {}
        self._ip_outcomes: Dict[int, InvariantOutcome] = {}
        self._ip_sites: Dict[int, List[Any]] = {}
        self._ip_walked = set(exits.get('walked', ()))
        self._ip_assumptions = list(exits.get('assumptions', []))
        # Every name a set! or a push changes, by its root.
        self._ip_changed = self._ip_changed_roots(body)
        self._ip_exit_scope = self._ip_binders_around(body) if self._ip_walked else {}
        self._ip_return_type = exits.get('return_type')
        # Per walked return, the claims to check there.
        self._ip_exit_outcomes: Dict[int, List[InvariantOutcome]] = {}
        claims = [('post', None, post) for post in exits.get('posts', [])]
        claims += [('property', name, expr) for name, expr in exits.get('properties', [])]
        for ret in exits.get('returns', []):
            for kind, name, expr in claims:
                outcome = InvariantOutcome(expr, None, kind=kind, site=ret, name=name)
                self._ip_exit_outcomes.setdefault(id(ret), []).append(outcome)
                report.exits.append(outcome)
        self._ip_all_conditions = ([c for _, conditions in sites for c in conditions]
                                   + [expr for _, _, expr in claims])
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
        if not self._ip_outcomes and not report.exits:
            return report

        tr = Z3Translator(self.type_env, self.filename, self.function_registry,
                          self.imported_defs, use_array_encoding=False, use_seq_encoding=True)
        tr.use_quantifier_patterns = False
        tr.structural_contains = True
        saved = {name: getattr(self, name, _MISSING)
                 for name in ('_xp_tr', '_xp_axioms', '_xp_bound')}
        self._xp_tr = tr
        self._ip_return_sort = self._ip_sort_of(self._ip_resolve(self._ip_return_type))
        self._xp_axioms: List[Any] = []
        self._xp_bound: List[str] = []
        self._ip_time_spent = False
        self._ip_loop_depth: Dict[int, int] = {}
        self._ip_depth = 0
        self._ip_consistent: Dict[Any, bool] = {}
        # Hypotheses of the iterations being walked - an invariant assumed at
        # the top of the body, the loop's condition, what is known of its
        # element - asserted only in checks made while that iteration is walked.
        self._ip_local: List[Any] = []
        # Constants standing for values the walk over-approximates without
        # making them opaque: what a loop may have left in a name, an element
        # of a collection nothing is known about. An invariant's step is meant
        # to fail through them; a postcondition at a return is not (#69).
        self._ip_havocked: set = set()
        # Everything the preconditions give is stated under this: an invariant
        # or a postcondition is checked with it, a property - which holds with
        # no precondition, as the main property solver has it - without.
        self._ip_pre = z3.FreshBool('pre')
        try:
            env, types = self._ip_declare_parameters(tr, params)
            self._ip_params = set(env)
            self._ip_param_terms = dict(env)
            self._ip_binders = self._ip_binder_counts(body)
            self._ip_assigned = self._ip_assigned_names(body)
            self._ip_addr_taken = self._ip_addresses_taken(body)
            self._ip_tracked = self._ip_tracked_lists(body, set(env))
            given = []
            for _, pre in preconditions:
                term = tr.translate_expr(pre)
                if term is None or not z3.is_bool(term):
                    self._ip_give_up(f"the precondition {pretty_print(pre)} does not translate")
                    return self._ip_finish(report, body)
                given.append(z3.Implies(self._ip_pre, term))
            for _, inv in self._collect_parameter_invariants(params):
                term = tr.translate_expr(inv)
                if term is not None and z3.is_bool(term):
                    given.append(term)
            self._ip_context = ([c for i, c in enumerate(tr.constraints)
                                 if i not in tr.definedness_constraints]
                                + given + self._ip_parameter_field_ranges(tr, env, types))
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
        for outcome in report.exits:
            # Checked every time the walk got there, and held each time.
            if outcome.status == 'pending' and outcome.visited:
                outcome.status = 'proved'
            elif outcome.status == 'pending':
                self._ip_set_unknown(outcome, "the return is not reached by the analysis")
        for outcome in report.outcomes:
            if outcome.status == 'proved' and outcome.loop is not None:
                outcome.assumable = self._ip_assumable(outcome, body)
        return report

    def _ip_give_up(self, reason: str) -> None:
        for outcome in self._ip_every_outcome():
            if outcome.status == 'pending':
                outcome.status = 'unknown'
                outcome.message = self._ip_unchecked_text(outcome, reason)

    def _ip_every_outcome(self) -> List[InvariantOutcome]:
        return (list(self._ip_outcomes.values())
                + [o for outcomes in self._ip_exit_outcomes.values() for o in outcomes])

    @staticmethod
    def _ip_unchecked_message(expr, reason: str) -> str:
        return f"could not check loop invariant: {pretty_print(expr)} ({reason})"

    @staticmethod
    def _ip_unchecked_text(outcome: InvariantOutcome, reason: str) -> str:
        return f"could not check {outcome.what}{outcome.where}: {outcome.text} ({reason})"

    def _ip_parameter_field_ranges(self, tr, env, types) -> List[Any]:
        """The declared ranges of each record parameter's own fields.

        Taken as given about the arguments, as the main verifier takes a
        parameter's range. Not stated for every record: a field accessor is
        named by the field alone, shared by every type with a field of that
        name, and C does not check a range when a record is built - a
        universal range axiom would contradict a record the body makes.
        """
        facts = []
        for name, typ in types.items():
            record = self._ip_resolve(typ)
            if not isinstance(record, RecordType):
                continue
            for field_name, field_type in record.fields.items():
                bounds = self._ip_resolve(field_type)
                if not isinstance(bounds, RangeType):
                    continue
                access = tr._translate_field_for_obj(env[name], field_name)
                if access is None or access.sort() != z3.IntSort():
                    continue
                if bounds.bounds.min_val is not None:
                    facts.append(access >= bounds.bounds.min_val)
                if bounds.bounds.max_val is not None:
                    facts.append(access <= bounds.bounds.max_val)
        return facts

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

    def _ip_addresses_taken(self, body) -> set:
        """Locals something other than the walk may write: those whose address
        is taken, which a call handed it may write, and those a lambda
        assigns, which calling the lambda - by any name - does."""
        names = set()

        def walk(node, in_fn=False):
            if not isinstance(node, SList) or len(node) == 0 or is_form(node, 'quote'):
                return
            if is_form(node, 'fn'):
                for item in node.items[1:]:
                    walk(item, True)
                return
            if in_fn and is_form(node, 'set!') and len(node) >= 2 and isinstance(node[1], Symbol):
                names.add(node[1].name.split('.')[0])
            if is_form(node, 'addr') and len(node) >= 2:
                # The root of the place: `(. r n)`, `r.n`, `(@ xs i)`,
                # `(deref p)` all hand out storage belonging to that name.
                place = node[1]
                while isinstance(place, SList) and len(place) >= 2 \
                        and isinstance(place[0], Symbol) and place[0].name in ('.', '@', 'deref'):
                    place = place[1]
                if isinstance(place, Symbol):
                    names.add(place.name.split('.')[0])
            for item in node.items:
                walk(item, in_fn)

        walk(body)
        return names

    def _ip_binder_counts(self, body) -> Dict[str, int]:
        """How many times each name is bound, by any form that binds one."""
        counts: Dict[str, int] = {}

        def bind(name):
            if isinstance(name, Symbol):
                counts[name.name] = counts.get(name.name, 0) + 1

        def walk(node):
            if not isinstance(node, SList) or len(node) == 0:
                return
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head == 'quote':
                return
            if head in ('let', 'let*') and len(node) >= 2 and isinstance(node[1], SList):
                for binding in node[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        name = self._binding_name(binding)
                        if name:
                            counts[name] = counts.get(name, 0) + 1
            elif head in ('for-each', 'for', 'forall', 'exists', 'with-arena') \
                    and len(node) >= 2 and isinstance(node[1], SList) and len(node[1]) >= 1:
                binder = node[1][0]
                if isinstance(binder, SList):
                    for item in binder.items:
                        bind(item)
                else:
                    bind(binder)
            elif head == 'match':
                for clause in node.items[2:]:
                    if isinstance(clause, SList) and len(clause) >= 1:
                        pattern = clause[0]
                        if isinstance(pattern, SList):
                            for item in pattern.items[1:]:
                                bind(item)
            elif head == 'fn' and len(node) >= 2 and isinstance(node[1], SList):
                for param in node[1].items:
                    bind(param[0] if isinstance(param, SList) and len(param) >= 1 else param)
            for item in node.items:
                walk(item)

        walk(body)
        return counts

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
        binders = self._ip_binder_counts(body)
        for name, bindings in candidates.items():
            # Any other binding of the name - a shadowing let*, a quantifier's
            # or a pattern's binder - is a different value under the same name.
            if bindings != 1 or name in params or binders.get(name, 0) != 1 \
                    or name in self._ip_addr_taken:
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

    def _ip_loop_writes(self, loop) -> Tuple[set, set, bool]:
        """What a loop may write, its header included - a condition is
        evaluated every iteration."""
        return self._ip_writes(loop.items[1:])

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

    def _ip_unwalked_return(self, items) -> bool:
        """A `return` under `items` that is not one of the walked exits."""
        def walk(node) -> bool:
            if not isinstance(node, SList) or len(node) == 0:
                return False
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head in ('quote', 'fn'):
                return False
            if head == 'return' and id(node) not in self._ip_walked:
                return True
            return any(walk(item) for item in node.items)
        return any(walk(item) for item in items)

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

    @staticmethod
    def _ip_plain_assignment(node) -> bool:
        """`(set! name value)` of a local, as opposed to a write through a place."""
        return (len(node) == 3 and isinstance(node[1], Symbol)
                and '.' not in node[1].name.strip('.'))

    def _ip_call_effect(self, call) -> Optional[str]:
        """What a call in the body may change, as a description; None if nothing."""
        head = call[0].name if isinstance(call[0], Symbol) else None
        if head is None:
            return "a call through a computed function"
        where = f"{head} (line {getattr(call, 'line', '?')})"
        if head == 'set!':
            return None if self._ip_plain_assignment(call) else f"the assignment at line {getattr(call, 'line', '?')}"
        if head == 'list-push' and len(call) >= 2 and isinstance(call[1], Symbol) \
                and call[1].name in self._ip_tracked:
            return None
        if self._ip_is_user_function(head):
            # A function not declared @pure may reach state through what it is
            # handed, and through C it may reach state it is not handed.
            return None if self._xp_callee_is_pure(head, self._xp_tr) else where
        if head in _MUTATORS:
            return where
        if head in _ALLOCATORS or head in _NEUTRAL_HEADS or head in _EXTRA_STATE_READS \
                or head in _PURE_OPERATORS:
            return None     # a user function of the same name was handled above
        if head in ('record-new', 'union-new', 'fn', 'quote', 'cast', 'forall', 'exists',
                    'implies', 'if', 'cond', 'when', 'match', 'do', 'let', 'let*', 'set!',
                    'return', 'break', 'continue', '@loop-invariant', 'and', 'or', 'not'):
            return None
        if _is_annotation(head):
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
            if name == 'quote' or _is_annotation(name):
                return
            if name in ('let', 'let*') and len(node) >= 2 and isinstance(node[1], SList):
                for binding in node[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        walk(binding[-1])
                for item in node.items[2:]:
                    walk(item)
                return
            if name in ('for-each', 'forall', 'exists') and len(node) >= 2 \
                    and isinstance(node[1], SList):
                # A desugared callback's source is the call minus its lambda:
                # the callee runs, and what it may change is its own effect.
                binder = node[1]
                if len(binder) >= 2:
                    walk(binder[1])
                for item in node.items[2:]:
                    walk(item)
                return
            if name == 'set!' and not self._ip_plain_assignment(node):
                # A write through a field, an index or a pointer changes state
                # the walk reads through uninterpreted terms.
                out.append(node)
                for item in node.items[1:]:
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
        # Names for a value built in place (_ip_exit_formula): a length read
        # through one is of a list no earlier change reached.
        fresh_roots = set(getattr(self, '_ip_fresh_roots', ()))

        def is_fresh(node, fresh) -> bool:
            while is_form(node, '.') and len(node) >= 2:
                node = node[1]
            return isinstance(node, Symbol) and node.name.split('.')[0] in fresh

        def type_of(node, bound):
            if isinstance(node, Symbol) and node.name in bound:
                return bound[node.name]
            if is_form(node, '.') and len(node) >= 3 and isinstance(node[2], Symbol):
                base = self._ip_resolve(type_of(node[1], bound))
                return base.fields.get(node[2].name) if isinstance(base, RecordType) else None
            return self._ip_static_type(node, st)

        def walk(node, bound, fresh=frozenset()):
            if isinstance(node, Symbol):
                n = node.name
                if '.' in n.strip('.'):
                    parts = n.split('.')
                    typ = bound[parts[0]] if parts[0] in bound else st.types.get(parts[0])
                    for field_name in parts[1:]:
                        base = self._ip_resolve(typ)
                        if not isinstance(base, RecordType):
                            reads.append(f"the field path {n}")
                            break
                        typ = base.fields.get(field_name)
                return
            if not isinstance(node, SList) or len(node) == 0:
                return
            head = node[0]
            if not isinstance(head, Symbol):
                for item in node.items:
                    walk(item, bound, fresh)
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
                        walk(source, bound, fresh)
                        collection = self._ip_resolve(type_of(source, bound))
                        element = getattr(collection, 'element_type', None)
                inner_fresh = fresh
                if len(binder) >= 1 and isinstance(binder[0], Symbol):
                    inner = dict(bound)
                    inner[binder[0].name] = element
                    inner_fresh = fresh - {binder[0].name}
                for item in node.items[2:]:
                    walk(item, inner, inner_fresh)
                return
            if name == 'match' and len(node) >= 3:
                walk(node[1], bound, fresh)
                scrutinee = self._ip_resolve(type_of(node[1], bound))
                from_fresh = is_fresh(node[1], fresh)
                for clause in node.items[2:]:
                    if not isinstance(clause, SList) or len(clause) < 1:
                        continue
                    inner = dict(bound)
                    arm_fresh = set(fresh) - {b.name for b in (clause[0].items[1:]
                                              if isinstance(clause[0], SList) else [])
                                              if isinstance(b, Symbol)}
                    if from_fresh and isinstance(clause[0], SList):
                        arm_fresh |= {b.name for b in clause[0].items[1:] if isinstance(b, Symbol)}
                    pattern = clause[0]
                    if isinstance(pattern, SList) and len(pattern) >= 2 and isinstance(pattern[0], Symbol):
                        tag = pattern[0].name.lstrip("'")
                        for index, binder in enumerate(pattern.items[1:]):
                            if isinstance(binder, Symbol):
                                inner[binder.name] = self._ip_payload_type(scrutinee, tag, index)
                    for item in clause.items[1:]:
                        walk(item, inner, frozenset(arm_fresh))
                return
            if name == 'list-len' and len(node) >= 2 and is_fresh(node[1], fresh):
                return
            if name in ('list-len', 'list-contains') and len(node) >= 2 \
                    and isinstance(node[1], Symbol) and node[1].name in tracked:
                for item in node.items[2:]:
                    walk(item, bound, fresh)
                return
            if name in _STATE_READS or name in _EXTRA_STATE_READS:
                reads.append(name)
            elif name == '.':
                if len(node) >= 2:
                    base = self._ip_resolve(type_of(node[1], bound))
                    if not isinstance(base, RecordType):
                        reads.append(f"the field {pretty_print(node)}")
                    walk(node[1], bound, fresh)
                return
            elif self._ip_is_user_function(name):
                if self._xp_callee_is_pure(name, self._xp_tr) and not self._xp_params_are_values(name):
                    reads.append(f"{name}, which is handed a collection")
            for item in node.items[1:]:
                walk(item, bound, fresh)

        walk(expr, {}, frozenset(fresh_roots))
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

    def _ip_effect(self, st: _IState, effect: Optional[str]) -> _IState:
        """The state after something that may change collection state.

        A local whose address was taken may have been written through it,
        which the walk cannot see - so it becomes opaque at every such point.
        """
        if effect is None:
            return st
        env = dict(st.env)
        for name in self._ip_addr_taken:
            if name in env:
                env[name] = self._ip_opaque(env[name].sort())
        return st.but(env=env, dirty=st.dirty or effect)

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
            return self._ip_opaque(sort), self._ip_effect(st, effect)

    def _ip_eval_term(self, expr, st: _IState, pc, invariant):
        if not invariant:
            impure = self._ip_impure_call_in_quantifier(expr)
            if impure is not None:
                raise _NoTranslation(f"{impure} is called inside a quantifier or match arm")
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
        if effect is not None:
            # A local a call may write, read in the same term, may be read
            # after the call - an `if` arm, the right of an `and`.
            reads = reads + [f"{n}, which a call may write" for n in sorted(self._ip_addr_taken)
                             if self._ip_mentions(expr, n)]
        stale = st.dirty or (effect if reads else None)
        if reads and stale:
            if invariant:
                raise _Unchecked(f"it reads {reads[0]}, which {stale} may change")
            term = self._ip_translate(expr, st, pc, instantiate=False, pin=False)
            return self._ip_opaque(term.sort()), self._ip_effect(st, effect)
        term = self._ip_translate(expr, st, pc, instantiate=True, pin=True, invariant=invariant)
        return term, self._ip_effect(st, effect)

    def _ip_check_pure(self, expr):
        """Refuse statement forms inside a term; a fresh collection is fine,
        and so is a `match` whose arms are terms."""
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                if head.name in ('let', 'let*', 'do', 'when', 'set!', 'list-push'):
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
            # What the main verifier knows of strings: a concatenation starts
            # with its first operand, keeps any prefix that operand had, and
            # one literal starts with another when its text does.
            if self._ip_mentions_any(expr, ('string-concat', 'starts-with')) or isinstance(expr, String) \
                    or self._ip_has_string_literal(expr):
                self._xp_axioms.extend(self._generate_string_operation_axioms(
                    expr, list(self._ip_all_conditions), tr))
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
        if isinstance(head, Symbol) and head.name == 'match':
            # The arms read names their patterns bind, which nothing here has
            # a value for; only the scrutinee is evaluated as it stands.
            if len(expr) >= 2:
                self._ip_pin(expr[1], pc)
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
            fields = []
            for item in expr.items[2:]:
                if isinstance(item, SList) and len(item) >= 2 and isinstance(item[0], Symbol):
                    fields.append((item[0].name, tr.translate_expr(item[1])))
            # Each field's value, where the accessor holds a value of that
            # sort. Accessors are named by field alone and their sort is a
            # guess from the name; a fact across sorts would be false - and
            # a record missing one is less than the program built, so it is
            # opaque rather than a source of counterexamples.
            probe = z3.FreshConst(z3.IntSort(), 'record')
            complete = all(value is not None
                           and tr._translate_field_for_obj(probe, field_name).sort() == value.sort()
                           for field_name, value in fields)
            const = probe if complete else self._ip_opaque(z3.IntSort())
            for field_name, value in fields:
                access = tr._translate_field_for_obj(const, field_name)
                if value is not None and access is not None and access.sort() == value.sort():
                    self._xp_axioms.append(z3.Implies(pc, access == value))
            # A list literal written as a field is that long when the record
            # is built; a push through the field later is a change of state
            # like any other (_ip_call_effect), after which a length read
            # through it is not trusted.
            for item in expr.items[2:]:
                if isinstance(item, SList) and len(item) >= 2 and tr.is_list_literal(item[1]):
                    length = tr.list_literal_length(item[1], tr.translate_expr(item[1]))
                    if length is not None:
                        self._xp_axioms.append(z3.Implies(pc, length))
            tr._pinned_terms[id(expr)] = const
        elif name == 'union-new':
            if len(expr) < 3 or not isinstance(expr[2], Symbol):
                raise _Bail("malformed union-new")
            self._xp_pin_variant(expr, expr[2].name, expr.items[3:], pc)
        elif name in _OPTION_RESULT_CONSTRUCTORS:
            self._xp_pin_variant(expr, name, expr.items[1:], pc)
        elif tr.is_list_literal(expr):
            return      # a handle of its own, with its length (the translator's)
        elif name in _ALLOCATORS:
            natural = tr.translate_expr(expr)
            sort = natural.sort() if natural is not None else z3.IntSort()
            tr._pinned_terms[id(expr)] = z3.FreshConst(sort, 'alloc')
        elif self._xp_is_builtin(name, tr) or name in _EXTRA_STATE_READS \
                or (name in _PURE_OPERATORS and not self._ip_is_user_function(name)) \
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
        for name in sorted(self._ip_addr_taken):
            if self._ip_mentions(condition, name):
                raise _Unchecked(f"it names {name}, which a call may write (its address is taken, "
                                 "or a lambda assigns it)")
        inner_binders = self._ip_binder_counts(condition)
        for source in self._ip_quantifier_sources(condition):
            root = self._ip_root_name(source)
            if root is not None and root in inner_binders:
                raise _Unchecked(f"it quantifies over {pretty_print(source)}, "
                                 "a name the invariant itself binds")
            if isinstance(source, Symbol) and source.name in st.seqs:
                continue
            if root is None:
                raise _Unchecked(f"it quantifies over {pretty_print(source)}, which is not a named collection")
            if not self._ip_stable_parameter(root, st):
                raise _Unchecked(f"it quantifies over {pretty_print(source)}, "
                                 "whose name does not always denote the same collection")
        impure = self._ip_impure_call_in_quantifier(condition)
        if impure is not None:
            raise _Unchecked(f"it calls {impure}, which is not @pure, inside a quantifier or match arm")
        term, _ = self._ip_eval(condition, st, pc, invariant=True)
        if z3.is_int(term):
            term = self._ensure_bool(term)     # as the main verifier reads it
        if not z3.is_bool(term):
            raise _Unchecked("it is not a Boolean condition")
        return term, list(self._ip_obligations)

    def _ip_check_exit(self, stmt, value, st: _IState, pc) -> None:
        """Check the contract where a walked `return` leaves the function.

        $result is the value it returns, a `mut` parameter whatever it holds
        here. The iteration's hypotheses (`_ip_local`) apply: an enclosing
        loop's invariant, its condition, what is known of its element - and
        so does every @assume, which the main verifier trusts of every run.
        """
        env, types, seqs = dict(st.env), dict(st.types), dict(st.seqs)
        fresh = False
        if value is not None:
            env['$result'] = value
            types['$result'] = self._ip_return_type
            if isinstance(stmt[1], Symbol) and stmt[1].name in st.seqs:
                seqs['$result'] = st.seqs[stmt[1].name]
            fresh = self._ip_fresh_value(stmt[1], st)
        at = st.but(env=env, types=types, seqs=seqs)
        hypotheses = []
        if value is not None and self._xp_tr.is_list_literal(stmt[1]):
            length = self._xp_tr.list_literal_length(stmt[1], value)
            if length is not None:
                hypotheses.append(length)
        # A contract names parameters, but here a local may have taken one's
        # name - `(for-each (k xs) (return k))` - and the walk's scope is the
        # return site's.
        shadowed = self._ip_exit_scope.get(id(stmt), frozenset())
        assumed, assume_note = [], None
        for assumption in self._ip_assumptions:
            if value is None and self._ip_mentions(assumption, '$result'):
                continue
            hidden = sorted(shadowed & self._ip_free_roots(assumption))
            # The main model reads an @assume where the body ends; about a
            # name the body changes, that is not what holds here.
            changed = sorted(self._ip_changed & self._ip_free_roots(assumption))
            try:
                if hidden:
                    raise _Unchecked(f"it names {hidden[0]}, which a local binding shadows here")
                if changed:
                    raise _Unchecked(f"it names {changed[0]}, which the body changes")
                term, obligations = self._ip_exit_formula(assumption, at, pc, fresh)
                assumed.append(z3.And(term, *obligations))
            except (_Unchecked, _Bail) as unchecked:
                # A trusted fact the walk cannot state here: a failure may be
                # one it rules out.
                assume_note = f"the @assume {pretty_print(assumption)} does not translate here ({unchecked})"
        for outcome in self._ip_exit_outcomes[id(stmt)]:
            if outcome.status != 'pending':
                continue
            outcome.visited = True
            if value is None and self._ip_mentions(outcome.expr, '$result'):
                self._ip_set_unknown(outcome, "the return has no value")
                continue
            hidden = sorted(shadowed & self._ip_free_roots(outcome.expr))
            if hidden:
                self._ip_set_unknown(outcome, f"it names {hidden[0]}, which a local binding "
                                              "shadows at this return")
                continue
            try:
                goal, obligations = self._ip_exit_formula(outcome.expr, at, pc, fresh)
            except _Unchecked as unchecked:
                self._ip_set_unknown(outcome, str(unchecked))
                continue
            # A contract's own side conditions are assumed, as the main
            # verifier assumes them of a @post.
            self._ip_decide(outcome, z3.Implies(z3.And(pc, st.alive, *obligations, *hypotheses,
                                                       *assumed), goal),
                            at, '', pc, goal=goal)
            if outcome.status == 'pending' and assumed and not self._ip_path_open(
                    outcome, [pc, st.alive, *hypotheses, *assumed]) and self._ip_path_open(
                    outcome, [pc, st.alive, *hypotheses]):
                # Held only because an @assume rules the return out: a
                # trusted claim is not evidence that a path is dead.
                self._ip_set_unknown(outcome, "an @assume contradicts the path to this return")
            if outcome.status == 'failed' and assume_note is not None:
                outcome.status = 'unknown'
                outcome.message = self._ip_unchecked_text(outcome, assume_note)
                outcome.counterexample = None

    @staticmethod
    def _ip_changed_roots(body) -> set:
        out = set()

        def walk(node):
            if not isinstance(node, SList) or len(node) == 0 or is_form(node, 'quote'):
                return
            head = node[0].name if isinstance(node[0], Symbol) else None
            if (head == 'set!' or head in _MUTATORS) and len(node) >= 2:
                place = node[1]
                while isinstance(place, SList) and len(place) >= 2:
                    place = place[1]
                if isinstance(place, Symbol):
                    out.add(place.name.split('.')[0])
            for item in node.items:
                walk(item)

        walk(body)
        return out

    def _ip_path_open(self, outcome: InvariantOutcome, conditions) -> bool:
        """True unless the facts rule `conditions` out (a timeout counts as open)."""
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)
        for fact in list(self._ip_context) + list(self._xp_axioms) + list(self._ip_local):
            solver.add(fact)
        if outcome.kind != 'property':
            solver.add(self._ip_pre)
        for condition in conditions:
            solver.add(condition)
        return solver.check() != z3.unsat

    @staticmethod
    def _ip_free_roots(expr) -> set:
        """The names `expr` reads that it does not bind itself - not a
        quantifier's variable, a match arm's or a let's - by the root of a
        field path (`x.f` reads x)."""
        out: set = set()

        def symbols(node) -> set:
            if isinstance(node, Symbol):
                return {node.name}
            if isinstance(node, SList):
                return {n for item in node.items for n in symbols(item)}
            return set()

        def walk(node, bound):
            if isinstance(node, Symbol):
                root = node.name.split('.')[0]
                if root not in bound:
                    out.add(root)
                return
            if not isinstance(node, SList) or len(node) == 0 or is_form(node, 'quote'):
                return
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head in ('forall', 'exists') and len(node) >= 3 and isinstance(node[1], SList):
                binder = node[1]
                for item in binder.items[1:]:
                    walk(item, bound)
                inner = bound | (symbols(binder[0]) if len(binder) >= 1 else set())
                for item in node.items[2:]:
                    walk(item, inner)
                return
            if head == 'match' and len(node) >= 2:
                walk(node[1], bound)
                for clause in node.items[2:]:
                    if isinstance(clause, SList) and len(clause) >= 1:
                        pattern = clause[0]
                        inner = bound | (symbols(SList(pattern.items[1:])) if isinstance(pattern, SList)
                                         else set())
                        for item in clause.items[1:]:
                            walk(item, inner)
                return
            if head in ('let', 'let*') and len(node) >= 2 and isinstance(node[1], SList):
                inner = set(bound)
                for binding in node[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        walk(binding[-1], inner)
                        first = (binding[1] if isinstance(binding[0], Symbol)
                                 and binding[0].name == 'mut' else binding[0])
                        if isinstance(first, Symbol):
                            inner.add(first.name)
                for item in node.items[2:]:
                    walk(item, inner)
                return
            if head == '.' and len(node) >= 2:
                walk(node[1], bound)    # the field's name is not a variable
                return
            for item in node.items[1:] if head is not None else node.items:
                walk(item, bound)

        walk(expr, frozenset())
        return out

    @staticmethod
    def _ip_binders_around(body) -> Dict[int, frozenset]:
        """For each `return` in `body`, the names bound around it: by a `let`,
        a loop's header, a match arm's pattern or a lambda's parameters."""
        out: Dict[int, frozenset] = {}

        def symbols(node) -> List[str]:
            if isinstance(node, Symbol):
                return [] if node.name in ('_', 'mut') else [node.name]
            if isinstance(node, SList):
                return [n for item in node.items for n in symbols(item)]
            return []

        def walk(node, scope):
            if not isinstance(node, SList) or len(node) == 0:
                return
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head == 'quote':
                return
            if head == 'return':
                out[id(node)] = frozenset(scope)
            if head in ('let', 'let*') and len(node) >= 2 and isinstance(node[1], SList):
                inner = set(scope)
                for binding in node[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        walk(binding[-1], inner)
                        first = (binding[1] if isinstance(binding[0], Symbol) and binding[0].name == 'mut'
                                 else binding[0])
                        if isinstance(first, Symbol):
                            inner.add(first.name)
                for item in node.items[2:]:
                    walk(item, inner)
                return
            if head in ('for-each', 'for') and len(node) >= 2 and isinstance(node[1], SList):
                binder = node[1]
                named = binder.items[:-1] if head == 'for-each' else binder.items[:1]
                names = [n for item in named for n in symbols(item)]
                for item in (binder.items[-1:] if head == 'for-each' else binder.items[1:]):
                    walk(item, scope)
                inner = set(scope) | set(names)
                for item in node.items[2:]:
                    walk(item, inner)
                return
            if head == 'match' and len(node) >= 2:
                walk(node[1], scope)
                for clause in node.items[2:]:
                    if isinstance(clause, SList) and len(clause) >= 1:
                        inner = set(scope) | set(symbols(clause[0])[1:] if isinstance(clause[0], SList)
                                                 else [])
                        for item in clause.items[1:]:
                            walk(item, inner)
                return
            if head == 'fn' and len(node) >= 2:
                inner = set(scope) | set(symbols(node[1]))
                for item in node.items[2:]:
                    walk(item, inner)
                return
            for item in node.items:
                walk(item, scope)

        walk(body, set())
        return out

    def _ip_exit_formula(self, condition, st: _IState, pc, fresh: bool):
        """A postcondition or property at a return: (term, definedness obligations).

        As _ip_formula, with $result bound. A $result built right there from
        constructors (`fresh`) holds no collection anything changed before:
        its lengths are read whatever the state, though not its elements,
        which a list literal's model does not describe.
        """
        for name in sorted(self._ip_addr_taken):
            if self._ip_mentions(condition, name):
                raise _Unchecked(f"it names {name}, which a call may write (its address is taken, "
                                 "or a lambda assigns it)")
        inner_binders = self._ip_binder_counts(condition)
        result_names = self._ip_result_names(condition) if fresh and '$result' not in st.seqs else set()
        if result_names:
            element_read = self._ip_result_element_read(condition, result_names)
            if element_read is not None:
                raise _Unchecked(f"it reads the elements of a list the return builds ({element_read})")
        for source in self._ip_quantifier_sources(condition):
            root = self._ip_root_name(source)
            if self._ip_rooted_in(source, result_names):
                continue    # a length of a list the return built (see above)
            if root is not None and root in inner_binders:
                raise _Unchecked(f"it quantifies over {pretty_print(source)}, "
                                 "a name the claim itself binds")
            if isinstance(source, Symbol) and source.name in st.seqs:
                continue
            if root is None:
                raise _Unchecked(f"it quantifies over {pretty_print(source)}, which is not a named collection")
            if not self._ip_stable_parameter(root, st):
                raise _Unchecked(f"it quantifies over {pretty_print(source)}, "
                                 "whose name does not always denote the same collection")
        impure = self._ip_impure_call_in_quantifier(condition)
        if impure is not None:
            raise _Unchecked(f"it calls {impure}, which is not @pure, inside a quantifier or match arm")
        saved = getattr(self, '_ip_fresh_roots', frozenset())
        self._ip_fresh_roots = frozenset({'$result'}) if fresh else frozenset()
        try:
            term, _ = self._ip_eval(condition, st, pc, invariant=True)
        finally:
            self._ip_fresh_roots = saved
        if z3.is_int(term):
            term = self._ensure_bool(term)
        if not z3.is_bool(term):
            raise _Unchecked("it is not a Boolean condition")
        return term, list(self._ip_obligations)

    @staticmethod
    def _ip_result_names(condition) -> set:
        """$result, and every name a `match` in `condition` binds to a part of it."""
        names = {'$result'}

        def rooted(node) -> bool:
            while is_form(node, '.') and len(node) >= 2:
                node = node[1]
            return isinstance(node, Symbol) and node.name.split('.')[0] in names

        def walk(node):
            if not isinstance(node, SList) or len(node) == 0:
                return
            if is_form(node, 'quote'):
                return
            if is_form(node, 'match') and len(node) >= 3 and rooted(node[1]):
                for clause in node.items[2:]:
                    if isinstance(clause, SList) and len(clause) >= 1 and isinstance(clause[0], SList):
                        names.update(b.name for b in clause[0].items[1:] if isinstance(b, Symbol))
            for item in node.items:
                walk(item)

        walk(condition)
        return names

    @staticmethod
    def _ip_rooted_in(node, names) -> bool:
        while is_form(node, '.') and len(node) >= 2:
            node = node[1]
        return isinstance(node, Symbol) and node.name.split('.')[0] in names

    def _ip_result_element_read(self, condition, names) -> Optional[str]:
        """An element read of a collection reached from $result, if any."""
        def walk(node):
            if not isinstance(node, SList) or len(node) == 0:
                return None
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head == 'quote':
                return None
            if head in ('list-contains', 'list-ref', '@', 'forall', 'exists') and len(node) >= 2:
                target = node[1][1] if head in ('forall', 'exists') and isinstance(node[1], SList) \
                    and len(node[1]) >= 2 else node[1]
                if self._ip_rooted_in(target, names):
                    return pretty_print(node)
            for item in node.items:
                found = walk(item)
                if found is not None:
                    return found
            return None

        return walk(condition)

    def _ip_fresh_value(self, expr, st: _IState) -> bool:
        """True if `expr` builds its value right here, holding no collection
        that existed before it: constructors all the way down, with lists
        made in place, and nothing else but scalars."""
        tr = self._xp_tr

        def scalar(node) -> bool:
            if isinstance(node, (Number, String)):
                return True
            typ = self._ip_resolve(self._ip_static_type(node, st))
            if isinstance(typ, RangeType):
                return True
            if isinstance(typ, PrimitiveType):
                return typ.name in ('Int', 'Bool', 'String', 'Float', 'F32', 'F64', 'I8', 'I16',
                                    'I32', 'I64', 'U8', 'U16', 'U32', 'U64', 'Char')
            return isinstance(typ, EnumType)

        def fresh(node) -> bool:
            if tr.is_list_literal(node) or is_form(node, 'list-new'):
                return True
            if not (isinstance(node, SList) and len(node) >= 1 and isinstance(node[0], Symbol)):
                return False
            head = node[0].name
            if self._ip_is_user_function(head):
                return False
            if head in ('some', 'ok', 'error', 'none'):
                return all(part(item) for item in node.items[1:])
            if head == 'union-new':
                return all(part(item) for item in node.items[3:])
            if head == 'record-new':
                return all(isinstance(item, SList) and len(item) >= 2 and part(item[-1])
                           for item in node.items[2:])
            return False

        def part(node) -> bool:
            return fresh(node) or scalar(node)

        return fresh(expr)

    def _ip_impure_call_in_quantifier(self, expr) -> Optional[str]:
        """A call inside a quantifier or a match arm is not pinned, so it is an
        uninterpreted function of its arguments - only right for a function
        that is one."""
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
            if head == 'match' and len(node) >= 2:
                found = walk(node[1], inside)
                if found:
                    return found
                for clause in node.items[2:]:
                    if isinstance(clause, SList):
                        for item in clause.items[1:]:
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

    def _ip_stable_parameter(self, root: Optional[str], st: _IState) -> bool:
        """True if `root` is a parameter that, here, still names the parameter.

        The translator looks a collection's sequence up by name, so a name any
        binding reuses - a `let`, a loop's or a pattern's binder - would read
        the parameter's list where the program means another.
        """
        if root is None or root not in self._ip_params or root in self._ip_assigned:
            return False
        if self._ip_binders.get(root, 0) != 0:
            return False
        term = st.env.get(root)
        return term is not None and term.eq(self._ip_param_terms[root])

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
    def _ip_mentions_any(expr, names) -> bool:
        if isinstance(expr, Symbol):
            return expr.name in names
        if isinstance(expr, SList):
            return any(InvariantProverMixin._ip_mentions_any(item, names) for item in expr.items)
        return False

    @staticmethod
    def _ip_has_string_literal(expr) -> bool:
        if isinstance(expr, String):
            return True
        if isinstance(expr, SList):
            return any(InvariantProverMixin._ip_has_string_literal(item) for item in expr.items)
        return False

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
        if _is_annotation(name):
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
            value = None
            if len(stmt) >= 2:
                value, st = self._ip_eval(stmt[1], st, pc, sort=self._ip_return_sort)
            if id(stmt) in self._ip_exit_outcomes:
                self._ip_check_exit(stmt, value, st, pc)
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
            return self._ip_effect(st, self._ip_call_effect(stmt))
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
        # What each name this let shadows held just before it was shadowed -
        # after anything an earlier initializer did to it.
        outer: Dict[str, Tuple[Any, Any, Any]] = {}
        for binding in stmt[1].items:
            if not isinstance(binding, SList) or len(binding) < 2:
                raise _Bail("malformed binding")
            bname = self._binding_name(binding)
            if bname is None:
                raise _Bail("unnamed binding")
            if bname in inner.env and bname not in outer and bname not in introduced:
                outer[bname] = (inner.env[bname], inner.types.get(bname), inner.seqs.get(bname, _MISSING))
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
            if bname in outer:
                value, typ, seq = outer[bname]
                env[bname] = value
                types[bname] = typ
                if seq is _MISSING:
                    seqs.pop(bname, None)
                else:
                    seqs[bname] = seq
            else:
                env.pop(bname, None)
                types.pop(bname, None)
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
        return self._ip_effect(state.but(env=env, types=types), effect)

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
                bound_types[binder] = self._ip_payload_type(scrutinee_type, tag, index)
            arms.append((test, self._ip_arm(body_items, st, bound_terms, bound_types,
                                            z3.And(pc, test))))
            tests.append(test)

        result = st
        for guard, arm_state in reversed(arms):
            result = self._ip_merge(guard, arm_state, result)
        return result

    def _ip_payload_type(self, scrutinee_type, tag: str, index: int = 0):
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
            return recorded[index] if index < len(recorded) else None
        if index != 0:
            return None
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
        if not isinstance(target, Symbol):
            _, st = self._ip_eval(target, st, pc, sort=z3.IntSort())
        element, st = self._ip_eval(stmt[2], st, pc, sort=z3.IntSort())
        if isinstance(target, Symbol) and target.name in st.seqs:
            if element.sort() != z3.IntSort():
                raise _Bail("a pushed element is not an Int-sorted term")
            seqs = dict(st.seqs)
            seqs[target.name] = z3.Concat(st.seqs[target.name], z3.Unit(element))
            return st.but(seqs=seqs)
        return self._ip_effect(st, self._ip_call_effect(stmt))

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
        if header is None and len(loop) >= 2 and isinstance(loop[1], SList) and len(loop[1]) >= 2:
            # A header this does not follow - a map's (k v) binder - still
            # evaluates its collection once, before the loop.
            _, st = self._ip_eval(loop[1][-1], st, pc, sort=z3.IntSort())
        if header is not None and header[0] in ('each', 'for') and reason is None \
                and any(self._ip_mentions(c, header[1]) for c in conditions):
            # On entry and after the loop the name means something else, or
            # nothing; an invariant is about the state between iterations.
            reason = f"it names the loop variable {header[1]}"
        # What the loop iterates is evaluated once, before the first iteration.
        bounds = None
        iteration_effect = None     # what each iteration may change besides the body
        if header is not None and header[0] == 'each':
            source = header[2]
            if self._ip_is_callback_source(source):
                # Its arguments are evaluated once; the callee runs around
                # every call of the callback, so its effects come before the
                # first iteration and between them.
                for arg in source.items[1:]:
                    _, st = self._ip_eval(arg, st, pc, sort=z3.IntSort())
                iteration_effect = self._ip_first_effect([source])
                st = self._ip_effect(st, iteration_effect)
                if conditions and reason is None and self._ip_contains_return(body_items):
                    # There `return` leaves the callback, not the function: the
                    # next call starts from wherever it left off.
                    reason = "return in a callback body"
            elif isinstance(source, SList):
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
                                    st, "not established on entry", pc)
        if reason is not None:
            for outcome in outcomes:
                self._ip_set_unknown(outcome, reason)

        checking = bool(conditions) and all(o.status == 'pending' for o in outcomes)

        # Inductive step, from an arbitrary iteration. Its hypotheses are
        # asserted outright in the checks made while it is walked (see
        # _ip_local); axioms recorded meanwhile carry its guard.
        body_effect = self._ip_first_effect(body_items) or iteration_effect
        if kind == 'while' and len(loop) >= 2:
            # The condition is evaluated at the top of every iteration.
            body_effect = body_effect or self._ip_first_effect([loop[1]])
        if body_effect is not None:
            names = names | {n for n in self._ip_addr_taken if n in st.env}
        step = self._ip_havoc(st, names, pushed, opaque=not checking)
        step = step.but(alive=z3.BoolVal(True), dirty=st.dirty or body_effect)
        step_pc = z3.And(pc, z3.FreshBool('iteration'))
        local_start = len(self._ip_local)
        try:
            step, facts = self._ip_enter_iteration(loop, header, bounds, st, step, step_pc)
            self._ip_local.extend(facts)
        except _Unchecked as unchecked:
            if checking:
                for outcome in outcomes:
                    self._ip_set_unknown(outcome, str(unchecked))
                checking = False
            # The body still reads what the header binds - a map's key and
            # value, say - and not the names they shadow.
            step = self._ip_bind_unknown(step, self._ip_header_names(loop))
        if checking:
            try:
                self._ip_local.extend(z3.Implies(self._ip_pre, self._ip_formula(c, step, step_pc)[0])
                                      for c in conditions)
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
        after = self._ip_effect(after, body_effect)
        if end is not None and self._ip_contains_return(body_items):
            after = after.but(alive=z3.And(st.alive, z3.FreshBool('alive')))
        if proved:
            for condition in conditions:
                try:
                    term, _ = self._ip_formula(condition, after, pc)
                except _Unchecked:
                    continue
                self._xp_axioms.append(z3.Implies(z3.And(pc, self._ip_pre), term))
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
                            end, "not preserved", step_pc)
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

    def _ip_enter_iteration(self, loop, header, bounds, entry: _IState, step: _IState, pc):
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
            # The C loop tests `i < hi` before every iteration, and increments
            # i after each: the bound read on entry is the one tested only if
            # nothing the body does can change it, and i counts up from lo
            # only if the body leaves it alone.
            written, _, cinline = self._ip_loop_writes(loop)
            # A write through memory - a call, a field or pointer assignment -
            # can change a field the bound reads, whatever the names say.
            body_effect = self._ip_first_effect(list(loop.items[2:]))
            facts = []
            if not cinline and var not in written:
                facts.append(lo <= index)
                if self._ip_fixed_bound(header[3], written, body_effect is None):
                    facts.append(index < hi)
            if len(facts) < 2:
                self._ip_havocked.add(index.decl().name())
            return step.but(env=env, types=types), facts
        _, var, source = header
        element_type = None
        source_type = self._ip_resolve(self._ip_static_type(source, entry))
        if isinstance(source_type, ListType):
            element_type = source_type.element_type if hasattr(source_type, 'element_type') else None
        element = z3.FreshConst(self._ip_sort_of(element_type), var)
        facts = []
        # Without a sequence to be an element of, the element is anything at
        # all - more than the collection can hold (see _ip_havocked).
        exact = False
        if isinstance(source, Symbol) and source.name in entry.seqs:
            facts.extend(self._ip_member(element, entry.seqs[source.name]))
            exact = True
        elif self._ip_is_callback_source(source):
            facts.extend(self._ip_callback_facts(source, element, entry, step, pc))
            # The lambda's other parameters: whatever the callee passes.
            extra_env = dict(step.env)
            extra_types = dict(step.types)
            for name, type_expr in getattr(self, '_desugared_extra_params', {}).get(id(loop), []):
                typ = (_parse_type_expr_simple(type_expr, self.type_env.type_registry)
                       if type_expr is not None else None)
                extra_env[name] = z3.FreshConst(self._ip_sort_of(self._ip_resolve(typ)), name)
                self._ip_havocked.add(extra_env[name].decl().name())
                extra_types[name] = typ
            step = step.but(env=extra_env, types=extra_types)
        else:
            if step.dirty is None:
                root = self._ip_root_name(source)
                if self._ip_stable_parameter(root, entry):
                    seq = self._xp_tr._get_or_create_collection_seq(source)
                    if seq is not None and seq.sort() == z3.SeqSort(element.sort()):
                        facts.extend(self._ip_member(element, seq))
                        exact = True
        if not exact:
            self._ip_havocked.add(element.decl().name())
        env = dict(step.env)
        env[var] = element
        types = dict(step.types)
        types[var] = element_type
        return step.but(env=env, types=types), facts

    def _ip_fixed_bound(self, expr, written, no_effect: bool) -> bool:
        """True if `expr` has the same value at every iteration's test: made
        of numbers and names the loop does not assign (nor a call through their
        address), and fields of them only if nothing in the loop may write
        memory - `p.n` of a pointer changes under a call handed p."""
        if isinstance(expr, Number):
            return True
        if isinstance(expr, Symbol):
            root = expr.name.split('.')[0]
            if root in written or root in self._ip_addr_taken:
                return False
            return no_effect or '.' not in expr.name.strip('.')
        if is_form(expr, '.') and len(expr) == 3:
            return no_effect and self._ip_fixed_bound(expr[1], written, no_effect)
        if isinstance(expr, SList) and len(expr) >= 1 and isinstance(expr[0], Symbol) \
                and expr[0].name in ('+', '-', '*'):
            return all(self._ip_fixed_bound(item, written, no_effect) for item in expr.items[1:])
        return False

    def _ip_header_names(self, loop) -> List[str]:
        """The names a loop's header binds."""
        if len(loop) < 2 or not isinstance(loop[1], SList) or loop[0].name == 'while':
            return []
        binder = loop[1]
        named = binder.items[:-1] if loop[0].name == 'for-each' else binder.items[:1]
        names = []
        for item in named:
            stack = [item]
            while stack:
                node = stack.pop()
                if isinstance(node, Symbol) and node.name not in ('_',):
                    names.append(node.name)
                elif isinstance(node, SList):
                    stack.extend(node.items)
        return names

    def _ip_bind_unknown(self, st: _IState, names) -> _IState:
        """`names` bound to values the walk knows nothing about."""
        env, types, seqs = dict(st.env), dict(st.types), dict(st.seqs)
        for name in names:
            env[name] = self._ip_opaque(z3.IntSort())
            types[name] = None
            seqs.pop(name, None)
        return st.but(env=env, types=types, seqs=seqs)

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
        # The lambda was the last argument, so it fills the parameter after
        # the ones `args` fill; another callback parameter's facts are not
        # about this one's element.
        if len(sig.params) != len(args) + 1:
            return facts
        lambda_param = sig.params[len(args)]
        params = list(sig.params[:len(args)])
        for assumption in getattr(sig, 'callback_assumptions', []) or []:
            callback_param = getattr(assumption, 'callback_param', None)
            if callback_param != lambda_param:
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
            self._ip_havocked.add(fresh.decl().name())
            env[name] = fresh
            # A declared range is not enforced by an assignment - (Int 0 .. 10)
            # compiles to a uint8_t that `set!` can take to 11 - so a fresh
            # value keeps no bound but the sign of an unsigned C type.
            typ = self._ip_resolve(st.types.get(name))
            if isinstance(typ, PrimitiveType) and typ.name.startswith('U') and fresh.sort() == z3.IntSort():
                self._xp_axioms.append(fresh >= 0)
        seqs = dict(st.seqs)
        for name in pushed:
            if name in seqs:
                sort = seqs[name].sort()
                seqs[name] = self._ip_opaque(sort) if opaque else z3.FreshConst(sort, name)
                self._ip_havocked.add(seqs[name].decl().name())
        return st.but(env=env, seqs=seqs)

    def _ip_unknown_within(self, loop, reason: str) -> None:
        """Every invariant of `loop` and of loops inside it not yet decided is unknown."""
        def walk(node):
            if not isinstance(node, SList):
                return
            for condition in self._ip_sites.get(id(node), []):
                self._ip_set_unknown(self._ip_outcomes[id(condition)], reason)
            for outcome in self._ip_exit_outcomes.get(id(node), []):
                self._ip_set_unknown(outcome, reason)
            for item in node.items:
                walk(item)
        walk(loop)

    def _ip_set_unknown(self, outcome: InvariantOutcome, reason: str, status: str = 'unknown') -> None:
        if outcome.status in ('pending', 'proved'):
            outcome.status = status
            outcome.message = self._ip_unchecked_text(outcome, reason)
            outcome.counterexample = None

    # ------------------------------------------------------------------
    # Solving
    # ------------------------------------------------------------------

    def _ip_decide(self, outcome: InvariantOutcome, claim, st: _IState, failure: str, path,
                   goal=None) -> None:
        """Check `claim` under everything the walk has established; record a failure.

        `path` is the claim's path condition. A proof is only a proof if the
        facts leave that path possible; the hypotheses of the iteration are
        left out of that question, since an iteration no state can start is
        a legitimate reason for the step to hold.
        """
        if outcome.status != 'pending':
            return
        if self._ip_time_spent:
            self._ip_set_unknown(outcome, "not checked: the time budget went on an earlier check")
            return
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)
        facts = list(self._ip_context) + list(self._xp_axioms)
        if outcome.kind != 'property':
            facts.append(self._ip_pre)
        for fact in facts:
            solver.add(fact)
        for fact in self._ip_local:
            solver.add(fact)
        solver.add(z3.Not(claim))
        result = solver.check()
        if result == z3.unsat:
            # A return the facts rule out is dead code, and a claim there
            # holds: only facts that contradict one another say nothing.
            reach = path if outcome.kind == 'invariant' else z3.BoolVal(True)
            key = (len(facts), reach.get_id(), outcome.kind == 'property')
            if key not in self._ip_consistent:
                self._ip_consistent[key] = not self._axioms_are_contradictory(facts + [reach])
            if not self._ip_consistent[key]:
                self._ip_set_unknown(outcome, "the verification context is inconsistent")
            return      # holds; the caller decides what that makes the invariant
        if result == z3.sat:
            model = solver.model()
            # At a return, a value a loop may have left behind is only what
            # the loop's invariants say of it - less than the program knows.
            over = self._ip_havocked if outcome.kind != 'invariant' else ()
            if goal is not None:
                # What decides whether the return is reached is not what
                # decides whether the claim holds there: a guard testing an
                # element nothing is known about leaves the return possible,
                # and a claim false whatever that element is stays false. So
                # the claim is its goal, and a fact recorded under a path
                # condition links values only through what it states.
                # The path's own tests still relate values: `(== x last)` ties
                # the returned x to whatever last is.
                tests = self._ip_conjuncts(path) + self._ip_conjuncts(st.alive)
                depends = self._ip_depends_on_opaque(goal, facts + list(self._ip_local) + tests,
                                                     over, consequents=True)
            else:
                depends = self._ip_depends_on_opaque(claim, facts + list(self._ip_local), over)
            if depends:
                self._ip_set_unknown(outcome, "it depends on something the analysis could not follow")
                return
            outcome.status = 'failed'
            if outcome.kind == 'invariant':
                outcome.message = f"loop invariant {failure}: {outcome.text}"
            else:
                outcome.message = f"{outcome.what} does not hold{outcome.where}: {outcome.text}"
            shown = outcome.expr
            if outcome.site is not None and len(outcome.site) >= 2:
                shown = SList([outcome.expr, outcome.site[1]])
            outcome.counterexample = self._ip_counterexample(shown, st, model)
            return
        self._ip_time_spent = True
        self._ip_set_unknown(outcome, "the solver timed out", status='timeout')

    def _ip_depends_on_opaque(self, claim, facts, over=(), consequents=False) -> bool:
        """True if the claim, or a fact linked to it through shared constants,
        mentions a value the walk could not follow - or one of `over`, the
        values it over-approximates. A counterexample through one is no
        evidence (#69)."""
        def own(consts):
            # A path condition's guard is shared by everything under it and
            # says nothing about values.
            return {c for c in consts if not c.startswith(('iteration!', 'alive!', 'pre!'))}

        def stated(fact):
            while consequents and z3.is_app_of(fact, z3.Z3_OP_IMPLIES):
                fact = fact.arg(1)
            return fact
        names = own(self._ip_constants(claim))
        linked = [(f, own(self._ip_constants(stated(f)))) for f in facts]
        grew = True
        while grew:
            grew = False
            for fact, consts in linked:
                if consts & names and not consts <= names:
                    names |= consts
                    grew = True
        return any(name.startswith(_OPAQUE) or name in over for name in names)

    @staticmethod
    def _ip_conjuncts(term) -> List[Any]:
        out, stack = [], [term]
        while stack:
            node = stack.pop()
            if z3.is_and(node):
                stack.extend(node.children())
            else:
                out.append(node)
        return out

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
        loop's exit if nothing after the loop changes them. A reason it is
        not is kept in `outcome.unused`.
        """
        def no(reason: str) -> bool:
            outcome.unused = reason
            return False

        loop = outcome.loop
        if self._ip_loop_depth.get(id(loop)) != 0:
            return no("its loop is inside another loop")
        # The invariant was proved of the paths that reach the loop. Asserted
        # about the function, it would also describe one that returned
        # before getting there: the caller states it only where no early
        # return was taken, which it can do for `return` but not for `?`.
        exits = self._ip_exits_before(body, loop)
        if exits == '?':
            return no("the function can exit before the loop in a way the verifier cannot guard")
        outcome.exits_before = exits == 'return'
        if self._needs_array_encoding([outcome.expr]):
            return no("it needs the array encoding; state it as a forall over the list")
        if self._ip_unwalked_return(list(loop.items[1:])):
            # A run that returns from inside the loop leaves it mid-iteration,
            # where the invariant need not hold. A walked return is fine: the
            # main model covers only the runs that take none, and on those the
            # loop ran to its end.
            return no("the loop can return from inside its body")
        after = self._ip_after(body, loop)
        tracked_read = {s.name for s in self._ip_quantifier_sources(outcome.expr)
                        if isinstance(s, Symbol) and s.name in self._ip_tracked}
        for node in after:
            if is_form(node, 'list-push') and len(node) >= 2 and isinstance(node[1], Symbol) \
                    and node[1].name in tracked_read:
                return no(f"{node[1].name} is pushed to after the loop")
        if outcome.reads_state:
            for node in after:
                if is_form(node, 'c-inline'):
                    return no("it reads collection state, and c-inline after the loop may change it")
                if isinstance(node, SList) and len(node) > 0 and isinstance(node[0], Symbol):
                    effect = self._ip_call_effect(node)
                    if effect is not None:
                        return no(f"it reads collection state, which {effect} after the loop may change")
        return True

    def _ip_exits_before(self, body, loop) -> Optional[str]:
        """'?' if a `?` comes before `loop`, else 'return' if a `return` does, else None."""
        state = {'found': None, 'done': False, 'assigned': False}

        def walk(node):
            if state['done'] or not isinstance(node, SList) or len(node) == 0:
                return
            if node is loop:
                state['done'] = True
                return
            head = node[0].name if isinstance(node[0], Symbol) else None
            if head in ('quote', 'fn'):
                return
            if head == '?':
                state['found'] = '?'
            elif head == 'return' and state['found'] is None and id(node) not in self._ip_walked:
                # A walked return is not one the main model has runs for.
                state['found'] = 'return'
            elif head == 'set!':
                state['assigned'] = True
            for item in node.items:
                walk(item)

        walk(body)
        if state['found'] == 'return' and state['assigned']:
            # The early-exit guards read names as they stood at the top; an
            # assignment before the loop may have changed what one tests.
            return '?'
        return state['found']

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
