"""
Axiom Generation Mixin for ContractVerifier.

Provides methods for generating Z3 axioms from loop patterns, record constructors,
list operations, and other SLOP constructs to enable verification.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Set, Tuple, TYPE_CHECKING

from slop.parser import SList, Symbol, String, Number, is_form
from slop.types import RecordType, RangeType

from .z3_setup import Z3_AVAILABLE, z3
from .loop_patterns import (
    PushSiteInfo,
    FilterPatternInfo, MapPatternInfo, NestedLoopPatternInfo, CountPatternInfo,
    FoldPatternInfo, ExistsSearchPatternInfo, ConditionalPushPatternInfo,
    InnerLoopInfo, FieldSource, MatchContext,
)

if TYPE_CHECKING:
    from slop.parser import SExpr
    from .translator import Z3Translator
    from .types import FunctionSignature


class AxiomGenerationMixin:
    """Mixin providing axiom generation methods."""

    @staticmethod
    def _binding_name(binding: 'SList') -> Optional[str]:
        """The name a `let` binding introduces, across the three spellings.

        (name value), (mut name value) and ((mut name) value) all bind a name;
        the last is easy to miss, since its head is a list rather than a symbol.
        """
        head = binding[0]
        if isinstance(head, Symbol):
            if head.name == 'mut' and len(binding) >= 3:
                target = binding[1]
            else:
                target = head
        elif isinstance(head, SList) and len(head) >= 2:
            if not (isinstance(head[0], Symbol) and head[0].name == 'mut'):
                return None
            target = head[1]
        else:
            return None
        return target.name if isinstance(target, Symbol) else None

    def _binding_in_scope_at_tail(self, body: 'SExpr', name: str):
        """The initializer bound to `name` where the body returns, and its scope.

        Follows the tail of the body - the last form of each nested do/let,
        which is what the function actually yields - and keeps the innermost
        binding of `name` seen on the way. Returns (None, body) when the name is
        not bound here at all, which is the case for a parameter.
        """
        initializer = None
        scope = body
        node = body
        while True:
            if is_form(node, 'let') and len(node) >= 3:
                bindings = node[1]
                if isinstance(bindings, SList):
                    for binding in bindings.items:
                        if (isinstance(binding, SList) and len(binding) >= 2
                                and self._binding_name(binding) == name):
                            initializer = binding[-1]
                            scope = node
                node = node.items[-1]
            elif is_form(node, 'do') and len(node) >= 2:
                node = node.items[-1]
            else:
                return initializer, scope

    def _count_bindings_of(self, expr: 'SExpr', name: str) -> int:
        """How many forms under `expr` bind `name`.

        More than one means an inner binding shadows the outer, so pushes to the
        two are not pushes to the same list. `for-each` binders count: a loop
        variable may share the accumulator's name.
        """
        count = 0
        if isinstance(expr, SList):
            if is_form(expr, 'for-each') and len(expr) >= 2 and isinstance(expr[1], SList):
                binder = expr[1]
                if len(binder) >= 1 and isinstance(binder[0], Symbol) and binder[0].name == name:
                    count += 1
            if is_form(expr, 'let') and len(expr) >= 2 and isinstance(expr[1], SList):
                for binding in expr[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        if self._binding_name(binding) == name:
                            count += 1
            for item in expr.items:
                count += self._count_bindings_of(item, name)
        return count

    def _field_path(self, expr: 'SExpr') -> Optional[str]:
        """A dotted path for a field access, in whichever spelling it is written.

        `(. report results)` and `report.results` are the same list; the parser
        keeps the second as one symbol. Returns None for anything that is not a
        field access, so a plain variable still matches by name.
        """
        if isinstance(expr, Symbol):
            return expr.name if '.' in expr.name.strip('.') else None
        if is_form(expr, '.') and len(expr) >= 3:
            head = self._field_path(expr[1])
            if head is None:
                head = expr[1].name if isinstance(expr[1], Symbol) else None
            field = expr[2].name if isinstance(expr[2], Symbol) else None
            if head is None or field is None:
                return None
            return f"{head}.{field}"
        return None

    def _uses_outside(self, body: 'SExpr', target: 'SExpr', allowed) -> bool:
        """True if `target` appears anywhere in `body` in a context `allowed` rejects.

        `target` is an expression, so this works for a plain variable and for
        something like `(. report results)` alike. `allowed` is called with
        (parent_head, index, returns_value) for each occurrence and says whether
        that use leaves the list's length knowable; returns_value is true only
        for the value the function actually yields, which means the trailing
        position of a do/let chain reached from the body root - `(list-pop (do r))`
        has r in a trailing position, but that block is an argument, not a result.
        """
        from slop.parser import pretty_print

        # Printing every node to compare it is quadratic on a large body, and
        # the rule files this runs over are large. Compare structurally, and
        # print only for a compound target against a node that could match it.
        target_is_symbol = isinstance(target, Symbol)
        target_name = target.name if target_is_symbol else None
        target_str = None if target_is_symbol else pretty_print(target)
        target_len = None if target_is_symbol else len(target)
        # `(. report results)` and `report.results` denote the same list, and a
        # body may use one to iterate and the other to mutate.
        target_path = self._field_path(target)

        def matches(node):
            if target_path is not None and self._field_path(node) == target_path:
                return True
            if target_is_symbol:
                return isinstance(node, Symbol) and node.name == target_name
            if not isinstance(node, SList) or len(node) != target_len:
                return False
            return pretty_print(node) == target_str

        def walk(node, parent_head, index, returns_value):
            if matches(node):
                return not allowed(parent_head, index, returns_value)
            if not isinstance(node, SList):
                return False
            head = node[0].name if len(node) and isinstance(node[0], Symbol) else None
            last = len(node) - 1
            block = head in ('do', 'let')
            for i, item in enumerate(node.items):
                # The binder of a for-each is (var collection); name that
                # position so a collection may be recognised there.
                child_head = '@for-each-binder' if (head == 'for-each' and i == 1) else head
                if isinstance(item, SList) and child_head == '@for-each-binder':
                    for j, sub in enumerate(item.items):
                        if walk(sub, '@for-each-binder', j, False):
                            return True
                    continue
                if walk(item, head, i, returns_value and block and i == last):
                    return True
            return False

        return walk(body, None, -1, True)

    @staticmethod
    def _accumulator_use_is_safe(parent_head, index, returns_value) -> bool:
        """Contexts in which the returned list's length stays derivable.

        Counting pushes bounds a list only if nothing else touches it. A
        list-pop shortens it, a set! replaces it outright, and handing it to a
        function that appends to it does the same at a distance. Only the target
        of a push, the argument of a read, its own binding, and the value the
        body yields are accounted for; anything else, including an operation
        this does not know about, means no bound.
        """
        if parent_head == 'list-push' and index == 1:
            return True
        # list-set is a read as far as the length goes: it overwrites an element
        # in place and leaves the count alone. It does change the contents,
        # which is a separate question, handled by withholding the provenance
        # axioms for a body that uses it.
        if parent_head in ('list-len', 'list-get', 'list-set') and index == 1:
            return True
        if parent_head == 'mut' and index == 1:
            return True
        return returns_value

    @staticmethod
    def _source_use_is_safe(parent_head, index, returns_value) -> bool:
        """Contexts in which a loop's source collection is only read.

        A loop bound is stated against the source's length as one term, so
        anything that changes that length - a push, a pop, a reassignment, a
        callee that appends - would have the bound read against a different
        collection than the loop saw.
        """
        if parent_head == '@for-each-binder' and index == 1:
            return True
        return parent_head in ('list-len', 'list-get', 'list-set') and index == 1

    def _list_escapes(self, expr: 'SExpr', target: 'SExpr') -> bool:
        """True if the returned list is used in a way that hides its length."""
        return self._uses_outside(expr, target, self._accumulator_use_is_safe)

    @staticmethod
    def _owner_use_is_safe(parent_head, index, returns_value) -> bool:  # noqa: D401
        """Contexts in which the owner of a field-valued collection is only read.

        For a source like `(. report results)`, `report` itself has to stay put:
        a `(set! report other)` after the loop, or handing `report` to a callee
        that replaces its list, changes which collection the bound is read
        against without touching the printed source expression at all.
        """
        return parent_head == '.' and index == 1

    def _is_stable_source(self, coll: 'SExpr') -> bool:
        """True if `coll` is a shape whose dependencies can be enumerated.

        A variable, or a field chain rooted at one. Anything else - an `if`
        choosing between two collections, a call returning one - depends on
        values this cannot list, so a mutation of one of them would go unnoticed
        while the printed source expression stayed the same.
        """
        node = coll
        while is_form(node, '.') and len(node) >= 2:
            node = node[1]
        return isinstance(node, Symbol)

    @staticmethod
    def _dotted_symbol_owners(name: str) -> List[str]:
        """The owner prefixes of a shorthand field symbol, e.g. `report.results`.

        The parser keeps that spelling as one symbol rather than a (. ...) form,
        so a chain written this way needs its prefixes recovered by hand.
        """
        if '.' not in name or name.startswith('.') or name.endswith('.'):
            return []
        parts = name.split('.')
        return ['.'.join(parts[:i]) for i in range(1, len(parts))]

    def _source_escapes(self, fn_body: 'SExpr', coll: 'SExpr') -> bool:
        """True if the loop's source collection is anything but read in this body."""
        if self._uses_outside(fn_body, coll, self._source_use_is_safe):
            return True
        # A field access is only as stable as the value it reads from.
        for owner in self._owner_expressions(coll):
            if self._uses_outside(fn_body, owner, self._owner_use_is_safe):
                return True
        return False

    def _owner_expressions(self, coll: 'SExpr') -> List['SExpr']:
        """The sub-expressions a field-access source depends on.

        Covers both spellings: the `(. report results)` form and the shorthand
        `report.results`, which the parser keeps as a single symbol.
        """
        owners: List['SExpr'] = []
        node = coll
        while is_form(node, '.') and len(node) >= 2:
            node = node[1]
            owners.append(node)
        if isinstance(node, Symbol):
            owners.extend(Symbol(prefix) for prefix in self._dotted_symbol_owners(node.name))
        return owners

    def _contains_any_form(self, expr: 'SExpr', heads) -> bool:
        """True if `expr` calls any of `heads` in this function's own body.

        The walk stops at a nested `(fn ...)`: a callback's `return` leaves the
        callback, and its `break` belongs to a loop inside it, so neither says
        anything about the enclosing function's exits. Counting them suppressed
        the result-length axioms of any function that passes a callback.
        """
        if isinstance(expr, SList):
            if len(expr) >= 1 and isinstance(expr[0], Symbol):
                if expr[0].name in heads:
                    return True
                if expr[0].name == 'fn':
                    return False
                # Quoted forms are data. A (return ...) inside one is a symbol
                # the function never executes.
                if expr[0].name == 'quote':
                    return False
            for item in expr.items:
                if self._contains_any_form(item, heads):
                    return True
        return False

    def _length_terms_for(self, expr: 'SExpr', translator: 'Z3Translator'):
        """Every length term for the list denoted by `expr`, plus links between them.

        A list can carry more than one length representation at once (see
        Z3Translator.list_length_terms). Callers assert a bound on all of them
        and add the links, so the fact is visible whichever one the contract
        happened to translate to.
        """
        terms: List[z3.ArithRef] = []

        if isinstance(expr, Symbol):
            terms.extend(translator.list_length_terms(expr.name))
        elif is_form(expr, '.') and len(expr) >= 3:
            obj, fld = expr[1], expr[2]
            if isinstance(obj, Symbol) and isinstance(fld, Symbol):
                # Same key as _extract_map_push_axioms / _get_or_create_collection_seq.
                # It names a Seq/array registration, not a variable - a parameter
                # could legitimately be called _field_report_results, and reading
                # it out of `variables` would tie that parameter's length to an
                # unrelated field's.
                key = translator.field_collection_key(obj.name, fld.name)
                seq = translator.list_seqs.get(key)
                if seq is not None:
                    terms.append(z3.Length(seq))
                arr_entry = translator.list_arrays.get(key)
                if arr_entry is not None:
                    terms.append(arr_entry[1])

        handle = translator.translate_expr(expr)
        if handle is not None and z3.is_expr(handle) and handle.sort() == z3.IntSort():
            func = translator.variables.get("field_len")
            if func is None:
                func = z3.Function("field_len", z3.IntSort(), z3.IntSort())
                translator.variables["field_len"] = func
            if isinstance(func, z3.FuncDeclRef) and func.arity() == 1:
                # Occupied by a user binding of that name otherwise; see
                # Z3Translator.field_len_term.
                field_len = func(handle)
                if not any(z3.eq(field_len, t) for t in terms):
                    terms.append(field_len)

        links = [terms[0] == t for t in terms[1:]]
        return terms, links

    def _result_length_axioms(self, fn_body: SExpr,
                              translator: 'Z3Translator') -> List[z3.BoolRef]:
        """Sound bounds on the length of the list this function returns.

        This replaces two axioms that used to be emitted independently and
        contradicted each other on any body that pushes (issue #115): a flat
        `field_len($result) == 0` derived from the `(mut r (list-new ...))`
        binding, which ignored every push, and a `field_len($result) >= n`
        derived from the push count, which was itself wrong for a conditional
        or looping push. An unsatisfiable pair makes every postcondition
        discharge without being proved.

        What the push sites support:

            no pushes                                 len == 0
            n straight-line unconditional pushes      len == n
            n sites, some conditional, none in a loop 0 <= len <= n
            unconditional push in a map loop          len == len(source)
            guarded push in a filter loop             0 <= len <= len(source)
            any other loop push                       no bound

        A push under a `match` arm or a `when`/`if` guard is conditional: it
        contributes to the upper bound but not the lower. A push inside a loop
        runs an unknown number of times, so the site count bounds nothing - only
        a recognised map/filter shape gives a bound there, from the length of
        the collection being iterated.
        """
        terms = translator.list_length_terms('$result')
        if not terms:
            return []

        axioms: List[z3.BoolRef] = list(translator.link_list_length_terms('$result'))

        # _get_return_expr only looks at the trailing expression. An explicit
        # (return ...) elsewhere in the body is a second exit it cannot see, and
        # whatever that path returns is just as much $result - so nothing about
        # the trailing expression describes the result on its own.
        if self._contains_any_form(fn_body, ('return',)):
            return axioms

        return_expr = self._get_return_expr(fn_body)

        # A bare (list-new ...) return is empty, with no body to push from.
        if is_form(return_expr, 'list-new'):
            axioms.extend(t == z3.IntVal(0) for t in terms)
            return axioms

        if not isinstance(return_expr, Symbol):
            return axioms

        name = return_expr.name

        # Resolve the returned name to the binding that governs it, and work
        # inside that binding's scope from here on. Scanning the whole body
        # instead conflates same-named bindings in disjoint scopes, and lets an
        # unrelated (list-new ...) elsewhere decide whether the returned list
        # started empty.
        initializer, scope = self._binding_in_scope_at_tail(fn_body, name)
        sites = self._collect_push_sites([scope], name)

        # Fail closed. _collect_push_sites is a whitelist walk: it classifies
        # the forms it knows and silently returns nothing for the rest, which is
        # fine for a heuristic but not for deriving a bound. A plain recursive
        # count of every (list-push name ...) in the body says how many there
        # really are; if the structured walk saw a different number it passed
        # through something it does not model - a form it does not descend into,
        # or a push built by (set! name (list-push name x)) - and no bound may
        # be claimed. Without this, a push under a `cond` yielded no sites and
        # so "proved" the result empty.
        if len(sites) != self._count_push_to_var([scope], name):
            return axioms

        # A nested (let ((mut name ...))) rebinds the name to a different list.
        # Pushes to the inner one are still counted against the outer, so bail.
        if self._count_bindings_of(scope, name) > 1:
            return axioms

        # Pushes are the only mutation modelled. A list-pop, a set! or a call
        # that receives the list and appends to it all change the length in ways
        # the count does not see.
        if self._list_escapes(scope, return_expr):
            return axioms

        # A list the function allocated itself started empty, so the push sites
        # account for its whole contents. One it was handed may already hold
        # anything, so the same sites only raise its floor.
        starts_empty = is_form(initializer, 'list-new')

        if any(site.loop_depth > 0 for site in sites):
            if not starts_empty:
                return axioms
            early_exit = self._contains_any_form(scope, ('break', 'continue'))
            loop_axioms = self._loop_result_length_axioms(
                scope, sites, terms, translator, early_exit)
            if loop_axioms:
                axioms.extend(loop_axioms)
                return axioms
            # No bound from the loop, but the pushes outside it still happened
            # and a loop only ever adds - so the floor they set holds whatever
            # the loop did. Without this a straight push before a while loop
            # left the result looking possibly empty.
            floor = sum(
                1 for site in sites
                if site.loop_depth == 0
                and not site.guard_conditions and not site.conditional)
            if floor:
                axioms.extend(t >= z3.IntVal(floor) for t in terms)
            return axioms

        upper = len(sites)
        lower = sum(
            1 for site in sites
            if not site.guard_conditions and not site.conditional
        )
        for t in terms:
            if not starts_empty:
                if lower:
                    axioms.append(t >= z3.IntVal(lower))
            elif lower == upper:
                axioms.append(t == z3.IntVal(lower))
            else:
                axioms.append(t >= z3.IntVal(lower))
                axioms.append(t <= z3.IntVal(upper))
        return axioms

    def _loop_result_length_axioms(self, fn_body: 'SExpr',
                                   sites: List['PushSiteInfo'],
                                   terms: List[z3.ArithRef],
                                   translator: 'Z3Translator',
                                   early_exit: bool = False) -> List[z3.BoolRef]:
        """Length bound for a result built by pushing inside a loop.

        The bound comes from the loop itself rather than from a named pattern:
        every push site must sit inside the same single `for-each`, and then k
        sites over a collection C give at most k*len(C) elements - exactly
        len(C) when the one site is unconditional. That covers a map and a
        filter alike, including a filter written as a `match` arm rather than a
        `when`, which the pattern detectors do not recognise.

        Anything else gets no bound: a `while` has no collection to measure, and
        nested loops multiply out to a product this does not try to express. The
        length is then left unconstrained beyond the non-negativity the type
        carries, and the caller reports that it could not bound it.

        `early_exit` suppresses the exact case: with a break, continue or return
        in the body the single push no longer runs once per element. The k*len(C)
        upper bound survives, since every exit only makes the loop shorter.
        """
        if not sites:
            return []

        collections = [site.loop_collections for site in sites]
        if any(len(c) != 1 or c[0] is None for c in collections):
            return []

        from slop.parser import pretty_print
        distinct = {pretty_print(c[0]) for c in collections}
        if len(distinct) != 1:
            return []

        source = collections[0][0]
        if not self._is_stable_source(source):
            return []
        if self._source_escapes(fn_body, source):
            return []

        src_terms, links = self._length_terms_for(source, translator)
        if not src_terms:
            return []
        source_len = src_terms[0]

        exact = (len(sites) == 1
                 and not sites[0].guard_conditions
                 and not sites[0].conditional
                 and not early_exit)
        if exact:
            return links + [t == source_len for t in terms]
        return links + [t <= len(sites) * source_len for t in terms]

    def _extract_seq_push_axioms(self, fn_body: SExpr, postconditions: List[SExpr],
                                  translator: 'Z3Translator') -> List[z3.BoolRef]:
        """Generate axioms connecting pushed elements to their source.

        For filter patterns like:
            (let ((mut result (list-new ...)))
              (for-each (t items)
                (when (pred t)
                  (list-push result t)))
              result)

        Generates axiom:
            ForAll i: 0 <= i < Length($result) =>
                Exists j: 0 <= j < Length(items) &&
                          $result[i] == items[j] && pred(items[j])

        This enables proving postconditions like:
            (forall (t $result) (pred t))
        """
        axioms: List[z3.BoolRef] = []

        # Find filter patterns
        filter_pattern = self._detect_filter_pattern(fn_body)
        if filter_pattern is None:
            return axioms

        # Need Seq for $result
        if '$result' not in translator.list_seqs:
            return axioms

        result_seq = translator.list_seqs['$result']

        # Get or create Seq for source collection
        if isinstance(filter_pattern.collection, Symbol):
            source_name = filter_pattern.collection.name
            if source_name not in translator.list_seqs:
                # Create Seq for the source collection
                translator._create_list_seq(source_name)
            source_seq = translator.list_seqs.get(source_name)
        else:
            return axioms

        if source_seq is None:
            return axioms

        # Create index variables for the quantified formula
        result_idx = z3.Int('_push_res_i')
        source_idx = z3.Int('_push_src_j')

        # Translate the predicate with loop variable bound to source element
        old_binding = translator.variables.get(filter_pattern.loop_var)
        try:
            # Bind loop var to source element at j
            translator.variables[filter_pattern.loop_var] = source_seq[source_idx]

            pred_z3 = translator.translate_expr(filter_pattern.predicate)
            if pred_z3 is None:
                return axioms

            # Handle negated predicates (exclusion filters)
            if filter_pattern.is_negated:
                # For (not (eq item excluded)), all result elements satisfy (not (eq elem excluded))
                # This is a simpler axiom: just propagate the predicate
                pass

            # Build the axiom:
            # ForAll i in result: Exists j in source: result[i] == source[j] && pred(source[j])
            #
            # This says: every element in result came from source and satisfies the predicate
            source_constraint = z3.Exists([source_idx],
                z3.And(
                    source_idx >= 0,
                    source_idx < z3.Length(source_seq),
                    result_seq[result_idx] == source_seq[source_idx],
                    pred_z3
                )
            )

            axiom = z3.ForAll([result_idx],
                z3.Implies(
                    z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                    source_constraint
                )
            )
            axioms.append(axiom)

            # Also add a simpler axiom that directly states the postcondition property
            # For filter (pred t), every element in result satisfies pred
            # ForAll i: 0 <= i < Length(result) => pred(result[i])
            translator.variables[filter_pattern.loop_var] = result_seq[result_idx]
            pred_on_result = translator.translate_expr(filter_pattern.predicate)
            if pred_on_result is not None:
                direct_axiom = z3.ForAll([result_idx],
                    z3.Implies(
                        z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                        pred_on_result
                    )
                )
                axioms.append(direct_axiom)

        finally:
            # Restore binding
            if old_binding is not None:
                translator.variables[filter_pattern.loop_var] = old_binding
            elif filter_pattern.loop_var in translator.variables:
                del translator.variables[filter_pattern.loop_var]

        return axioms

    def _extract_map_push_axioms(self, fn_body: SExpr, postconditions: List[SExpr],
                                  translator: 'Z3Translator') -> List[z3.BoolRef]:
        """Generate axioms connecting result fields to source fields for map patterns.

        For map patterns like:
            (let ((mut result (list-new ...)))
              (for-each (dt (. delta triples))
                (list-push result
                  (triple-new arena
                    (triple-predicate dt)  ; predicate preserved
                    (triple-object dt)     ; subject <- object (swapped)
                    (triple-subject dt)))) ; object <- subject (swapped)
              result)

        Generates axiom:
            ForAll i: 0 <= i < Length($result) =>
                Exists j: 0 <= j < Length(source) &&
                    field_predicate($result[i]) == field_predicate(source[j]) &&
                    field_subject($result[i]) == field_object(source[j]) &&
                    field_object($result[i]) == field_subject(source[j])

        This enables proving postconditions like:
            (forall (t $result)
              (exists (dt (. delta triples))
                (and (term-eq (triple-predicate dt) (triple-predicate t))
                     (term-eq (triple-subject t) (triple-object dt))
                     (term-eq (triple-object t) (triple-subject dt)))))

        Also handles nested loop patterns (joins) like eq-trans where inner loops
        iterate over query results derived from outer loop variables.
        """
        axioms: List[z3.BoolRef] = []

        # First try: single-loop map pattern
        map_pattern = self._detect_map_pattern(fn_body)
        if map_pattern is None:
            # Second try: nested loop pattern (joins)
            nested_patterns = self._detect_all_nested_loop_patterns(fn_body)
            if nested_patterns:
                for nested_pattern in nested_patterns:
                    axioms.extend(self._generate_nested_loop_axioms(
                        nested_pattern, postconditions, translator
                    ))
                return axioms
            return axioms

        # Need Seq for $result
        if '$result' not in translator.list_seqs:
            return axioms

        result_seq = translator.list_seqs['$result']

        # Get or create Seq for source collection
        source_seq = None
        source_name = None

        if isinstance(map_pattern.collection, Symbol):
            source_name = map_pattern.collection.name
            if source_name not in translator.list_seqs:
                translator._create_list_seq(source_name)
            source_seq = translator.list_seqs.get(source_name)
        elif is_form(map_pattern.collection, '.') and len(map_pattern.collection) >= 3:
            # Field access: (. obj field) - use same naming as property translator
            obj = map_pattern.collection[1]
            field = map_pattern.collection[2]
            if isinstance(obj, Symbol) and isinstance(field, Symbol):
                # Must match the key _get_or_create_collection_seq registers under
                source_name = translator.field_collection_key(obj.name, field.name)
                if source_name not in translator.list_seqs:
                    translator._create_list_seq(source_name)
                source_seq = translator.list_seqs.get(source_name)

        if source_seq is None:
            return axioms

        # Create index variables for the quantified formula
        result_idx = z3.Int('_map_res_i')
        source_idx = z3.Int('_map_src_j')

        # Build field correspondence constraints
        # For each (result_field, source_expr) in field_mappings,
        # generate: field_{result_field}($result[i]) == translate(source_expr)[loop_var/source[j]]

        old_binding = translator.variables.get(map_pattern.loop_var)
        try:
            # Bind loop var to source element at j for translating source expressions
            translator.variables[map_pattern.loop_var] = source_seq[source_idx]

            field_constraints = []

            # Determine the type prefix from the collection being iterated
            # For (. delta triples) iterating Triple elements, prefix is "triple"
            type_prefix = self._infer_element_type_prefix(map_pattern.collection)

            for result_field, source_expr in map_pattern.field_mappings.items():
                # Determine result accessor name
                if type_prefix:
                    result_accessor_name = f"{type_prefix}-{result_field}"
                else:
                    result_accessor_name = result_field

                # Create the result field function
                result_field_func_name = f"fn_{result_accessor_name}_1"
                if result_field_func_name not in translator.variables:
                    result_field_func = z3.Function(
                        result_field_func_name,
                        z3.IntSort(),
                        z3.IntSort()
                    )
                    translator.variables[result_field_func_name] = result_field_func
                else:
                    result_field_func = translator.variables[result_field_func_name]

                result_field_z3 = result_field_func(result_seq[result_idx])

                # Find appropriate equality function for the field type
                eq_func = self._get_type_equality_function(
                    result_accessor_name, translator
                )

                # Check if source_expr references the loop variable
                # If not, it's a constant field - use source field == result field
                if not self._references_var(source_expr, map_pattern.loop_var):
                    # Constant field: add constraint that source field equals result field
                    # This is valid because filter conditions ensure matching values
                    source_field_z3 = result_field_func(source_seq[source_idx])
                    if eq_func is not None:
                        field_constraints.append(eq_func(result_field_z3, source_field_z3))
                    else:
                        field_constraints.append(result_field_z3 == source_field_z3)
                    continue

                # Translate the source expression with loop var bound to source[j]
                source_z3 = translator.translate_expr(source_expr)
                if source_z3 is None:
                    continue

                # For map pattern: result.subject = source.object
                # We need: term-eq(triple-subject(result[i]), triple-object(source[j]))

                if eq_func is not None:
                    # Use type-specific equality: eq_func(result_field, source_field)
                    field_constraints.append(eq_func(result_field_z3, source_z3))
                else:
                    # Fallback to native equality
                    field_constraints.append(result_field_z3 == source_z3)

            if not field_constraints:
                return axioms

            # Build the axiom:
            # ForAll i in result: Exists j in source: AND(field_constraints...)
            source_constraint = z3.Exists([source_idx],
                z3.And(
                    source_idx >= 0,
                    source_idx < z3.Length(source_seq),
                    *field_constraints
                )
            )

            axiom = z3.ForAll([result_idx],
                z3.Implies(
                    z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                    source_constraint
                )
            )
            axioms.append(axiom)

            # Size relationship: result size <= source size
            # For unfiltered maps they're equal; for filtered maps result may be smaller
            size_axiom = z3.Length(result_seq) <= z3.Length(source_seq)
            axioms.append(size_axiom)

            # Completeness axiom (inverse direction):
            # ForAll j in source: filter_conditions(source[j]) =>
            #     Exists i in result: field_constraints(result[i], source[j])
            #
            # This enables proving "for every filtered source, there's a matching result"
            filter_conditions, filter_bindings = self._extract_filter_conditions_from_loop(fn_body)
            if filter_conditions:
                # Resolve variables in filter conditions through bindings
                resolved_conditions = [
                    self._resolve_filter_condition(cond, filter_bindings)
                    for cond in filter_conditions
                ]

                # Translate filter conditions with loop var bound to source[j]
                filter_z3 = []
                for cond in resolved_conditions:
                    cond_z3 = translator.translate_expr(cond)
                    if cond_z3 is not None:
                        filter_z3.append(cond_z3)

                if filter_z3:
                    # Build: filter1 AND filter2 AND ... => Exists result matching
                    result_constraint = z3.Exists([result_idx],
                        z3.And(
                            result_idx >= 0,
                            result_idx < z3.Length(result_seq),
                            *field_constraints
                        )
                    )

                    completeness_axiom = z3.ForAll([source_idx],
                        z3.Implies(
                            z3.And(
                                source_idx >= 0,
                                source_idx < z3.Length(source_seq),
                                *filter_z3
                            ),
                            result_constraint
                        )
                    )
                    axioms.append(completeness_axiom)

            # Match context subset axioms: connect match-bound collection to parent
            if map_pattern.match_context is not None:
                match_axioms = self._generate_match_subset_axioms(
                    map_pattern.match_context, source_seq, source_name, translator
                )
                axioms.extend(match_axioms)

        finally:
            # Restore binding
            if old_binding is not None:
                translator.variables[map_pattern.loop_var] = old_binding
            elif map_pattern.loop_var in translator.variables:
                del translator.variables[map_pattern.loop_var]

        return axioms

    def _generate_nested_loop_axioms(
        self,
        pattern: NestedLoopPatternInfo,
        postconditions: List[SExpr],
        translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Generate axioms for nested loop join patterns.

        For nested patterns like eq-trans:
        (let ((same-as (make-iri arena OWL_SAME_AS))
              (mut result (list-new arena Triple)))
          (for-each (dt (. delta triples))
            (when (term-eq (triple-predicate dt) same-as)
              (let ((x (triple-subject dt))
                    (y (triple-object dt)))
                (let ((y-objects (indexed-graph-match ...)))
                  (for-each (yo-triple y-objects)
                    (let ((z (triple-object yo-triple)))
                      (when inner-filter
                        (list-push result (make-triple arena x same-as z)))))))))
          result)

        Generates axioms that connect result elements to outer collection elements
        based on field provenance analysis:

        For fields with OUTER provenance (e.g., subject from x = triple-subject(dt)):
            ForAll i in result: Exists j in outer_collection:
                outer_filter(outer_collection[j]) AND
                result_field(result[i]) = outer_field(outer_collection[j])

        For fields with CONSTANT provenance (e.g., predicate = same-as):
            ForAll i in result: Exists j in outer_collection:
                outer_filter(outer_collection[j]) AND
                result_field(result[i]) = constant_field(outer_collection[j])

        This enables proving properties like:
            (forall (t $result)
              (exists (dt (. delta triples))
                (term-eq (triple-predicate dt) (triple-predicate t))))
        """
        axioms: List[z3.BoolRef] = []

        # Need Seq for $result
        if '$result' not in translator.list_seqs:
            return axioms

        result_seq = translator.list_seqs['$result']

        # Get or create Seq for outer source collection
        outer_seq = None
        outer_name = None

        if isinstance(pattern.outer_collection, Symbol):
            outer_name = pattern.outer_collection.name
            if outer_name not in translator.list_seqs:
                translator._create_list_seq(outer_name)
            outer_seq = translator.list_seqs.get(outer_name)
        elif is_form(pattern.outer_collection, '.') and len(pattern.outer_collection) >= 3:
            # Field access: (. obj field)
            obj = pattern.outer_collection[1]
            field = pattern.outer_collection[2]
            if isinstance(obj, Symbol) and isinstance(field, Symbol):
                outer_name = translator.field_collection_key(obj.name, field.name)
                if outer_name not in translator.list_seqs:
                    translator._create_list_seq(outer_name)
                outer_seq = translator.list_seqs.get(outer_name)
        elif isinstance(pattern.outer_collection, SList) and len(pattern.outer_collection) >= 1:
            # Function call collection (from callback desugaring):
            # (fn-name arg1 arg2 ...)
            head = pattern.outer_collection[0]
            if isinstance(head, Symbol):
                outer_name = f"_call_{head.name}"
                if outer_name not in translator.list_seqs:
                    translator._create_list_seq(outer_name)
                outer_seq = translator.list_seqs.get(outer_name)

        if outer_seq is None:
            return axioms

        # Create index variables
        result_idx = z3.Int('_nested_res_i')
        outer_idx = z3.Int('_nested_outer_j')

        # Save and set up variable bindings
        old_outer_binding = translator.variables.get(pattern.outer_loop_var)

        try:
            # Bind outer loop var to outer element at j
            translator.variables[pattern.outer_loop_var] = outer_seq[outer_idx]

            # Also bind outer_bindings variables through resolution
            old_bindings = {}
            for var_name, var_expr in pattern.outer_bindings.items():
                old_bindings[var_name] = translator.variables.get(var_name)
                # Translate the binding expression with outer_loop_var bound
                var_z3 = translator.translate_expr(var_expr)
                if var_z3 is not None:
                    translator.variables[var_name] = var_z3

            # Determine type prefix from collection
            type_prefix = self._infer_element_type_prefix(pattern.outer_collection)

            # Build outer filter constraint (if any)
            outer_filter_z3 = None
            if pattern.outer_filter is not None:
                # Resolve filter condition through outer_let_bindings
                resolved_filter = self._resolve_filter_condition(
                    pattern.outer_filter, pattern.outer_let_bindings
                )
                outer_filter_z3 = translator.translate_expr(resolved_filter)

            # Build field constraints based on provenance
            field_constraints = []

            for result_field, source_expr in pattern.field_mappings.items():
                provenance = pattern.field_provenance.get(result_field, FieldSource.OUTER)

                # Determine result accessor name
                if type_prefix:
                    result_accessor_name = f"{type_prefix}-{result_field}"
                else:
                    result_accessor_name = result_field

                # Create the result field function
                result_field_func_name = f"fn_{result_accessor_name}_1"
                if result_field_func_name not in translator.variables:
                    result_field_func = z3.Function(
                        result_field_func_name,
                        z3.IntSort(),
                        z3.IntSort()
                    )
                    translator.variables[result_field_func_name] = result_field_func
                else:
                    result_field_func = translator.variables[result_field_func_name]

                result_field_z3 = result_field_func(result_seq[result_idx])

                # Get equality function
                eq_func = self._get_type_equality_function(result_accessor_name, translator)

                if provenance == FieldSource.CONSTANT:
                    # Constant field: result field equals constant from outer source
                    # For same-as predicate: triple-predicate(result[i]) = triple-predicate(outer[j])
                    # (since both are filtered to have same-as predicate)
                    outer_field_z3 = result_field_func(outer_seq[outer_idx])
                    if eq_func is not None:
                        field_constraints.append(eq_func(result_field_z3, outer_field_z3))
                    else:
                        field_constraints.append(result_field_z3 == outer_field_z3)

                elif provenance == FieldSource.OUTER:
                    # Outer field: result field equals expression derived from outer var
                    # Resolve through bindings
                    resolved_expr = self._resolve_through_context(
                        source_expr, pattern.outer_bindings
                    )
                    source_z3 = translator.translate_expr(resolved_expr)
                    if source_z3 is not None:
                        if eq_func is not None:
                            field_constraints.append(eq_func(result_field_z3, source_z3))
                        else:
                            field_constraints.append(result_field_z3 == source_z3)

                elif provenance == FieldSource.INNER:
                    # Inner field: derived from inner loop variable
                    # Find which inner loop this field comes from by resolving through bindings
                    inner_loop = self._find_inner_loop_for_field(
                        source_expr, pattern.inner_loops, pattern.outer_bindings
                    )
                    if inner_loop is not None:
                        # Create a Seq for the inner collection
                        # Resolve collection expression through outer bindings
                        resolved_coll = self._resolve_through_context(
                            inner_loop.collection, pattern.outer_bindings
                        )
                        inner_seq = translator._get_or_create_collection_seq(resolved_coll)
                        if inner_seq is not None:
                            inner_idx = z3.Int(f'_nested_inner_k_{result_field}')
                            # Resolve the source expression through inner bindings
                            # to find which field of the inner element maps to the result field
                            inner_field_expr = self._resolve_inner_field_accessor(
                                source_expr, inner_loop
                            )
                            if inner_field_expr is not None:
                                inner_field_func_name = f"fn_{inner_field_expr}_1"
                                if inner_field_func_name not in translator.variables:
                                    inner_field_func = z3.Function(
                                        inner_field_func_name,
                                        z3.IntSort(), z3.IntSort()
                                    )
                                    translator.variables[inner_field_func_name] = inner_field_func
                                else:
                                    inner_field_func = translator.variables[inner_field_func_name]

                                # Build inner existential constraints
                                inner_parts = [
                                    inner_idx >= 0,
                                    inner_idx < z3.Length(inner_seq),
                                    eq_func(result_field_z3, inner_field_func(inner_seq[inner_idx]))
                                    if eq_func is not None
                                    else result_field_z3 == inner_field_func(inner_seq[inner_idx])
                                ]

                                inner_constraint = z3.Exists(
                                    [inner_idx],
                                    z3.And(*inner_parts)
                                )
                                field_constraints.append(inner_constraint)

                # MIXED provenance - skip, too complex

            if not field_constraints:
                return axioms

            # Build the outer existence axiom:
            # ForAll i in result: Exists j in outer:
            #     outer_filter(outer[j]) AND field_constraints
            outer_constraint_parts = [
                outer_idx >= 0,
                outer_idx < z3.Length(outer_seq)
            ]
            if outer_filter_z3 is not None:
                outer_constraint_parts.append(outer_filter_z3)
            outer_constraint_parts.extend(field_constraints)

            outer_existence = z3.Exists([outer_idx], z3.And(*outer_constraint_parts))

            axiom = z3.ForAll([result_idx],
                z3.Implies(
                    z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                    outer_existence
                )
            )
            axioms.append(axiom)

            # Size relationship: result size <= outer size
            # (may be much smaller due to filtering and join)
            size_axiom = z3.Length(result_seq) <= z3.Length(outer_seq)
            axioms.append(size_axiom)

            # Generate instantiated axioms from imported postconditions for inner loops
            for inner_loop in pattern.inner_loops:
                resolved_coll = self._resolve_through_context(
                    inner_loop.collection, pattern.outer_bindings
                )
                inst_inner_seq = translator._get_or_create_collection_seq(resolved_coll)
                if inst_inner_seq is not None:
                    inst_axioms = self._generate_instantiated_inner_axioms(
                        inner_loop, inst_inner_seq, pattern.outer_bindings, translator
                    )
                    axioms.extend(inst_axioms)

            # Match context subset axioms for nested patterns
            if pattern.match_context is not None:
                match_axioms = self._generate_match_subset_axioms(
                    pattern.match_context, outer_seq, outer_name, translator
                )
                axioms.extend(match_axioms)

        finally:
            # Restore bindings
            if old_outer_binding is not None:
                translator.variables[pattern.outer_loop_var] = old_outer_binding
            elif pattern.outer_loop_var in translator.variables:
                del translator.variables[pattern.outer_loop_var]

            for var_name, old_val in old_bindings.items():
                if old_val is not None:
                    translator.variables[var_name] = old_val
                elif var_name in translator.variables:
                    del translator.variables[var_name]

        return axioms

    def _generate_match_subset_axioms(
        self,
        match_ctx: 'MatchContext',
        child_seq: z3.SeqRef,
        child_name: Optional[str],
        translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Generate subset axioms connecting a match-bound collection to its parent.

        When iterating over pred-triples from:
            (match (map-get (. delta by-predicate) KEY)
              ((some pred-triples) (for-each (dt pred-triples) ...)))

        pred-triples is a subset of delta.triples with predicate == KEY.

        Generates:
        1. Subset axiom: ForAll j in child: Exists k in parent: child[j] == parent[k]
        2. Predicate filter: ForAll j in child: field_predicate(child[j]) == KEY
           (only when KEY is resolvable and collection_expr is a by-predicate index)
        """
        axioms: List[z3.BoolRef] = []

        # Determine the parent collection from the match_ctx.collection_expr
        # e.g., (. delta by-predicate) → parent is (. delta triples) conceptually
        # But for the subset axiom, we connect child elements to the parent list.
        # The collection_expr is what map-get operates on (the index map).
        # To find the parent list, we look at the structure:
        # (. delta by-predicate) → parent is (. delta triples)
        parent_seq = None
        parent_name = None

        if is_form(match_ctx.collection_expr, '.') and len(match_ctx.collection_expr) >= 3:
            obj = match_ctx.collection_expr[1]
            field = match_ctx.collection_expr[2]
            if isinstance(obj, Symbol) and isinstance(field, Symbol):
                # The index is (. obj by-predicate), parent list is (. obj triples)
                parent_name = translator.field_collection_key(obj.name, "triples")
                if parent_name not in translator.list_seqs:
                    translator._create_list_seq(parent_name)
                parent_seq = translator.list_seqs.get(parent_name)

        if parent_seq is None:
            return axioms

        # 1. Subset axiom: every element of child_seq exists in parent_seq
        child_idx = z3.Int('_match_child_j')
        parent_idx = z3.Int('_match_parent_k')

        subset_axiom = z3.ForAll([child_idx],
            z3.Implies(
                z3.And(child_idx >= 0, child_idx < z3.Length(child_seq)),
                z3.Exists([parent_idx],
                    z3.And(
                        parent_idx >= 0,
                        parent_idx < z3.Length(parent_seq),
                        child_seq[child_idx] == parent_seq[parent_idx]
                    )
                )
            )
        )
        axioms.append(subset_axiom)

        # 2. Predicate filter axiom: elements have predicate == KEY
        # Only when the collection is a by-predicate index
        if is_form(match_ctx.collection_expr, '.') and len(match_ctx.collection_expr) >= 3:
            field = match_ctx.collection_expr[2]
            if isinstance(field, Symbol) and field.name == 'by-predicate':
                # Translate the key expression
                key_z3 = translator.translate_expr(match_ctx.key_expr)
                if key_z3 is not None:
                    # Get predicate field accessor
                    pred_func_name = "fn_triple-predicate_1"
                    if pred_func_name not in translator.variables:
                        pred_func = z3.Function(pred_func_name, z3.IntSort(), z3.IntSort())
                        translator.variables[pred_func_name] = pred_func
                    else:
                        pred_func = translator.variables[pred_func_name]

                    # Get equality function
                    eq_func = self._get_type_equality_function('triple-predicate', translator)

                    filter_idx = z3.Int('_match_filter_j')
                    elem_pred = pred_func(child_seq[filter_idx])
                    if eq_func is not None:
                        pred_constraint = eq_func(elem_pred, key_z3)
                    else:
                        pred_constraint = elem_pred == key_z3

                    filter_axiom = z3.ForAll([filter_idx],
                        z3.Implies(
                            z3.And(filter_idx >= 0, filter_idx < z3.Length(child_seq)),
                            pred_constraint
                        )
                    )
                    axioms.append(filter_axiom)

        # Size constraint
        axioms.append(z3.Length(child_seq) <= z3.Length(parent_seq))

        return axioms

    def _generate_instantiated_inner_axioms(
        self,
        inner_loop: 'InnerLoopInfo',
        inner_seq: z3.SeqRef,
        outer_bindings: Dict[str, SExpr],
        translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Generate instantiated axioms from imported function postconditions.

        Instead of universally quantifying over ALL function parameters (which Z3
        can't instantiate efficiently), binds parameters to their actual argument
        values from the call site and quantifies only over the loop index variable.

        For inner_loop.collection = (indexed-graph-match arena g (some y) (some same-as) no-term)
        with @assume (forall (t $result) (indexed-graph-contains g t)):

        Generates:
            ForAll idx: 0 <= idx < Length(inner_seq) =>
                fn_indexed-graph-contains_2(g, inner_seq[idx])
        """
        axioms: List[z3.BoolRef] = []

        # Resolve collection through outer bindings
        resolved_coll = self._resolve_through_context(
            inner_loop.collection, outer_bindings
        )

        # Extract function name from the resolved collection (head symbol)
        if not isinstance(resolved_coll, SList) or len(resolved_coll) < 1:
            return axioms
        head = resolved_coll[0]
        if not isinstance(head, Symbol):
            return axioms
        fn_name = head.name

        # Look up function signature
        sig = self.imported_defs.functions.get(fn_name)
        if sig is None:
            return axioms

        # Collect all postconditions and assumptions
        annotations = list(sig.postconditions) + list(sig.assumptions)

        # Rewrite @callback-assume annotations as collection postconditions
        # (@callback-assume callback (prop $callback-arg)) becomes
        # (forall (t $result) (prop t)) with $callback-arg → t
        if sig.callback_assumptions:
            for ca in sig.callback_assumptions:
                rewritten = self._rewrite_callback_assume_as_postcondition(ca.assumption)
                if rewritten is not None:
                    annotations.append(rewritten)

        if not annotations:
            return axioms

        # Build param-name -> call-arg mapping
        # For callback-desugared calls, the callback param is NOT in the call args
        call_args = resolved_coll.items[1:]  # arguments after function name
        param_names = sig.params

        # Filter out callback parameter names (they won't have corresponding call args)
        if sig.callback_assumptions:
            callback_param_names = {ca.callback_param for ca in sig.callback_assumptions}
            param_names = [p for p in sig.params if p not in callback_param_names]

        if len(call_args) != len(param_names):
            return axioms

        for post in annotations:
            try:
                inst_axiom = self._instantiate_postcondition_for_inner_loop(
                    fn_name, param_names, call_args, post, inner_seq, translator
                )
                if inst_axiom is not None:
                    axioms.append(inst_axiom)
            except Exception:
                continue

        # Generate containment congruence axioms:
        # If an element is contained in a graph, then a make-triple with the same
        # fields is also contained. This bridges indexed-graph-contains(g, elem)
        # to indexed-graph-contains(g, make-triple(arena, s, p, o)) when elem has
        # those fields.
        axioms.extend(self._generate_containment_congruence_axioms(
            sig, call_args, inner_seq, translator
        ))

        return axioms

    def _rewrite_callback_assume_as_postcondition(self, assumption: SExpr) -> Optional[SExpr]:
        """Rewrite a @callback-assume property into a collection postcondition.

        Transforms: (indexed-graph-contains g $callback-arg)
        Into:       (forall (t $result) (indexed-graph-contains g t))

        Replaces $callback-arg with t and wraps in (forall (t $result) ...).
        """
        t_sym = Symbol('_cb_t')
        rewritten_body = self._substitute_callback_arg(assumption, t_sym)
        # Wrap: (forall (_cb_t $result) rewritten_body)
        binding = SList([t_sym, Symbol('$result')])
        return SList([Symbol('forall'), binding, rewritten_body])

    def _substitute_callback_arg(self, expr: SExpr, replacement: Symbol) -> SExpr:
        """Replace $callback-arg with replacement symbol throughout expr."""
        if isinstance(expr, Symbol):
            if expr.name == '$callback-arg':
                return replacement
            return expr
        if isinstance(expr, SList):
            new_items = [self._substitute_callback_arg(item, replacement) for item in expr.items]
            result = SList(new_items)
            if hasattr(expr, 'line'):
                result.line = expr.line
                result.col = expr.col
            return result
        return expr

    def _generate_containment_congruence_axioms(
        self,
        sig: 'FunctionSignature',
        call_args: List[SExpr],
        inner_seq: z3.SeqRef,
        translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Generate axioms bridging element containment to constructed element containment.

        When an inner loop iterates over query results contained in a container g,
        and the property checks contains(g, constructor(arena, fields...)),
        Z3 needs to know that containment depends on field values, not object identity.

        This works with any record type that has:
        1. A constructor function with @post mapping params to fields
        2. A contains predicate (e.g., *-contains)

        For each element elem in inner_seq that is known to be in g:
            contains(g, constructor(arena, field1(elem), field2(elem), ...))

        This is sound because containment checks by field equality.
        """
        axioms: List[z3.BoolRef] = []

        # Check if there's a containment axiom (forall (t $result) (contains g t))
        # and a container parameter we can identify
        contains_func_name = None
        graph_arg_z3 = None

        for post in list(sig.postconditions) + list(sig.assumptions):
            if not isinstance(post, SList) or len(post) < 3:
                continue
            head = post[0]
            if not (isinstance(head, Symbol) and head.name == 'forall'):
                continue
            binding = post[1]
            if not (isinstance(binding, SList) and len(binding) == 2):
                continue
            bind_coll = binding[1]
            if not (isinstance(bind_coll, Symbol) and bind_coll.name == '$result'):
                continue
            body = post[2]
            # Check for (fn-contains g t) pattern
            if isinstance(body, SList) and len(body) >= 3:
                fn_head = body[0]
                if isinstance(fn_head, Symbol) and 'contains' in fn_head.name:
                    contains_func_name = fn_head.name
                    # The container arg is body[1], resolve through params
                    graph_ref = body[1]
                    if isinstance(graph_ref, Symbol):
                        # Find this param in the call args
                        for i, pname in enumerate(sig.params):
                            if pname == graph_ref.name and i < len(call_args):
                                graph_arg_z3 = translator.translate_expr(call_args[i])
                                break
                    break

        if contains_func_name is None or graph_arg_z3 is None:
            return axioms

        # Find a constructor function with postconditions that define field mappings.
        # Search all imported functions for constructors (functions with @post mapping
        # params to fields via accessor postconditions like (== (accessor $result) param)).
        constructor_name = None
        constructor_sig = None

        for fn_name, fn_sig in self.imported_defs.functions.items():
            if not fn_sig.postconditions:
                continue
            # A constructor typically has postconditions mapping params to fields
            field_mappings = self._infer_constructor_field_mappings(fn_sig)
            if field_mappings and len(field_mappings) >= 2:
                # Found a constructor with field mappings
                constructor_name = fn_name
                constructor_sig = fn_sig
                break

        if constructor_name is None or constructor_sig is None:
            return axioms

        # Get field mappings: param_name -> (accessor_name, field_name)
        field_mappings = self._infer_constructor_field_mappings(constructor_sig)

        # Get or create the contains function
        contains_key = f"fn_{contains_func_name}_2"
        if contains_key not in translator.variables:
            contains_func = z3.Function(
                contains_key, z3.IntSort(), z3.IntSort(), z3.BoolSort()
            )
            translator.variables[contains_key] = contains_func
        else:
            contains_func = translator.variables[contains_key]

        # Get or create constructor function
        constructor_key = f"fn_{constructor_name}_{len(constructor_sig.params)}"
        if constructor_key not in translator.variables:
            arg_sorts = [z3.IntSort()] * len(constructor_sig.params)
            constructor_func = z3.Function(constructor_key, *arg_sorts, z3.IntSort())
            translator.variables[constructor_key] = constructor_func
        else:
            constructor_func = translator.variables[constructor_key]

        # Get or create field accessor functions and build constructor args
        idx = z3.Int('_congr_idx')
        elem = inner_seq[idx]

        # Get arena (first call arg, typically)
        arena_z3 = translator.variables.get('arena')
        if arena_z3 is None:
            arena_z3 = translator.translate_expr(call_args[0]) if call_args else None
        if arena_z3 is None:
            return axioms

        # Build constructor arguments in parameter order
        constructor_args = []
        for param_name in constructor_sig.params:
            if param_name == 'arena':
                constructor_args.append(arena_z3)
            elif param_name in field_mappings:
                accessor_name = field_mappings[param_name]
                acc_key = f"fn_{accessor_name}_1"
                if acc_key not in translator.variables:
                    acc_func = z3.Function(acc_key, z3.IntSort(), z3.IntSort())
                    translator.variables[acc_key] = acc_func
                else:
                    acc_func = translator.variables[acc_key]
                constructor_args.append(acc_func(elem))
            else:
                # Unknown param - can't build complete constructor call
                return axioms

        constructed = constructor_func(*constructor_args)

        axiom = z3.ForAll([idx],
            z3.Implies(
                z3.And(idx >= 0, idx < z3.Length(inner_seq)),
                z3.Implies(
                    contains_func(graph_arg_z3, elem),
                    contains_func(graph_arg_z3, constructed)
                )
            )
        )
        axioms.append(axiom)

        return axioms

    def _infer_constructor_field_mappings(
        self, sig: 'FunctionSignature'
    ) -> Dict[str, str]:
        """Infer param_name -> accessor_name mappings from constructor postconditions.

        For postconditions like:
            (== (triple-subject $result) s)
            (== (triple-predicate $result) p)
            (== (triple-object $result) o)

        Returns: {'s': 'triple-subject', 'p': 'triple-predicate', 'o': 'triple-object'}
        """
        mappings: Dict[str, str] = {}

        for post in sig.postconditions:
            if not isinstance(post, SList) or len(post) != 3:
                continue
            head = post[0]
            if not isinstance(head, Symbol) or head.name not in ('==', 'term-eq'):
                continue

            lhs, rhs = post[1], post[2]

            # Try both orientations: (== (accessor $result) param) and (== param (accessor $result))
            for accessor_side, param_side in [(lhs, rhs), (rhs, lhs)]:
                if (isinstance(accessor_side, SList) and len(accessor_side) == 2 and
                    isinstance(accessor_side[0], Symbol) and
                    isinstance(accessor_side[1], Symbol) and
                    accessor_side[1].name == '$result' and
                    isinstance(param_side, Symbol) and
                    param_side.name in sig.params):
                    mappings[param_side.name] = accessor_side[0].name
                    break

        return mappings

    def _instantiate_postcondition_for_inner_loop(
        self,
        fn_name: str,
        param_names: List[str],
        call_args: List[SExpr],
        post: SExpr,
        inner_seq: z3.SeqRef,
        translator: 'Z3Translator'
    ) -> Optional[z3.BoolRef]:
        """Instantiate a single postcondition for a concrete inner loop call.

        Binds function parameters to their actual argument values, then:
        - If postcondition is (forall (t $result) body): quantify over index into inner_seq
        - Otherwise: translate directly with bound params
        """
        # Save translator state
        saved_vars: Dict[str, object] = {}
        for pname in param_names:
            saved_vars[pname] = translator.variables.get(pname)
        saved_result = translator.variables.get('$result')
        saved_result_seq = translator.list_seqs.get('$result')

        try:
            # Bind each param to translated call arg
            for pname, arg in zip(param_names, call_args):
                arg_z3 = translator.translate_expr(arg)
                if arg_z3 is not None:
                    translator.variables[pname] = arg_z3

            # Try to simplify (implies (!= param (none)) body) when param is (some x)
            simplified = self._try_simplify_option_implies(
                post, param_names, call_args, translator
            )
            if simplified is not None:
                post = simplified

            # Check if this is a (forall (t $result) body) pattern
            if self._postcondition_treats_result_as_collection(post):
                return self._instantiate_collection_postcondition(
                    fn_name, post, inner_seq, translator
                )
            else:
                # Simple postcondition - translate directly
                translator.variables['$result'] = inner_seq
                post_z3 = translator.translate_expr(post)
                if post_z3 is not None and z3.is_bool(post_z3):
                    return post_z3
                return None

        finally:
            # Restore translator state
            for pname, saved_val in saved_vars.items():
                if saved_val is None:
                    translator.variables.pop(pname, None)
                else:
                    translator.variables[pname] = saved_val
            if saved_result is None:
                translator.variables.pop('$result', None)
            else:
                translator.variables['$result'] = saved_result
            if saved_result_seq is None:
                translator.list_seqs.pop('$result', None)
            else:
                translator.list_seqs['$result'] = saved_result_seq

    def _try_simplify_option_implies(
        self,
        post: SExpr,
        param_names: List[str],
        call_args: List[SExpr],
        translator: 'Z3Translator'
    ) -> Optional[SExpr]:
        """Simplify (implies (!= param (none)) body) when param is known to be (some x).

        When the actual call argument for a parameter is (some x), the condition
        (!= param (none)) is trivially true. We can replace the implies with just
        the body, substituting (unwrap param) with x directly.

        This avoids Z3 needing to reason through union_tag/union_payload indirection.

        Returns simplified postcondition or None if no simplification applies.
        """
        if not (isinstance(post, SList) and len(post) == 3):
            return None
        head = post[0]
        if not (isinstance(head, Symbol) and head.name == 'implies'):
            return None

        cond = post[1]
        body = post[2]

        # Check for (!= param (none)) pattern
        if not (isinstance(cond, SList) and len(cond) == 3):
            return None
        cond_head = cond[0]
        if not (isinstance(cond_head, Symbol) and cond_head.name == '!='):
            return None

        # Find which side is (none) and which is the param
        param_side = None
        if isinstance(cond[2], SList) and len(cond[2]) == 1:
            c2_head = cond[2][0]
            if isinstance(c2_head, Symbol) and c2_head.name == 'none':
                param_side = cond[1]
        if param_side is None and isinstance(cond[1], SList) and len(cond[1]) == 1:
            c1_head = cond[1][0]
            if isinstance(c1_head, Symbol) and c1_head.name == 'none':
                param_side = cond[2]
        if param_side is None:
            return None

        if not isinstance(param_side, Symbol):
            return None

        # Find which param this is and what the actual call arg is
        param_idx = None
        for i, pname in enumerate(param_names):
            if pname == param_side.name:
                param_idx = i
                break
        if param_idx is None:
            return None

        call_arg = call_args[param_idx]

        # Check if call arg is (some x)
        if not (isinstance(call_arg, SList) and len(call_arg) == 2):
            return None
        arg_head = call_arg[0]
        if not (isinstance(arg_head, Symbol) and arg_head.name == 'some'):
            return None

        # The condition is trivially true. Substitute (unwrap param) with x in body.
        inner_value = call_arg[1]
        simplified_body = self._substitute_unwrap(body, param_side.name, inner_value)

        # Also bind the param directly to the unwrapped value in the translator
        inner_z3 = translator.translate_expr(inner_value)
        if inner_z3 is not None:
            # Override the param binding to be the unwrapped value directly
            # (instead of fn_some_1(x) which requires union_payload to extract)
            translator.variables[param_side.name] = inner_z3

        return simplified_body

    def _substitute_unwrap(
        self, expr: SExpr, param_name: str, replacement: SExpr
    ) -> SExpr:
        """Replace (unwrap param_name) with replacement in expr."""
        if isinstance(expr, SList):
            # Check for (unwrap param_name)
            if (len(expr) == 2 and isinstance(expr[0], Symbol)
                    and expr[0].name == 'unwrap'
                    and isinstance(expr[1], Symbol)
                    and expr[1].name == param_name):
                return replacement
            # Recurse
            new_items = [self._substitute_unwrap(item, param_name, replacement)
                         for item in expr.items]
            return SList(new_items, expr.line, expr.col)
        return expr

    def _instantiate_collection_postcondition(
        self,
        fn_name: str,
        post: SExpr,
        inner_seq: z3.SeqRef,
        translator: 'Z3Translator'
    ) -> Optional[z3.BoolRef]:
        """Handle (forall (t $result) body) by quantifying over inner_seq index.

        Also handles (implies cond (forall (t $result) body)) by translating
        the condition and wrapping the result in Implies.

        Produces: ForAll idx: 0 <= idx < Length(inner_seq) => body[t/inner_seq[idx]]
        """
        if not (isinstance(post, SList) and len(post) >= 3):
            return None
        head = post[0]

        # Handle (implies cond (forall ...))
        if isinstance(head, Symbol) and head.name == 'implies' and len(post) == 3:
            cond = post[1]
            inner_post = post[2]
            cond_z3 = translator.translate_expr(cond)
            if cond_z3 is None:
                return None
            inner_result = self._instantiate_collection_postcondition(
                fn_name, inner_post, inner_seq, translator
            )
            if inner_result is None:
                return None
            return z3.Implies(cond_z3, inner_result)

        # Parse the (forall (binding_var $result) body) form
        if not (isinstance(head, Symbol) and head.name == 'forall'):
            return None
        binding = post[1]
        if not (isinstance(binding, SList) and len(binding) == 2):
            return None
        bind_var = binding[0]
        bind_coll = binding[1]
        if not (isinstance(bind_var, Symbol) and isinstance(bind_coll, Symbol)
                and bind_coll.name == '$result'):
            return None
        body = post[2]
        var_name = bind_var.name

        # Create index variable
        idx = z3.Int(f'_inst_{fn_name}_idx')

        # Bind the iteration variable to inner_seq[idx]
        saved_var = translator.variables.get(var_name)
        try:
            translator.variables[var_name] = inner_seq[idx]
            body_z3 = translator.translate_expr(body)
            if body_z3 is None or not z3.is_bool(body_z3):
                return None

            return z3.ForAll([idx],
                z3.Implies(
                    z3.And(idx >= 0, idx < z3.Length(inner_seq)),
                    body_z3
                )
            )
        finally:
            if saved_var is None:
                translator.variables.pop(var_name, None)
            else:
                translator.variables[var_name] = saved_var

    def _extract_filter_conditions_from_loop(
        self, fn_body: SExpr
    ) -> Tuple[List[SExpr], Dict[str, SExpr]]:
        """Extract filter conditions from (when ...) clauses leading to list-push.

        For patterns like:
            (let ((mut result (list-new arena Type)))
              (for-each (dt source)
                (when cond1
                  (let ((x expr1))
                    (when cond2
                      (list-push result ...)))))
              result)

        Returns:
            - List of filter condition expressions [cond1, cond2]
            - Bindings context for variable resolution {'x': expr1}

        This is used to generate completeness axioms for filtered map patterns.
        """
        # Must be a let expression
        if not is_form(fn_body, 'let') or len(fn_body) < 3:
            return [], {}

        bindings = fn_body[1]
        if not isinstance(bindings, SList):
            return [], {}

        # Build initial bindings context from outer let
        initial_bindings: Dict[str, SExpr] = {}
        for binding in bindings.items:
            if isinstance(binding, SList) and len(binding) >= 2:
                first = binding[0]
                if isinstance(first, Symbol):
                    if first.name == 'mut' and len(binding) >= 3:
                        var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                        var_value = binding[2]
                    else:
                        var_name = first.name
                        var_value = binding[1]
                    if var_name and var_value:
                        initial_bindings[var_name] = var_value

        # Find for-each loop in body (also inside match branches)
        body_exprs = fn_body.items[2:]
        result = self._find_for_each_and_collect_conditions(body_exprs, initial_bindings)
        if result is not None:
            return result

        return [], initial_bindings

    def _find_for_each_and_collect_conditions(
        self, stmts: list, bindings: Dict[str, 'SExpr']
    ) -> Optional[Tuple[List['SExpr'], Dict[str, 'SExpr']]]:
        """Find for-each in statements (including inside match branches) and collect filter conditions."""
        for stmt in stmts:
            if is_form(stmt, 'for-each') and len(stmt) >= 3:
                loop_body = stmt.items[2:]
                conditions, bindings_ctx = self._collect_filter_conditions(
                    loop_body, bindings.copy()
                )
                return conditions, bindings_ctx
            # Recurse into match branches
            if is_form(stmt, 'match') and len(stmt) >= 3:
                for clause in stmt.items[2:]:
                    if isinstance(clause, SList) and len(clause) >= 2:
                        result = self._find_for_each_and_collect_conditions(
                            clause.items[1:], bindings.copy()
                        )
                        if result is not None:
                            return result
        return None

    def _collect_filter_conditions(
        self, stmts: List[SExpr], bindings: Dict[str, SExpr]
    ) -> Tuple[List[SExpr], Dict[str, SExpr]]:
        """Recursively collect filter conditions from when clauses on path to list-push.

        Traverses into when, let, and do forms, collecting:
        - Conditions from (when cond ...) clauses
        - Variable bindings from (let ((x val)) ...)

        Returns (conditions, bindings) when list-push is found, or ([], bindings) otherwise.
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Handle (when condition body)
            if is_form(stmt, 'when') and len(stmt) >= 3:
                condition = stmt[1]
                then_body = stmt[2]

                # Check if then_body contains list-push (possibly nested)
                if self._contains_list_push([then_body]):
                    # Recursively collect conditions from then_body
                    inner_conditions, inner_bindings = self._collect_filter_conditions(
                        [then_body], bindings.copy()
                    )
                    # Prepend this condition
                    return [condition] + inner_conditions, inner_bindings

            # Handle (let ((x val) ...) body...)
            if is_form(stmt, 'let') and len(stmt) >= 3:
                let_bindings = stmt[1]
                new_bindings = bindings.copy()

                # Extract bindings
                if isinstance(let_bindings, SList):
                    for binding in let_bindings.items:
                        if isinstance(binding, SList) and len(binding) >= 2:
                            var_name = None
                            var_value = None
                            if isinstance(binding[0], Symbol):
                                if binding[0].name == 'mut' and len(binding) >= 3:
                                    var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                                    var_value = binding[2]
                                else:
                                    var_name = binding[0].name
                                    var_value = binding[1]
                            if var_name and var_value:
                                new_bindings[var_name] = var_value

                # Recurse into let body
                inner_conditions, inner_bindings = self._collect_filter_conditions(
                    stmt.items[2:], new_bindings
                )
                if inner_conditions or self._contains_list_push(stmt.items[2:]):
                    return inner_conditions, inner_bindings

            # Handle (do body...)
            if is_form(stmt, 'do') and len(stmt) >= 2:
                inner_conditions, inner_bindings = self._collect_filter_conditions(
                    stmt.items[1:], bindings.copy()
                )
                if inner_conditions or self._contains_list_push(stmt.items[1:]):
                    return inner_conditions, inner_bindings

            # Found list-push - return empty conditions (base case)
            if is_form(stmt, 'list-push'):
                return [], bindings

        return [], bindings

    def _contains_list_push(self, stmts: List[SExpr]) -> bool:
        """Check if any statement contains a list-push call."""
        for stmt in stmts:
            if is_form(stmt, 'list-push'):
                return True
            if isinstance(stmt, SList):
                # Recurse into nested forms
                if is_form(stmt, 'when') and len(stmt) >= 3:
                    if self._contains_list_push([stmt[2]]):
                        return True
                elif is_form(stmt, 'let') and len(stmt) >= 3:
                    if self._contains_list_push(stmt.items[2:]):
                        return True
                elif is_form(stmt, 'do') and len(stmt) >= 2:
                    if self._contains_list_push(stmt.items[1:]):
                        return True
        return False

    def _resolve_filter_condition(
        self, condition: SExpr, bindings: Dict[str, SExpr]
    ) -> SExpr:
        """Resolve variables in filter condition through let bindings.

        Recursively substitutes variable references with their bound values.

        Returns fully resolved condition.
        """
        if isinstance(condition, Symbol):
            var_name = condition.name
            if var_name in bindings:
                return self._resolve_filter_condition(bindings[var_name], bindings)
            return condition

        if isinstance(condition, SList) and len(condition) >= 1:
            resolved_items = [
                self._resolve_filter_condition(item, bindings)
                for item in condition.items
            ]
            return SList(resolved_items, condition.line, condition.col)

        return condition

    def _find_inner_loop_for_field(
        self, source_expr: SExpr, inner_loops: List['InnerLoopInfo'],
        outer_bindings: Dict[str, SExpr]
    ) -> Optional['InnerLoopInfo']:
        """Find which inner loop a field's source expression derives from.

        For source_expr like (triple-object yo-triple), finds the inner loop
        whose loop_var is 'yo-triple'.
        """
        # Check if source_expr is a function call on an inner loop var
        if isinstance(source_expr, SList) and len(source_expr) >= 2:
            arg = source_expr[-1]  # Last arg is typically the loop var
            if isinstance(arg, Symbol):
                for inner_loop in inner_loops:
                    if arg.name == inner_loop.loop_var:
                        return inner_loop

        # Check if source_expr is a symbol that's an inner loop var directly
        if isinstance(source_expr, Symbol):
            for inner_loop in inner_loops:
                if source_expr.name == inner_loop.loop_var:
                    return inner_loop

        return None

    def _resolve_inner_field_accessor(
        self, source_expr: SExpr, inner_loop: 'InnerLoopInfo'
    ) -> Optional[str]:
        """Get the field accessor name from a source expression involving an inner loop var.

        For source_expr like (triple-object yo-triple), returns 'triple-object'.
        """
        if isinstance(source_expr, SList) and len(source_expr) >= 2:
            head = source_expr[0]
            if isinstance(head, Symbol):
                return head.name
        return None

    def _infer_element_type_prefix(self, collection: SExpr) -> Optional[str]:
        """Infer the element type prefix from a collection expression.

        For (. delta triples) where triples is a list of Triple, returns "triple".
        For a variable 'triples' that is (List Triple), returns "triple".

        This is used to construct field accessor names like triple-subject.
        """
        # Check for field access: (. obj field)
        if is_form(collection, '.') and len(collection) >= 3:
            field = collection[2]
            if isinstance(field, Symbol):
                field_name = field.name
                # Common patterns: "triples" -> "triple", "terms" -> "term"
                if field_name.endswith('s'):
                    return field_name[:-1]  # Remove trailing 's'
                return field_name

        # Check for simple variable name
        if isinstance(collection, Symbol):
            var_name = collection.name
            if var_name.endswith('s'):
                return var_name[:-1]
            return var_name

        return None

    def _get_type_equality_function(
        self, accessor_name: str, translator: 'Z3Translator'
    ) -> Optional[z3.FuncDeclRef]:
        """Get the appropriate equality function for a field type.

        Infers the equality function from the accessor name pattern:
        {type}-{field} -> {type}-eq. For example, triple-predicate -> triple-eq.

        IMPORTANT: Only returns an equality function if:
        1. The function is imported with a postcondition defining its semantics, OR
        2. The function already exists in the translator's variables

        If no imported equality function is found, returns None to use native ==.
        This ensures axioms align with what Z3 can actually reason about.

        Returns Z3 function or None if no specific equality function found.
        """
        # Infer from accessor pattern: {type}-{field} -> {type}-eq
        if '-' in accessor_name:
            type_prefix = accessor_name.rsplit('-', 1)[0]
            eq_func_name = f"fn_{type_prefix}-eq_2"
            if eq_func_name in translator.variables:
                return translator.variables[eq_func_name]
            # Check if type-eq is imported with semantics
            if self._has_imported_equality_semantics(f'{type_prefix}-eq'):
                eq_func = z3.Function(
                    eq_func_name,
                    z3.IntSort(), z3.IntSort(), z3.BoolSort()
                )
                translator.variables[eq_func_name] = eq_func
                return eq_func
            # No imported equality function with semantics - use native ==
            return None

        return None

    def _has_imported_equality_semantics(self, eq_func_name: str) -> bool:
        """Check if an equality function is imported with postcondition semantics.

        Returns True if the function is imported with (@post (== $result (== a b))).
        """
        sig = self.imported_defs.functions.get(eq_func_name)
        if sig is None or len(sig.params) != 2:
            return False

        # Check postconditions for pattern: (== $result (== a b))
        for post in sig.postconditions:
            if is_form(post, '==') and len(post) == 3:
                lhs, rhs = post[1], post[2]
                # Check for (== $result (== ...)) or (== (== ...) $result)
                if isinstance(lhs, Symbol) and lhs.name == '$result':
                    if is_form(rhs, '==') and len(rhs) == 3:
                        return True
                elif isinstance(rhs, Symbol) and rhs.name == '$result':
                    if is_form(lhs, '==') and len(lhs) == 3:
                        return True
        return False

    def _extract_imported_equality_axioms(
        self, translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Extract axioms from imported equality functions.

        For imported functions like term-eq with postcondition:
            (@post (== $result (== a b)))

        Generate a Z3 axiom that tells Z3 what the equality function means:
            ForAll a, b: fn_term-eq_2(a, b) == (a == b)

        This allows Z3 to reason about equality in properties.
        """
        axioms: List[z3.BoolRef] = []

        for fn_name, sig in self.imported_defs.functions.items():
            # Check if this looks like an equality function
            if not (fn_name.endswith('-eq') or fn_name.endswith('?')):
                continue

            # Must have exactly 2 parameters
            if len(sig.params) != 2:
                continue

            # Check postconditions for pattern: (== $result (== a b))
            found_eq_axiom = False
            for post in sig.postconditions:
                eq_axiom = self._parse_equality_postcondition(
                    fn_name, sig.params, post, translator
                )
                if eq_axiom is not None:
                    axioms.append(eq_axiom)
                    found_eq_axiom = True

            # No fallback: if a function lacks an explicit (@post (== $result (== a b)))
            # postcondition, we do NOT assume structural equality. Functions like
            # approx-eq or case-insensitive comparisons would be unsound with that axiom.
            # To get equality semantics, add the postcondition to the function definition.

        return axioms

    def _parse_equality_postcondition(
        self,
        fn_name: str,
        params: List[str],
        post: SExpr,
        translator: 'Z3Translator'
    ) -> Optional[z3.BoolRef]:
        """Parse an equality postcondition and generate a Z3 axiom.

        Pattern: (== $result (== a b)) or (== $result (== b a))
        where a, b are the function's parameters.

        Returns: ForAll a, b: fn_name(a, b) == (a == b)
        """
        if not is_form(post, '==') or len(post) != 3:
            return None

        lhs, rhs = post[1], post[2]

        # Check for (== $result (== ...))
        if not (isinstance(lhs, Symbol) and lhs.name == '$result'):
            # Try swapped: (== (== ...) $result)
            if isinstance(rhs, Symbol) and rhs.name == '$result':
                lhs, rhs = rhs, lhs
            else:
                return None

        # rhs should be (== a b) where a, b are the params
        if not is_form(rhs, '==') or len(rhs) != 3:
            return None

        inner_lhs, inner_rhs = rhs[1], rhs[2]
        if not (isinstance(inner_lhs, Symbol) and isinstance(inner_rhs, Symbol)):
            return None

        # Check that these are the function's parameters
        param_names = {inner_lhs.name, inner_rhs.name}
        if param_names != set(params):
            return None

        # Create or get the Z3 function
        func_key = f"fn_{fn_name}_2"
        if func_key not in translator.variables:
            func = z3.Function(func_key, z3.IntSort(), z3.IntSort(), z3.BoolSort())
            translator.variables[func_key] = func
        else:
            func = translator.variables[func_key]

        # Create quantified variables
        a = z3.Int(f'{fn_name}_a')
        b = z3.Int(f'{fn_name}_b')

        # Generate axiom: ForAll a, b: fn(a, b) == (a == b)
        axiom = z3.ForAll([a, b], func(a, b) == (a == b))
        return axiom

    def _extract_imported_postcondition_axioms(
        self, translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Extract universal axioms from imported function postconditions.

        For imported functions with postconditions, generate universally quantified
        axioms that enable reasoning about relational properties involving multiple
        calls to the same function.

        For example, for a function like indexed-graph-match with postcondition:
            (@post (forall (t $result) (indexed-graph-contains g t)))

        We generate an axiom that universally quantifies over the function's parameters:
            ForAll arena, g, s, p, o:
                ForAll t in (indexed-graph-match arena g s p o):
                    indexed-graph-contains(g, t)

        This enables verifying properties like completeness-forward that involve
        both filtered and unfiltered calls to the same function.
        """
        axioms: List[z3.BoolRef] = []

        for fn_name, sig in self.imported_defs.functions.items():
            # Skip equality functions - handled by _extract_imported_equality_axioms
            if fn_name.endswith('-eq') and len(sig.params) == 2:
                continue

            for post in sig.postconditions:
                axiom = self._translate_postcondition_as_universal_axiom(
                    fn_name, sig, post, translator
                )
                if axiom is not None:
                    axioms.append(axiom)

            # Also generate axioms from @assume annotations
            for assume in sig.assumptions:
                axiom = self._translate_postcondition_as_universal_axiom(
                    fn_name, sig, assume, translator
                )
                if axiom is not None:
                    axioms.append(axiom)

        return axioms

    def _translate_postcondition_as_universal_axiom(
        self,
        fn_name: str,
        sig: 'FunctionSignature',
        post: SExpr,
        translator: 'Z3Translator'
    ) -> Optional[z3.BoolRef]:
        """Translate a single postcondition as a universal axiom.

        The postcondition is universally quantified over the function's parameters.
        $result is replaced with a call to the function with the quantified params.

        For example:
            fn: indexed-graph-match(arena, g, s, p, o)
            @post: (forall (t $result) (pred t))

        Becomes:
            ForAll arena, g, s, p, o:
                ForAll t in (indexed-graph-match arena g s p o):
                    pred(t)
        """
        from .types import FunctionSignature

        if not sig.params:
            return None

        # Create quantified variables for each parameter
        param_vars: List[z3.ArithRef] = []
        param_map: Dict[str, z3.ArithRef] = {}

        for i, param_name in enumerate(sig.params):
            # Create a unique Z3 variable for this parameter
            var = z3.Int(f'_ax_{fn_name}_{param_name}')
            param_vars.append(var)
            param_map[param_name] = var

        # Create or get the Z3 function for the function call
        func_key = f"fn_{fn_name}_{len(sig.params)}"
        if func_key not in translator.variables:
            # Determine return sort based on postcondition patterns
            # If postcondition uses forall/exists with $result, it's a collection
            if self._postcondition_treats_result_as_collection(post):
                # For collections, we model the function result as an Int (id)
                # and create a corresponding Seq if needed
                return_sort = z3.IntSort()
            else:
                return_sort = z3.IntSort()

            arg_sorts = [z3.IntSort()] * len(sig.params)
            func = z3.Function(func_key, *arg_sorts, return_sort)
            translator.variables[func_key] = func
        else:
            func = translator.variables[func_key]

        # Create the function call with quantified parameters
        fn_result = func(*param_vars)

        # Save current variable bindings
        saved_vars: Dict[str, z3.ExprRef] = {}
        for param_name, param_var in param_map.items():
            saved_vars[param_name] = translator.variables.get(param_name)
            translator.variables[param_name] = param_var

        # For collection-returning functions, set up a Seq for $result
        # that represents the function's result with these specific parameters
        saved_result = translator.variables.get('$result')
        saved_result_seq = translator.list_seqs.get('$result')

        try:
            # If postcondition uses $result as a collection, create a Seq for it
            if self._postcondition_treats_result_as_collection(post):
                # Create a unique Seq name for this function call
                seq_name = f'_ax_{fn_name}_result'
                if seq_name not in translator.list_seqs:
                    translator._create_list_seq(seq_name)
                result_seq = translator.list_seqs.get(seq_name)
                if result_seq is not None:
                    translator.list_seqs['$result'] = result_seq
                    # Also bind $result to the function result (id)
                    translator.variables['$result'] = fn_result
            else:
                translator.variables['$result'] = fn_result

            # Translate the postcondition body
            post_z3 = translator.translate_expr(post)
            if post_z3 is None or not z3.is_bool(post_z3):
                return None

            # Wrap in universal quantifier over all parameters
            if param_vars:
                return z3.ForAll(param_vars, post_z3)
            else:
                return post_z3

        finally:
            # Restore variable bindings
            for param_name, saved_val in saved_vars.items():
                if saved_val is None:
                    if param_name in translator.variables:
                        del translator.variables[param_name]
                else:
                    translator.variables[param_name] = saved_val

            if saved_result is None:
                if '$result' in translator.variables:
                    del translator.variables['$result']
            else:
                translator.variables['$result'] = saved_result

            if saved_result_seq is None:
                if '$result' in translator.list_seqs:
                    del translator.list_seqs['$result']
            else:
                translator.list_seqs['$result'] = saved_result_seq

    def _postcondition_treats_result_as_collection(self, post: SExpr) -> bool:
        """Check if a postcondition treats $result as a collection.

        Returns True if the postcondition contains patterns like:
        - (forall (t $result) ...)
        - (exists (t $result) ...)
        - (list-len $result)
        """
        if isinstance(post, SList) and len(post) >= 1:
            head = post[0]
            if isinstance(head, Symbol):
                # Check for (forall (t $result) ...) or (exists (t $result) ...)
                if head.name in ('forall', 'exists') and len(post) >= 3:
                    binding = post[1]
                    if isinstance(binding, SList) and len(binding) == 2:
                        coll = binding[1]
                        if isinstance(coll, Symbol) and coll.name == '$result':
                            return True

                # Check for (list-len $result)
                if head.name == 'list-len' and len(post) >= 2:
                    arg = post[1]
                    if isinstance(arg, Symbol) and arg.name == '$result':
                        return True

            # Recursively check subexpressions
            for item in post.items:
                if self._postcondition_treats_result_as_collection(item):
                    return True

        return False

    def _generate_exists_search_axioms(
        self, pattern: ExistsSearchPatternInfo, translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Generate axioms for an exists-search loop pattern.

        For the pattern:
          (let ((mut found false))
            (for-each (v coll) (when pred (set! found true)))
            (if found branch-when-found branch-when-not-found))

        Determines which branch returns (none) vs (some ...) and generates:
          union_tag($result) == none_tag ↔ ∃i: 0 <= i < Len(seq) ∧ pred(seq[i])

        or the negation, depending on which branch is (none).
        """
        axioms: List[z3.BoolRef] = []

        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # Determine which branch returns (none) and which returns (some ...)
        # (none) has union tag 0, (some ...) has tag 1
        found_returns_none = (isinstance(pattern.return_when_found, SList) and
                              is_form(pattern.return_when_found, 'none'))
        not_found_returns_none = (isinstance(pattern.return_when_not_found, SList) and
                                  is_form(pattern.return_when_not_found, 'none'))

        if not found_returns_none and not not_found_returns_none:
            # Check for bare symbol 'none'
            found_returns_none = (isinstance(pattern.return_when_found, Symbol) and
                                  pattern.return_when_found.name == 'none')
            not_found_returns_none = (isinstance(pattern.return_when_not_found, Symbol) and
                                      pattern.return_when_not_found.name == 'none')

        if not found_returns_none and not not_found_returns_none:
            return axioms

        # Get or create union_tag function
        tag_func_name = "union_tag"
        if tag_func_name not in translator.variables:
            tag_func = z3.Function(tag_func_name, z3.IntSort(), z3.IntSort())
            translator.variables[tag_func_name] = tag_func
        else:
            tag_func = translator.variables[tag_func_name]

        # Get collection sequence
        if not translator.use_seq_encoding:
            return axioms

        seq = translator._get_or_create_collection_seq(pattern.collection)
        if seq is None:
            return axioms

        # Create index variable and element at that index
        idx_var = z3.Int(f'_exists_search_idx')
        elem_at_idx = seq[idx_var]

        # Translate the predicate with loop_var bound to seq[idx]
        old_binding = translator.variables.get(pattern.loop_var)
        try:
            translator.variables[pattern.loop_var] = elem_at_idx
            pred_z3 = translator.translate_expr(pattern.predicate)
        finally:
            if old_binding is not None:
                translator.variables[pattern.loop_var] = old_binding
            elif pattern.loop_var in translator.variables:
                del translator.variables[pattern.loop_var]

        if pred_z3 is None or not z3.is_bool(pred_z3):
            return axioms

        # Build existential: ∃i: 0 <= i < Length(seq) ∧ pred(seq[i])
        existential = z3.Exists([idx_var], z3.And(
            idx_var >= 0,
            idx_var < z3.Length(seq),
            pred_z3
        ))

        # none tag is 0 in the Option type encoding
        none_tag = z3.IntVal(0)

        if found_returns_none:
            # found=true → (none), found=false → (some ...)
            # So: union_tag($result) == 0 ↔ ∃v: pred(v)
            axioms.append((tag_func(result_var) == none_tag) == existential)
        else:
            # found=true → (some ...), found=false → (none)
            # So: union_tag($result) == 0 ↔ ¬∃v: pred(v)
            axioms.append((tag_func(result_var) == none_tag) == z3.Not(existential))

        return axioms

    def _generate_emptiness_universality_axioms(
        self, pattern: ConditionalPushPatternInfo, translator: 'Z3Translator'
    ) -> List[z3.BoolRef]:
        """Generate emptiness-universality axioms for nested conditional push.

        For nested for-each loops with conditional push via enum match,
        generates:
          Length(seq_$result) == 0 ↔
            ForAll i,j: 0 <= i < Len(outer_seq) ∧ 0 <= j < Len(inner_seq)
              → no_push_condition(outer_seq[i], inner_seq[j])

        This enables proving properties like:
          (== (list-len $result) 0)
            ↔ (forall (v coll1) (forall (o coll2) (== (fn v o) variant)))
        """
        axioms: List[z3.BoolRef] = []

        if not translator.use_seq_encoding:
            return axioms

        # Get result sequence
        result_seq = translator.list_seqs.get('$result')
        if result_seq is None:
            return axioms

        # Get outer collection sequence
        outer_seq = translator._get_or_create_collection_seq(pattern.outer_collection)
        if outer_seq is None:
            return axioms

        # Get inner collection sequence — use resolved expression if available
        inner_coll_for_seq = pattern.inner_collection_resolved or pattern.inner_collection
        inner_seq = translator._get_or_create_collection_seq(inner_coll_for_seq)
        if inner_seq is None:
            return axioms

        # Also equate the let-bound variable seq with the resolved seq
        # (e.g., seq_other-values == seq_fn_resolve-path_...)
        if (pattern.inner_collection_resolved is not None and
                isinstance(pattern.inner_collection, Symbol)):
            let_seq = translator._get_or_create_collection_seq(pattern.inner_collection)
            if let_seq is not None and not z3.eq(let_seq, inner_seq):
                axioms.append(let_seq == inner_seq)

        # Use the same index variable naming as the translator (_idx_{loop_var})
        # so Z3 can syntactically match with property expressions
        i_var = z3.Int(f'_idx_{pattern.outer_loop_var}')
        j_var = z3.Int(f'_idx_{pattern.inner_loop_var}')

        # Bind loop vars to seq elements
        outer_elem = outer_seq[i_var]
        inner_elem = inner_seq[j_var]

        old_outer = translator.variables.get(pattern.outer_loop_var)
        old_inner = translator.variables.get(pattern.inner_loop_var)

        try:
            translator.variables[pattern.outer_loop_var] = outer_elem
            translator.variables[pattern.inner_loop_var] = inner_elem

            # Translate the match scrutinee (resolved through let bindings)
            scrutinee_z3 = translator.translate_expr(pattern.match_scrutinee_resolved)
            if scrutinee_z3 is None:
                return axioms

            # Build the no-push condition
            if pattern.no_push_tag is not None:
                # No push when scrutinee == no_push_tag
                tag_z3 = translator.translate_expr(Symbol(pattern.no_push_tag))
                if tag_z3 is None:
                    return axioms
                no_push_cond = (scrutinee_z3 == tag_z3)
            elif pattern.push_tag is not None:
                # Push when scrutinee == push_tag, so no push when !=
                tag_z3 = translator.translate_expr(Symbol(pattern.push_tag))
                if tag_z3 is None:
                    return axioms
                no_push_cond = (scrutinee_z3 != tag_z3)
            else:
                return axioms

        finally:
            if old_outer is not None:
                translator.variables[pattern.outer_loop_var] = old_outer
            elif pattern.outer_loop_var in translator.variables:
                del translator.variables[pattern.outer_loop_var]
            if old_inner is not None:
                translator.variables[pattern.inner_loop_var] = old_inner
            elif pattern.inner_loop_var in translator.variables:
                del translator.variables[pattern.inner_loop_var]

        # Build: Length($result) == 0 ↔
        #   ForAll i,j: (0 <= i < Len(outer) ∧ 0 <= j < Len(inner)) → no_push_cond
        # IMPORTANT: Must match the And nesting from translator._translate_forall_collection
        # which builds z3.And(z3.And(i>=0, i<Len), z3.And(j>=0, j<Len)) — nested 2-ary Ands.
        # A flat 4-ary And is semantically equivalent but Z3 can't match them structurally.
        implication = z3.Implies(
            z3.And(
                z3.And(i_var >= 0, i_var < z3.Length(outer_seq)),
                z3.And(j_var >= 0, j_var < z3.Length(inner_seq)),
            ),
            no_push_cond
        )
        multi_pat = z3.MultiPattern(outer_elem, inner_elem)
        universality = z3.ForAll(
            [i_var, j_var], implication, patterns=[multi_pat]
        )

        # Match the exact Z3 AST structure the translator produces for the property:
        #   ForAll(...) == (0 == Length($result))
        # The operand order matters — (0 == Length) not (Length == 0)
        axioms.append(universality == (z3.IntVal(0) == z3.Length(result_seq)))

        return axioms

    def _generate_filter_axioms(self, pattern: FilterPatternInfo,
                                translator: Z3Translator) -> List:
        """Generate Z3 axioms for detected filter pattern.

        Axioms:
        1. Size constraint: (size result) <= (size source) where source is the parent object
        2. Exclusion constraint: If predicate is (not (eq item x)), then (not (contains result x))
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # Translate the collection
        collection_z3 = translator.translate_expr(pattern.collection)
        if collection_z3 is None:
            return axioms

        # Axiom 1: Size constraint - result size <= source size
        # If collection is (. obj field), compare to obj's size, not field's size
        # This matches postconditions like (graph-size $result) <= (graph-size g)
        source_obj = None
        if is_form(pattern.collection, '.') and len(pattern.collection) >= 2:
            # Collection is (. obj field) - use obj as the source for size comparison
            source_obj = translator.translate_expr(pattern.collection[1])

        if source_obj is not None:
            # Use the source object for size comparison
            # Try common size accessor patterns
            size_func_name = "field_size"
            if size_func_name not in translator.variables:
                size_func = z3.Function(size_func_name, z3.IntSort(), z3.IntSort())
                translator.variables[size_func_name] = size_func
            else:
                size_func = translator.variables[size_func_name]

            result_size = size_func(result_var)
            source_size = size_func(source_obj)
            axioms.append(result_size <= source_size)
            axioms.append(result_size >= 0)
        else:
            # Fallback: compare to collection size directly
            size_func_name = "field_size"
            if size_func_name not in translator.variables:
                size_func = z3.Function(size_func_name, z3.IntSort(), z3.IntSort())
                translator.variables[size_func_name] = size_func
            else:
                size_func = translator.variables[size_func_name]

            result_size = size_func(result_var)
            collection_size = size_func(collection_z3)
            axioms.append(result_size <= collection_size)
            axioms.append(result_size >= 0)

        # Axiom 2: Exclusion constraint for (not (eq item x)) patterns
        if pattern.is_negated and pattern.excluded_item is not None:
            excluded_z3 = translator.translate_expr(pattern.excluded_item)
            if excluded_z3 is not None:
                # Get or create contains predicate function
                contains_func_name = "fn_graph-contains_2"  # 2-arity contains
                if contains_func_name not in translator.variables:
                    contains_func = z3.Function(contains_func_name, z3.IntSort(), z3.IntSort(), z3.BoolSort())
                    translator.variables[contains_func_name] = contains_func
                else:
                    contains_func = translator.variables[contains_func_name]

                # The excluded item is NOT in the result
                axioms.append(z3.Not(contains_func(result_var, excluded_z3)))

        return axioms

    def _detect_count_pattern(self, body: SExpr) -> Optional[CountPatternInfo]:
        """Detect count loop pattern in function body.

        Pattern:
        (let ((mut count 0))
          (for-each (item collection)
            (if predicate
              (set! count (+ count 1))))
          count)

        Returns CountPatternInfo if detected, None otherwise.
        """
        # Must be a let expression
        if not is_form(body, 'let') or len(body) < 3:
            return None

        bindings = body[1]
        if not isinstance(bindings, SList):
            return None

        # Find mutable count binding initialized to 0
        count_var = None
        for binding in bindings.items:
            if self._is_mutable_binding(binding) and len(binding) >= 3:
                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                init_expr = binding[2]
                # Check if initialized to 0
                if var_name and isinstance(init_expr, Number) and init_expr.value == 0:
                    count_var = var_name
                    break

        if not count_var:
            return None

        # Find for-each loop in body
        body_exprs = body.items[2:]
        for body_expr in body_exprs:
            if is_form(body_expr, 'for-each') and len(body_expr) >= 3:
                loop_binding = body_expr[1]
                if isinstance(loop_binding, SList) and len(loop_binding) >= 2:
                    loop_var = loop_binding[0].name if isinstance(loop_binding[0], Symbol) else None
                    collection = loop_binding[1]

                    if loop_var:
                        # Search loop body for (if predicate (set! count (+ count 1)))
                        loop_body = body_expr.items[2:]
                        predicate = self._find_count_increment_predicate(loop_body, count_var)
                        if predicate is not None:
                            return CountPatternInfo(
                                count_var=count_var,
                                collection=collection,
                                loop_var=loop_var,
                                predicate=predicate
                            )

        return None

    def _find_count_increment_predicate(self, stmts: List[SExpr], count_var: str) -> Optional[SExpr]:
        """Find the predicate in a count increment pattern.

        Looks for patterns like:
        - (if predicate (set! count (+ count 1)))
        - (when predicate (set! count (+ count 1)))
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Check for if/when with count increment
            if (is_form(stmt, 'if') or is_form(stmt, 'when')) and len(stmt) >= 3:
                predicate = stmt[1]
                then_branch = stmt[2]

                # Check if then branch is (set! count (+ count 1))
                if self._is_count_increment(then_branch, count_var):
                    return predicate

            # Recurse into nested let
            if is_form(stmt, 'let') and len(stmt) >= 3:
                nested_result = self._find_count_increment_predicate(stmt.items[2:], count_var)
                if nested_result is not None:
                    return nested_result

        return None

    def _is_count_increment(self, expr: SExpr, count_var: str) -> bool:
        """Check if expression is (set! count (+ count 1))."""
        if not is_form(expr, 'set!') or len(expr) < 3:
            return False

        target = expr[1]
        if not isinstance(target, Symbol) or target.name != count_var:
            return False

        value = expr[2]
        if not is_form(value, '+') or len(value) < 3:
            return False

        # Check for (+ count 1) or (+ 1 count)
        arg1 = value[1]
        arg2 = value[2]

        if isinstance(arg1, Symbol) and arg1.name == count_var:
            if isinstance(arg2, Number) and arg2.value == 1:
                return True
        if isinstance(arg2, Symbol) and arg2.name == count_var:
            if isinstance(arg1, Number) and arg1.value == 1:
                return True

        return False

    def _counter_rises_by_one(self, body: 'SExpr', name: str) -> bool:
        """True if `name` starts at zero and every write adds exactly one."""
        writes: List = []

        def walk(node):
            if not isinstance(node, SList) or len(node) < 1:
                return
            head = node[0]
            if isinstance(head, Symbol):
                if head.name in ('fn', 'quote'):
                    return
                if head.name == 'set!' and len(node) >= 3 and isinstance(node[1], Symbol):
                    if node[1].name == name:
                        writes.append(node[2])
                    return
            for item in node.items:
                walk(item)

        walk(body)
        if len(writes) != 1:
            return False
        value = writes[0]
        if not (isinstance(value, SList) and len(value) == 3):
            return False
        head, left, right = value[0], value[1], value[2]
        if not (isinstance(head, Symbol) and head.name == '+'):
            return False
        if isinstance(left, Number) and left.value == 1:
            # (+ 1 count), which the detector accepts as well
            left, right = right, left
        if not (isinstance(left, Symbol) and left.name == name):
            return False
        if not (isinstance(right, Number) and right.value == 1):
            return False
        # The assigned value may itself assign - `(do (set! count 100) 0)` looks
        # like one write from outside.
        nested: List = []

        def nested_walk(node):
            if not isinstance(node, SList) or len(node) < 1:
                return
            head_sym = node[0]
            if isinstance(head_sym, Symbol):
                if head_sym.name in ('fn', 'quote'):
                    return
                if head_sym.name == 'set!' and len(node) >= 3:
                    nested.append(node)
            for item in node.items:
                nested_walk(item)

        nested_walk(value)
        if nested:
            return False
        return self._binding_starts_at_zero(body, name)

    def _binding_starts_at_zero(self, body: 'SExpr', name: str) -> bool:
        """True if every `let` binding of `name` initialises it to 0."""
        found = False

        def walk(node):
            nonlocal found
            if not isinstance(node, SList):
                return True
            if is_form(node, 'let') and len(node) >= 2 and isinstance(node[1], SList):
                for binding in node[1].items:
                    if not (isinstance(binding, SList) and len(binding) >= 2):
                        continue
                    first = binding[0]
                    if isinstance(first, Symbol) and first.name == 'mut' and len(binding) >= 3:
                        bound, init = binding[1], binding[2]
                    elif isinstance(first, Symbol):
                        bound, init = first, binding[1]
                    elif (isinstance(first, SList) and len(first) >= 2
                          and isinstance(first[0], Symbol) and first[0].name == 'mut'):
                        # ((mut name) init), the third spelling _translate_let takes
                        bound, init = first[1], binding[1]
                    else:
                        continue
                    if isinstance(bound, Symbol) and bound.name == name:
                        found = True
                        if not (isinstance(init, Number) and init.value == 0):
                            return False
            for item in node.items:
                if not walk(item):
                    return False
            return True

        return walk(body) and found

    def _count_returns(self, expr: 'SExpr') -> int:
        """How many `(return ...)` forms this function body has of its own."""
        if not isinstance(expr, SList) or len(expr) < 1:
            return 0
        head = expr[0]
        if isinstance(head, Symbol):
            if head.name in ('fn', 'quote'):
                return 0
            if head.name == 'return':
                return 1 + sum(self._count_returns(item) for item in expr.items[1:])
        return sum(self._count_returns(item) for item in expr.items)

    def _generate_count_axioms(self, pattern: CountPatternInfo,
                               translator: Z3Translator,
                               body: Optional['SExpr'] = None) -> List:
        """Generate Z3 axioms for detected count pattern.

        Axioms:
        1. Count is non-negative: $result >= 0
        2. Count is bounded by collection size: $result <= (list-len collection)
        """
        axioms = []
        # The bound describes the counter. _detect_count_pattern only finds a
        # count-shaped loop; it does not check that the function returns the
        # counter, and a function that returns something else would otherwise
        # inherit the bound.
        counted = translator.variables.get(pattern.count_var)
        result_var = translator.variables.get('$result')
        if counted is None or result_var is None:
            return axioms
        if not (z3.is_expr(counted) and counted.sort() == z3.IntSort()):
            return axioms
        if body is not None:
            returned = self._get_return_expr(body)
            # A trailing `(return count)` is not an early exit - it is how the
            # function ends. Unwrap it, then require that nothing else returns:
            # any other exit yields something the loop never counted, and this
            # bound is asserted about $result on every path.
            trailing_return = is_form(returned, 'return') and len(returned) >= 2
            if trailing_return:
                returned = returned[1]
            other_returns = self._count_returns(body) > (1 if trailing_return else 0)
            if other_returns:
                return axioms
            if not (isinstance(returned, Symbol) and returned.name == pattern.count_var):
                return axioms
            # The bound is one element at most, so the counter has to be raised
            # by exactly one at exactly one place. _detect_count_pattern matches
            # the first increment it finds and says nothing about the rest, so a
            # second one - or a (set! count 100) - would go unnoticed.
            if not self._counter_rises_by_one(body, pattern.count_var):
                return axioms
        elif not z3.eq(counted, result_var):
            return axioms

        # Only add numeric axioms if result is an integer type
        if result_var.sort() != z3.IntSort():
            return axioms

        # Axiom 1: Count is non-negative
        axioms.append(result_var >= 0)

        # Axiom 2: Count is bounded by collection size.
        # Stated with the same length terms `(list-len collection)` translates
        # to in a contract - fn_list-len_1 was a fourth spelling that no goal
        # ever mentioned, so the bound was unusable (see #115's length bridge).
        length_terms, links = self._length_terms_for(pattern.collection, translator)
        axioms.extend(links)
        for term in length_terms:
            axioms.append(result_var <= term)

        return axioms

    def _detect_fold_pattern(self, body: SExpr) -> Optional[FoldPatternInfo]:
        """Detect fold/accumulation loop pattern in function body.

        Pattern:
        (let ((mut acc init))
          (for-each (item collection)
            (set! acc (op acc item)))
          acc)

        Returns FoldPatternInfo if detected, None otherwise.
        """
        # Must be a let expression
        if not is_form(body, 'let') or len(body) < 3:
            return None

        bindings = body[1]
        if not isinstance(bindings, SList):
            return None

        # Find mutable accumulator binding
        acc_var = None
        init_value = None
        for binding in bindings.items:
            if self._is_mutable_binding(binding) and len(binding) >= 3:
                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                init_expr = binding[2]
                # Accept numeric or simple initializers (not empty collection inits)
                if var_name and not self._is_empty_collection_init(init_expr):
                    acc_var = var_name
                    init_value = init_expr
                    break

        if not acc_var or init_value is None:
            return None

        # Find for-each loop in body
        body_exprs = body.items[2:]
        for body_expr in body_exprs:
            if is_form(body_expr, 'for-each') and len(body_expr) >= 3:
                loop_binding = body_expr[1]
                if isinstance(loop_binding, SList) and len(loop_binding) >= 2:
                    loop_var = loop_binding[0].name if isinstance(loop_binding[0], Symbol) else None
                    collection = loop_binding[1]

                    if loop_var:
                        # Search loop body for (set! acc (op acc item))
                        loop_body = body_expr.items[2:]
                        operator = self._find_accumulator_operator(loop_body, acc_var, loop_var)
                        if operator is not None:
                            return FoldPatternInfo(
                                acc_var=acc_var,
                                init_value=init_value,
                                collection=collection,
                                loop_var=loop_var,
                                operator=operator
                            )

        return None

    def _find_accumulator_operator(self, stmts: List[SExpr], acc_var: str, loop_var: str) -> Optional[str]:
        """Find the operator in a fold/accumulation pattern.

        Looks for patterns like:
        - (set! acc (+ acc item))
        - (set! acc (* acc item))
        - (set! acc (max acc item))
        """
        for stmt in stmts:
            # Skip annotations
            if isinstance(stmt, SList) and len(stmt) >= 1:
                head = stmt[0]
                if isinstance(head, Symbol) and head.name.startswith('@'):
                    continue

            # Check for (set! acc (op acc item))
            if is_form(stmt, 'set!') and len(stmt) >= 3:
                target = stmt[1]
                if isinstance(target, Symbol) and target.name == acc_var:
                    value = stmt[2]
                    if isinstance(value, SList) and len(value) >= 3:
                        op = value[0]
                        if isinstance(op, Symbol):
                            # Check if it involves acc and loop_var
                            arg1 = value[1]
                            arg2 = value[2]
                            uses_acc = (isinstance(arg1, Symbol) and arg1.name == acc_var) or \
                                       (isinstance(arg2, Symbol) and arg2.name == acc_var)
                            uses_loop = (isinstance(arg1, Symbol) and arg1.name == loop_var) or \
                                        (isinstance(arg2, Symbol) and arg2.name == loop_var)
                            if uses_acc and uses_loop:
                                return op.name

            # Check for conditional accumulation (if pred (set! acc ...))
            if (is_form(stmt, 'if') or is_form(stmt, 'when')) and len(stmt) >= 3:
                then_branch = stmt[2]
                result = self._find_accumulator_operator([then_branch], acc_var, loop_var)
                if result is not None:
                    return result

            # Recurse into nested let
            if is_form(stmt, 'let') and len(stmt) >= 3:
                nested_result = self._find_accumulator_operator(stmt.items[2:], acc_var, loop_var)
                if nested_result is not None:
                    return nested_result

        return None

    def _generate_fold_axioms(self, pattern: FoldPatternInfo,
                              translator: Z3Translator) -> List:
        """Generate Z3 axioms for detected fold pattern.

        Axioms depend on the operator:
        - For '+': If init >= 0 and items non-negative, result >= init
        - For '*': Special handling for multiplication
        - For 'max'/'min': Result bounded by init and collection
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # Translate initial value
        init_z3 = translator.translate_expr(pattern.init_value)

        op = pattern.operator
        if op == '+':
            # For addition starting at 0, result is non-negative if items are
            if isinstance(pattern.init_value, Number) and pattern.init_value.value == 0:
                # Common case: sum starting at 0, items assumed non-negative
                # We can't prove this without knowing item signs, so just add non-negative constraint
                # if init is 0 (most common for sums)
                pass
            # For any + accumulator, result >= init if items are non-negative
            # This is a heuristic - we add it when init is a known value
            if init_z3 is not None:
                # Add axiom: result >= init (for non-negative items)
                # This is sound for counting/summing positive values
                pass

        elif op == 'max':
            # For max, result >= init
            if init_z3 is not None:
                axioms.append(result_var >= init_z3)

        elif op == 'min':
            # For min, result <= init
            if init_z3 is not None:
                axioms.append(result_var <= init_z3)

        return axioms


    # ============================================================================
    # Structural Push-Site Analysis
    # ============================================================================

    def _resolve_through_bindings(self, expr: 'SExpr', bindings: Dict[str, 'SExpr'],
                                   depth: int = 0) -> 'SExpr':
        """Resolve a variable through bindings, following chains up to a depth limit."""
        if depth > 10:
            return expr
        if isinstance(expr, Symbol) and expr.name in bindings:
            return self._resolve_through_bindings(bindings[expr.name], bindings, depth + 1)
        return expr

    def _exprs_structurally_equal(self, a: 'SExpr', b: 'SExpr') -> bool:
        """Check if two S-expressions are structurally identical."""
        if isinstance(a, Symbol) and isinstance(b, Symbol):
            return a.name == b.name
        if isinstance(a, Number) and isinstance(b, Number):
            return a.value == b.value
        if isinstance(a, String) and isinstance(b, String):
            return a.value == b.value
        if isinstance(a, SList) and isinstance(b, SList):
            if len(a) != len(b):
                return False
            return all(self._exprs_structurally_equal(ai, bi)
                       for ai, bi in zip(a.items, b.items))
        return False

    def _extract_constructor_fields(self, pushed_expr: 'SExpr',
                                     bindings: Dict[str, 'SExpr']
                                     ) -> Optional[Tuple[str, Dict[str, 'SExpr']]]:
        """Extract constructor name and field values from a pushed expression.

        For (make-triple arena S P O), returns:
            ("triple", {"subject": S, "predicate": P, "object": O})

        Uses imported postconditions to determine field mappings.
        Falls back to positional field names.
        """
        resolved = self._resolve_through_bindings(pushed_expr, bindings)
        if not isinstance(resolved, SList) or len(resolved) < 1:
            return None

        head = resolved[0]
        if not isinstance(head, Symbol):
            return None

        # Use imported postconditions for field mapping
        if hasattr(self, 'imported_defs') and self.imported_defs:
            mappings = self._infer_field_mappings_from_postconditions(
                head.name, resolved, bindings
            )
            if mappings:
                # Resolve each field value through bindings
                resolved_mappings = {}
                for field_name, field_expr in mappings.items():
                    resolved_mappings[field_name] = self._resolve_through_bindings(
                        field_expr, bindings
                    )
                type_prefix = head.name.replace('make-', '').replace('-new', '')
                return (type_prefix, resolved_mappings)

        # Fallback: positional for make-X patterns (skip arena at position 1)
        if head.name.startswith('make-') and len(resolved) >= 3:
            type_prefix = head.name[5:]  # strip "make-"
            mappings = {}
            for i, arg in enumerate(resolved.items[2:]):  # skip fn name and arena
                resolved_arg = self._resolve_through_bindings(arg, bindings)
                mappings[f'field_{i}'] = resolved_arg
            return (type_prefix, mappings)

        return None

    def _generate_structural_push_axioms(
        self, push_sites: List['PushSiteInfo'], translator: 'Z3Translator',
        fn_params: Optional[List[str]] = None
    ) -> List[z3.BoolRef]:
        """Generate axioms from structural analysis of push sites.

        Two kinds of axioms:
        1. Constant field: If the same field resolves to the same expression
           across ALL push sites, generate field(result[i]) == const.
        2. Novelty guard: If ALL push sites are guarded by
           (not (indexed-graph-contains g EXPR)) where EXPR is the pushed value,
           generate Not(indexed-graph-contains(g, result[i])).

        Args:
            push_sites: Collected push site information
            translator: Z3 translator for expression conversion
            fn_params: Function parameter names (treated as constants)

        Returns:
            List of Z3 axioms
        """
        if not push_sites:
            return []

        axioms: List[z3.BoolRef] = []

        # Need Seq for $result
        if '$result' not in translator.list_seqs:
            return axioms

        result_seq = translator.list_seqs['$result']
        result_idx = z3.Int('_struct_res_i')

        # --- Constant field axioms ---
        axioms.extend(self._generate_constant_field_axioms(
            push_sites, translator, result_seq, result_idx, fn_params
        ))

        # --- Novelty guard axioms ---
        axioms.extend(self._generate_guard_axioms(
            push_sites, translator, result_seq, result_idx
        ))

        return axioms

    def _generate_constant_field_axioms(
        self, push_sites: List['PushSiteInfo'], translator: 'Z3Translator',
        result_seq, result_idx, fn_params: Optional[List[str]] = None
    ) -> List[z3.BoolRef]:
        """Generate axioms for fields that are constant across all push sites."""
        axioms: List[z3.BoolRef] = []
        if fn_params is None:
            fn_params = []

        # Extract constructor fields from each push site
        all_site_fields: List[Optional[Tuple[str, Dict[str, 'SExpr']]]] = []
        for site in push_sites:
            fields = self._extract_constructor_fields(site.pushed_expr, site.bindings)
            all_site_fields.append(fields)

        # If any site doesn't have a constructor, we can't analyze fields
        if any(f is None for f in all_site_fields):
            return axioms

        # Get field names from first site
        first_type, first_fields = all_site_fields[0]

        # Check each field for constancy across all sites
        for field_name in first_fields:
            first_value = first_fields[field_name]

            # Check if this field has the same resolved value across all sites
            all_same = True
            for site_fields in all_site_fields[1:]:
                _, other_fields = site_fields
                if field_name not in other_fields:
                    all_same = False
                    break
                other_value = other_fields[field_name]
                if not self._exprs_structurally_equal(first_value, other_value):
                    all_same = False
                    break

            if not all_same:
                continue

            # Verify the constant value is truly constant (a literal, a function param,
            # or a call with only constant args like (make-iri arena OWL_SAME_AS))
            if not self._is_constant_expr(first_value, fn_params):
                continue

            # Translate the constant to Z3
            const_z3 = translator.translate_expr(first_value)
            if const_z3 is None:
                continue

            # Get or create field accessor function
            accessor_name = f"{first_type}-{field_name}" if first_type else field_name
            field_func_name = f"fn_{accessor_name}_1"
            if field_func_name not in translator.variables:
                field_func = z3.Function(
                    field_func_name, z3.IntSort(), z3.IntSort()
                )
                translator.variables[field_func_name] = field_func
            else:
                field_func = translator.variables[field_func_name]

            # Get appropriate equality function
            eq_func = self._get_type_equality_function(accessor_name, translator)

            # Generate: ForAll i, 0 <= i < Length(result) =>
            #           field(result[i]) == const
            result_field = field_func(result_seq[result_idx])
            if eq_func is not None:
                field_eq = eq_func(result_field, const_z3)
            else:
                field_eq = (result_field == const_z3)

            axiom = z3.ForAll([result_idx], z3.Implies(
                z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                field_eq
            ))
            axioms.append(axiom)

        return axioms

    def _generate_guard_axioms(
        self, push_sites: List['PushSiteInfo'], translator: 'Z3Translator',
        result_seq, result_idx
    ) -> List[z3.BoolRef]:
        """Generate axioms for guard conditions that hold across all push sites.

        Detects (not (indexed-graph-contains g EXPR)) guards where EXPR is
        the pushed expression (or resolves to the same variable).
        """
        axioms: List[z3.BoolRef] = []

        # Check if ALL push sites have a novelty guard
        all_have_novelty = True
        for site in push_sites:
            has_novelty = False
            for guard in site.guard_conditions:
                if self._is_novelty_guard(guard, site.pushed_expr, site.bindings):
                    has_novelty = True
                    break
            if not has_novelty:
                all_have_novelty = False
                break

        if not all_have_novelty:
            return axioms

        # Find the graph variable and contains function from the first site's guard
        first_site = push_sites[0]
        for guard in first_site.guard_conditions:
            guard_info = self._extract_novelty_guard_info(guard, first_site.pushed_expr,
                                                           first_site.bindings)
            if guard_info is not None:
                graph_expr, contains_fn_name = guard_info

                # Translate graph variable
                graph_z3 = translator.translate_expr(graph_expr)
                if graph_z3 is None:
                    break

                # Get or create the contains function
                if contains_fn_name not in translator.variables:
                    contains_func = z3.Function(
                        contains_fn_name, z3.IntSort(), z3.IntSort(), z3.BoolSort()
                    )
                    translator.variables[contains_fn_name] = contains_func
                else:
                    contains_func = translator.variables[contains_fn_name]

                # Generate: ForAll i, 0 <= i < Length(result) =>
                #           Not(contains(g, result[i]))
                axiom = z3.ForAll([result_idx], z3.Implies(
                    z3.And(result_idx >= 0, result_idx < z3.Length(result_seq)),
                    z3.Not(contains_func(graph_z3, result_seq[result_idx]))
                ))
                axioms.append(axiom)
                break

        return axioms

    def _is_novelty_guard(self, guard: 'SExpr', pushed_expr: 'SExpr',
                           bindings: Dict[str, 'SExpr']) -> bool:
        """Check if guard is (not (indexed-graph-contains g EXPR)) where EXPR
        is the pushed expression or resolves to the same thing."""
        if not is_form(guard, 'not') or len(guard) < 2:
            return False
        inner = guard[1]
        if not is_form(inner, 'indexed-graph-contains') or len(inner) < 3:
            return False
        # inner[1] = graph, inner[2] = the expression being checked
        checked_expr = inner[2]
        resolved_pushed = self._resolve_through_bindings(pushed_expr, bindings)
        resolved_checked = self._resolve_through_bindings(checked_expr, bindings)
        return self._exprs_structurally_equal(resolved_pushed, resolved_checked)

    def _extract_novelty_guard_info(
        self, guard: 'SExpr', pushed_expr: 'SExpr', bindings: Dict[str, 'SExpr']
    ) -> Optional[Tuple['SExpr', str]]:
        """Extract (graph_expr, contains_fn_name) from a novelty guard."""
        if not is_form(guard, 'not') or len(guard) < 2:
            return None
        inner = guard[1]
        if not is_form(inner, 'indexed-graph-contains') or len(inner) < 3:
            return None
        checked_expr = inner[2]
        resolved_pushed = self._resolve_through_bindings(pushed_expr, bindings)
        resolved_checked = self._resolve_through_bindings(checked_expr, bindings)
        if not self._exprs_structurally_equal(resolved_pushed, resolved_checked):
            return None
        graph_expr = inner[1]
        contains_fn_name = "fn_indexed-graph-contains_2"
        return (graph_expr, contains_fn_name)

    def _is_constant_expr(self, expr: 'SExpr', fn_params: List[str]) -> bool:
        """Check if an expression is constant for the duration of a function call.

        Constant means: literal, function parameter, or a call with only constant args.
        """
        if isinstance(expr, (Number, String)):
            return True
        if isinstance(expr, Symbol):
            # Function parameters are constant for the call
            if expr.name in fn_params:
                return True
            # ALL_CAPS identifiers are module-level constants
            if expr.name.isupper() or '_' in expr.name and all(
                c.isupper() or c == '_' for c in expr.name
            ):
                return True
            return False
        if isinstance(expr, SList) and len(expr) >= 1:
            head = expr[0]
            if isinstance(head, Symbol):
                # Constructor calls with constant args: (make-iri arena CONST)
                if head.name.startswith('make-'):
                    return all(
                        self._is_constant_expr(arg, fn_params)
                        or (isinstance(arg, Symbol) and arg.name == 'arena')
                        for arg in expr.items[1:]
                    )
            return False
        return False


__all__ = ['AxiomGenerationMixin']
