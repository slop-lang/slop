"""A callee's contract, assumed at one of its call sites.

Every phase that reasons across a call - the main model (Phase 12), the exact
push model and the loop-invariant walk - assumes the same thing about it: where
the call runs and its @pre holds, its @post and @property hold of the call's
own result. As one formula, `Implies(And(guard, *pre), post)`, with `$result`
read as the call's term and each parameter as the argument passed for it.

What that must never become is a fact about something else. The main model
used to read a callee's `$result` as the *caller's* `$result`, on every path,
without the callee's @pre (#169, #134): any call anywhere in a body - in one
branch, as a statement, inside a loop - spoke for what the caller returned. A
collection post had the same leak through the back door: the translator keeps
sequences by *name*, so a callee's `(forall (t $result) ...)` or
`(list-len items)` read whatever the caller had registered under `$result` or
`items`.
"""

from contextlib import contextmanager
from typing import Any, Callable, Iterable, List, Optional, Sequence, Set, Tuple

import z3

from slop.parser import SList, Symbol, Number, String, is_form
from slop.types import (
    PrimitiveType, RangeType, EnumType, RecordType, UnionType, OptionType, ResultType,
    ListType, PtrType,
)

_MISSING = object()

# Forms that read a collection out of the translator's name-keyed registries,
# and create an entry there for a name that has none. A callee's contract that
# reads its own parameter or result this way would read the caller's list of
# that name instead, or leave a fresh, shared one behind.
_NAME_KEYED_COLLECTION_READERS = frozenset((
    'list-contains', 'all-triples-have-predicate',
))


def callee_contract(tr, fn_name: str) -> Optional[Tuple[List[str], List[Any], List[Any]]]:
    """(params, preconditions, postconditions and properties) of a user function.

    A local definition wins over an imported signature of the same name. A
    @property holds of every call with no precondition, so it is assumed like a
    postcondition - under the same guard, which only weakens it.
    """
    registry = tr.function_registry
    if registry is not None and fn_name in registry.functions:
        fn_def = registry.functions[fn_name]
        return (list(fn_def.params), list(getattr(fn_def, 'preconditions', []) or []),
                list(fn_def.postconditions) + [expr for _, expr in fn_def.properties])
    sig = tr.imported_defs.functions.get(fn_name)
    if sig is not None:
        return (list(sig.params), list(getattr(sig, 'preconditions', []) or []),
                list(sig.postconditions) + list(getattr(sig, 'properties', []) or []))
    return None


def callee_mut_params(tr, fn_name: str) -> Set[str]:
    """The parameters of `fn_name` declared `mut`.

    A `mut` parameter is the callee's own copy of the value (#180). Named in a
    postcondition it means the copy as the callee left it, which the caller
    never sees: the caller's argument keeps the value it passed (#230).
    """
    registry = tr.function_registry
    if registry is not None and fn_name in registry.functions:
        fn_def = registry.functions[fn_name]
        return {p for p, mode in zip(fn_def.params, fn_def.param_modes) if mode == 'mut'}
    sig = tr.imported_defs.functions.get(fn_name)
    if sig is not None:
        return {p for p, mode in zip(sig.params, getattr(sig, 'param_modes', []) or [])
                if mode == 'mut'}
    return set()


# Forms that change the collection their first operand names.
_COLLECTION_WRITES = frozenset((
    'list-push', 'list-pop', 'list-set', 'list-clear', 'list-insert', 'list-remove',
    'map-put', 'map-remove', 'map-clear', 'set-put', 'set-remove', 'set-clear',
))


def _root_and_field(target):
    """(name, first field or None) for `p`, `p.f...` or `(. ... (. p f) ...)`."""
    if isinstance(target, Symbol):
        parts = target.name.split('.')
        return parts[0], (parts[1] if len(parts) > 1 else None)
    if is_form(target, '.') and len(target) >= 3:
        root, field_name = _root_and_field(target[1])
        if root is None:
            return None, None
        if field_name is None:
            field_name = target[2].name if isinstance(target[2], Symbol) else '?'
        return root, field_name
    return None, None


def _writes_to(body, name: str) -> Optional[Set[str]]:
    """The fields of `name` that `body` may change, or None if it may change all of it.

    A `set!` of the name or a field of it, a collection write through it, its
    address taken, or a closure capturing it (a `mut` parameter is captured by
    reference). Over-approximate: a shadowing local of the same name counts.
    """
    fields: Set[str] = set()
    whole = False

    def note(target):
        nonlocal whole
        root, field_name = _root_and_field(target)
        if root == name:
            if field_name is None:
                whole = True
            else:
                fields.add(field_name)

    def walk(node):
        nonlocal whole
        if not isinstance(node, SList) or len(node) == 0:
            return
        head = node[0]
        if isinstance(head, Symbol):
            if head.name == 'quote':
                return
            if head.name == 'set!':
                if (len(node) == 4 and isinstance(node[1], Symbol) and node[1].name == name
                        and isinstance(node[2], Symbol)):
                    fields.add(node[2].name)        # (set! p f v)
                elif len(node) >= 2:
                    note(node[1])
            elif head.name in _COLLECTION_WRITES and len(node) >= 2:
                note(node[1])
            elif head.name in ('addr', 'fn', 'lambda') and _names_any(node, {name}):
                whole = True
        for item in node.items:
            walk(item)

    walk(body)
    return None if whole else fields


def _mut_reads_unchanged(tr, fn_name: str, expr, mut_params: Set[str]) -> bool:
    """True if every read of a `mut` parameter in `expr` sees what was passed in.

    A `mut` parameter in a postcondition is the callee's copy as it left it
    (#230). Where the callee never changes the part read, that is the value
    the caller passed: a field of value type the body never writes, or the
    whole parameter when the body writes none of it. growl's delta-add pushes
    to `(. d triples)` and posts about `(. d iteration)`.
    """
    registry = tr.function_registry
    fn_def = registry.functions.get(fn_name) if registry is not None else None
    types = _callee_types(tr, fn_name)
    if types is None:
        return False
    param_types = types[0]
    if fn_def is not None:
        forms = list(getattr(fn_def, 'body_forms', None) or [])
        if not forms:
            return False
        body = SList([Symbol('do')] + forms)
        writes = {name: _writes_to(body, name) for name in mut_params}
    else:
        sig = tr.imported_defs.functions.get(fn_name)
        recorded = getattr(sig, 'mut_writes', None) or {}
        if sig is None or any(name not in recorded for name in mut_params):
            return False
        writes = {name: recorded[name] for name in mut_params}

    def ok(node) -> bool:
        if isinstance(node, Symbol):
            root, field_name = _root_and_field(node)
            if root not in mut_params:
                return True
            if field_name is None:
                return writes[root] == set()
            return field_read_ok(root, field_name)
        if not isinstance(node, SList) or len(node) == 0:
            return True
        if is_form(node, '.') and len(node) >= 3:
            root, field_name = _root_and_field(node)
            if root in mut_params:
                return field_read_ok(root, field_name)
        return all(ok(item) for item in node.items)

    def field_read_ok(root: str, field_name: str) -> bool:
        changed = writes[root]
        if changed is None or field_name in changed:
            return False
        record = _resolve(tr, param_types.get(root))
        if not isinstance(record, RecordType) or field_name not in record.fields:
            return False
        # A field holding a handle can change through another name for it.
        return is_value_type(tr, record.fields[field_name], set())

    return ok(expr)


def _names_any(expr, names: Set[str]) -> bool:
    """True if `expr` names one of `names`, bare or as the root of `p.field`."""
    if isinstance(expr, Symbol):
        name = expr.name
        if '.' in name[1:] and not name.startswith("'"):
            name = name.split('.', 1)[0]
        return name in names
    if isinstance(expr, SList):
        return any(_names_any(item, names) for item in expr.items)
    return False


def callee_has_contract(tr, fn_name: str) -> bool:
    """True if `fn_name` is a user function with a @post or @property to assume."""
    contract = callee_contract(tr, fn_name)
    return contract is not None and bool(contract[2])


def callee_is_pure(tr, fn_name: str) -> bool:
    """True if the user function `fn_name` is declared @pure."""
    registry = tr.function_registry
    if registry is not None and fn_name in registry.functions:
        return registry.functions[fn_name].is_pure
    imported = tr.imported_defs.functions.get(fn_name)
    return imported is not None and getattr(imported, 'is_pure', False)


def params_are_values(tr, fn_name: str) -> bool:
    """True if no parameter of `fn_name` can carry state the caller reads afterwards.

    Every parameter must be a plain value - no list, set, map or pointer
    anywhere inside it - and none may be `out`. A callee this cannot see the
    signature of does not qualify.
    """
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
    # changing it never reaches the caller. `out` no longer compiles, but a
    # source written for an older slop may still say it.
    if any(mode == 'out' for mode in modes):
        return False
    return all(is_value_type(tr, t, set()) for t in types)


def is_value_type(tr, typ, seen) -> bool:
    """True if a value of `typ` reaches no mutable storage."""
    if isinstance(typ, PrimitiveType):
        if typ.name in ('Int', 'I8', 'I16', 'I32', 'I64', 'U8', 'U16', 'U32', 'U64',
                        'Float', 'F32', 'F64', 'Bool', 'String', 'Unit', 'Arena'):
            return True
        target = tr.type_env.type_registry.get(typ.name) or tr.imported_defs.types.get(typ.name)
        if target is None or target is typ:
            return False
        return is_value_type(tr, target, seen)
    if isinstance(typ, (RangeType, EnumType)):
        return True
    if id(typ) in seen:
        return True     # a recursive type is as mutable as its other parts
    seen = seen | {id(typ)}
    if isinstance(typ, RecordType):
        return all(is_value_type(tr, t, seen) for t in typ.fields.values())
    if isinstance(typ, UnionType):
        payloads = []
        for tag in typ.variants:
            recorded = typ.payload_types.get(tag)
            if recorded is None:
                first = typ.variants[tag]
                recorded = (first,) if first is not None else ()
            payloads.extend(recorded)
        return all(p is None or is_value_type(tr, p, seen) for p in payloads)
    if isinstance(typ, OptionType):
        return is_value_type(tr, typ.inner, seen)
    if isinstance(typ, ResultType):
        return all(is_value_type(tr, getattr(typ, f), seen)
                   for f in ('ok_type', 'err_type') if hasattr(typ, f))
    return False        # lists, maps, sets, pointers, channels, functions


def _callee_types(tr, fn_name: str):
    """({param: type}, return type) of a user function, or None if unknown."""
    registry = tr.function_registry
    if registry is not None and fn_name in registry.functions:
        from .type_builder import _parse_type_expr_simple
        fn_def = registry.functions[fn_name]
        if len(fn_def.param_type_exprs) != len(fn_def.params):
            return None
        types = {}
        for name, expr in zip(fn_def.params, fn_def.param_type_exprs):
            types[name] = (None if expr is None
                           else _parse_type_expr_simple(expr, tr.type_env.type_registry))
        ret = fn_def.return_type_expr
        return types, (None if ret is None
                       else _parse_type_expr_simple(ret, tr.type_env.type_registry))
    sig = tr.imported_defs.functions.get(fn_name)
    if sig is not None and len(sig.param_types) == len(sig.params):
        return dict(zip(sig.params, sig.param_types)), sig.return_type
    return None


# Operators whose value is a function of their operands' values alone. A
# String is a value - its bytes never change - so the string builtins are too.
_VALUE_OPERATORS = frozenset((
    '==', '!=', '<', '<=', '>', '>=', '+', '-', '*', '/', '%',
    'and', 'or', 'not', 'implies', 'if',
    'string-len', 'starts-with', 'ends-with', 'string-eq', 'string-contains',
))


def _resolve(tr, typ, depth: int = 0):
    """`typ` with named types looked up, to the declaration they name."""
    while isinstance(typ, PrimitiveType) and depth < 16:
        target = tr.type_env.type_registry.get(typ.name) or tr.imported_defs.types.get(typ.name)
        if target is None or target is typ:
            break
        typ, depth = target, depth + 1
    return typ


def _payload_types(tr, scrutinee_type, tag: str):
    """The payload types an arm's pattern `tag` binds, or None if unknown."""
    typ = _resolve(tr, scrutinee_type)
    if isinstance(typ, OptionType):
        return (typ.inner,) if tag == 'some' else () if tag == 'none' else None
    if isinstance(typ, ResultType):
        return (typ.ok_type,) if tag == 'ok' else (typ.err_type,) if tag == 'error' else None
    if isinstance(typ, UnionType) and tag in typ.variants:
        recorded = typ.payload_types.get(tag)
        if recorded is None:
            first = typ.variants[tag]
            recorded = (first,) if first is not None else ()
        return tuple(recorded)
    return None


def _caller_shares_its_storage(body) -> bool:
    """True if `body` takes an address or builds a closure.

    A local or parameter of the caller is a copy no one else holds, until the
    caller takes `(addr x)` of it or a closure captures it (a closure captures
    a `mut` local by reference). Then a callee may change it.
    """
    if not isinstance(body, SList) or len(body) == 0:
        return False
    head = body[0]
    if isinstance(head, Symbol):
        if head.name == 'quote':
            return False
        if head.name in ('addr', 'fn', 'lambda'):
            return True
    return any(_caller_shares_its_storage(item) for item in body.items)


def _caller_bindings(body) -> dict:
    """What each local of the caller is bound or assigned from, by name.

    A let or let* binding's initializer, a `set!` of the bare name, a
    for-each binder's collection and a match binder's scrutinee: whatever a
    local can hold comes from one of them. Over-approximate - all bindings of
    a name, wherever they are.
    """
    sources: dict = {}

    def add(name, expr):
        sources.setdefault(name, []).append(expr)

    def walk(node):
        if not isinstance(node, SList) or len(node) == 0:
            return
        head = node[0]
        if isinstance(head, Symbol):
            if head.name == 'quote':
                return
            if head.name in ('let', 'let*') and len(node) >= 2 and isinstance(node[1], SList):
                for binding in node[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        first = binding[0]
                        if isinstance(first, Symbol) and first.name == 'mut' and len(binding) >= 3:
                            name = binding[1]
                        elif isinstance(first, SList) and len(first) >= 2:
                            name = first[1]
                        else:
                            name = first
                        if isinstance(name, Symbol):
                            add(name.name, binding[-1])
            elif head.name == 'set!' and len(node) == 3 and isinstance(node[1], Symbol) \
                    and '.' not in node[1].name:
                add(node[1].name, node[2])
            elif head.name == 'for-each' and len(node) >= 2 and isinstance(node[1], SList) \
                    and len(node[1]) >= 2:
                binder, source = node[1][0], node[1][-1]
                for name in (binder.items if isinstance(binder, SList) else [binder]):
                    if isinstance(name, Symbol):
                        add(name.name, source)
            elif head.name == 'match' and len(node) >= 3:
                for clause in node.items[2:]:
                    if isinstance(clause, SList) and len(clause) >= 1 \
                            and isinstance(clause[0], SList):
                        for binder in clause[0].items[1:]:
                            if isinstance(binder, Symbol):
                                add(binder.name, node[1])
        for item in node.items:
            walk(item)

    walk(body)
    return sources


def _written_in_place(body) -> Set[str]:
    """The names `body` changes in place: a field of one set, a collection
    write through one or a field of one. Not a `set!` of the bare name, which
    the translator gives a new version."""
    names: Set[str] = set()

    def walk(node):
        if not isinstance(node, SList) or len(node) == 0:
            return
        head = node[0]
        if isinstance(head, Symbol):
            if head.name == 'quote':
                return
            if head.name == 'set!' and len(node) >= 3:
                target = node[1]
                if len(node) == 4 and isinstance(target, Symbol):
                    names.add(target.name.split('.', 1)[0])
                else:
                    root, field_name = _root_and_field(target)
                    if root is not None and field_name is not None:
                        names.add(root)
            elif head.name in _COLLECTION_WRITES and len(node) >= 2:
                root, _ = _root_and_field(node[1])
                if root is not None:
                    names.add(root)
        for item in node.items:
            walk(item)

    walk(body)
    return names


def unstable_arguments(tr, call_expr, params: Sequence[str], caller_body,
                       caller_param_types) -> Set[str]:
    """The parameters whose argument a stateful callee might change behind the call.

    A post naming a parameter describes the argument as the call passed it.
    The main model reads the caller's value after the call as the same term,
    even where the callee wrote it through a pointer (#242) - and reads
    `(deref p)` as `p` itself, so a local copied out of a pointer is the same
    term as what the pointer reaches. Such a post would then describe the
    changed value. An argument is stable when it and everything it was bound
    from avoid pointers: literals, names, operators and calls over stable
    operands, fields read only out of a parameter of the caller held by value -
    never `deref`, and never in a caller that takes an address or builds a
    closure.
    """
    if _caller_shares_its_storage(caller_body):
        return set(params)
    sources = _caller_bindings(caller_body)
    # Names the caller changes in place - a field set, a push - which the model
    # does not version (#242): a read after the call is the term before it. A
    # parameter declared as a pointer is not among them: a field set through
    # it changes what it points to, not the pointer passed, and a read through
    # it is a state read the contract filter already refuses.
    written_in_place = {
        name for name in _written_in_place(caller_body)
        if not isinstance(_resolve(tr, caller_param_types.get(name)), PtrType)
        or name in sources}

    def by_value_record(name: str) -> Optional[RecordType]:
        typ = _resolve(tr, caller_param_types.get(name))
        return typ if isinstance(typ, RecordType) else None

    def field_chain_ok(root: str, fields: Sequence[str]) -> bool:
        if root in sources or root in written_in_place:
            return False        # a local's type is not known here
        record = by_value_record(root)
        for index, field_name in enumerate(fields):
            if record is None or field_name not in record.fields:
                return False
            if index + 1 < len(fields):
                record = _resolve(tr, record.fields[field_name])
                if not isinstance(record, RecordType):
                    return False
        return True

    def chain(node):
        """(root, [fields]) for `p.a.b` or `(. (. p a) b)`, else None."""
        if isinstance(node, Symbol):
            parts = node.name.split('.')
            return parts[0], parts[1:]
        if is_form(node, '.') and len(node) == 3 and isinstance(node[2], Symbol):
            inner = chain(node[1])
            if inner is None:
                return None
            return inner[0], inner[1] + [node[2].name]
        return None

    visiting: Set[str] = set()

    def stable_name(name: str) -> bool:
        if name in written_in_place:
            return False
        if name not in sources:
            return True         # a parameter, a constant, an enum value
        if name in visiting:
            return True         # stable unless something else says otherwise
        visiting.add(name)
        try:
            return all(stable(expr) for expr in sources[name])
        finally:
            visiting.discard(name)

    def stable(node) -> bool:
        if isinstance(node, (Number, String)):
            return True
        if isinstance(node, Symbol):
            if node.name in ('true', 'false', 'nil') or node.name.startswith("'"):
                return True
            root, fields = chain(node)
            if fields:
                return field_chain_ok(root, fields)
            return stable_name(root)
        if not isinstance(node, SList) or len(node) == 0:
            return False
        head = node[0]
        if not isinstance(head, Symbol):
            return False
        if head.name == 'quote':
            return True
        if head.name in ('deref', 'addr', 'fn', 'lambda'):
            return False
        if head.name == '.':
            found = chain(node)
            return found is not None and field_chain_ok(*found)
        if head.name == 'cast' and len(node) == 3:
            return stable(node[2])
        # An operator, a constructor or a call: a value the caller holds,
        # computed from these operands.
        return all(stable(item) for item in node.items[1:])

    return {param for param, arg in zip(params, call_expr.items[1:]) if not stable(arg)}


def contract_is_state_free(tr, fn_name: str, expr) -> bool:
    """True if `expr`, part of `fn_name`'s contract, reads no mutable state.

    A callee that may change state - not @pure, and given a list, a map or a
    pointer - is one term for every call with the same arguments (#227), and
    the model reads state as if it never changed: `(. c n)` through a pointer
    is one value wherever it is read. A contract that reads the counter it
    bumps would then claim, for every call, what is true only of one.

    What is read out of a value is fixed once the call returns: a field of a
    record passed or returned by value - whatever else the record holds -
    and the payload of a Result, an Option or a union, through `match`. So
    is a String's length, and the length of a List - a header held by value,
    which a callee cannot push to unless `mut`, and `mut` on a List is an
    error (spec 3.4). Anything read through a pointer, out of a collection's
    contents, or by calling a function is not.
    """
    types = _callee_types(tr, fn_name)
    if types is None:
        return False
    param_types, return_type = types
    env = dict(param_types)
    env['$result'] = return_type

    def type_of(node, env):
        """The declared type of a name or a by-value field chain, or None."""
        if isinstance(node, Symbol):
            parts = node.name.split('.')
            typ = env.get(parts[0])
            for field_name in parts[1:]:
                typ = field_type(typ, field_name)
            return typ
        if is_form(node, '.') and len(node) == 3 and isinstance(node[2], Symbol):
            return field_type(type_of(node[1], env), node[2].name)
        return None

    def field_type(typ, field_name):
        record = _resolve(tr, typ)
        if isinstance(record, RecordType):
            return record.fields.get(field_name)
        return None

    def by_value_record(node, env) -> bool:
        return isinstance(_resolve(tr, type_of(node, env)), RecordType)

    def free(node, env) -> bool:
        if isinstance(node, Symbol):
            # `p.field` is a field read, as `(. p field)` is; a bare name is
            # the value the call was given.
            parts = node.name.split('.')
            if len(parts) > 1 and parts[0]:
                for end in range(1, len(parts)):
                    if not by_value_record(Symbol('.'.join(parts[:end])), env):
                        return False
            return True
        if isinstance(node, (Number, String)):
            return True
        if not isinstance(node, SList) or len(node) == 0:
            return True
        head = node[0]
        if not isinstance(head, Symbol):
            return False
        if head.name == 'quote':
            return True
        if head.name == '.':
            return len(node) == 3 and free(node[1], env) and by_value_record(node[1], env)
        if head.name == 'list-len':
            # The length in a List header the callee holds by value: its copy
            # of a parameter (or of a List field of one), or the List it
            # returns. Whether the caller's own header can change behind the
            # call is the caller's question (unstable_arguments).
            return (len(node) == 2 and free(node[1], env)
                    and isinstance(_resolve(tr, type_of(node[1], env)), ListType))
        if head.name == 'match' and len(node) >= 3:
            if not free(node[1], env):
                return False
            scrutinee_type = type_of(node[1], env)
            for clause in node.items[2:]:
                if not isinstance(clause, SList) or len(clause) < 2:
                    return False
                pattern = clause[0]
                arm_env = env
                if isinstance(pattern, SList) and len(pattern) >= 1 and isinstance(pattern[0], Symbol):
                    payloads = _payload_types(tr, scrutinee_type, pattern[0].name.lstrip("'"))
                    arm_env = dict(env)
                    for index, binder in enumerate(pattern.items[1:]):
                        if isinstance(binder, Symbol):
                            arm_env[binder.name] = (payloads[index] if payloads is not None
                                                    and index < len(payloads) else None)
                if not all(free(item, arm_env) for item in clause.items[1:]):
                    return False
            return True
        if head.name in _VALUE_OPERATORS:
            return all(free(item, env) for item in node.items[1:])
        return False

    return free(expr, env)


def contract_closed_over(tr, expr, allowed) -> bool:
    """True if every free name in `expr` is in `allowed`.

    Function heads and field names are not free names. Anything else a
    callee's contract mentions - a global, another parameter's alias - would be
    read in the caller's scope, where it means something else.
    """

    def free(node, bound, position_is_field=False) -> bool:
        if isinstance(node, Symbol):
            n = node.name
            # `p.field` names p; the rest is field names.
            if '.' in n[1:] and not n.startswith("'"):
                n = n.split('.', 1)[0]
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
            # Names a match arm or a quantifier binds are the contract's own,
            # not free names of the caller's.
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


def _mentions(expr, names: Set[str]) -> bool:
    if isinstance(expr, Symbol):
        return expr.name in names
    if isinstance(expr, SList):
        return any(_mentions(item, names) for item in expr.items)
    return False


def reads_collection_of(expr, names: Set[str]) -> bool:
    """True if `expr` quantifies over, or tests membership in, a collection
    built from one of `names`.

    Those reads go through the translator's name-keyed sequence registry, which
    holds the *caller's* lists: under a callee's contract, `(forall (t items)
    ...)` would range over whatever the caller calls `items`, and over a name
    the caller has no list for, it registers a fresh one that every later
    reader of that name shares. A length or element read falls back to an
    uninterpreted function of the argument's own term when the name is hidden,
    so only these are refused.
    """
    if not isinstance(expr, SList) or len(expr) == 0:
        return False
    head = expr[0]
    if isinstance(head, Symbol):
        if head.name == 'quote':
            return False
        if (head.name in ('forall', 'exists') and len(expr) >= 2
                and isinstance(expr[1], SList) and len(expr[1]) >= 2
                and _mentions(expr[1][1], names)):
            return True
        if (head.name in _NAME_KEYED_COLLECTION_READERS and len(expr) >= 2
                and _mentions(expr[1], names)):
            return True
    return any(reads_collection_of(item, names) for item in expr.items)


def _keyed_by(key: str, names: Iterable[str]) -> bool:
    """True if a collection registry key belongs to one of `names`.

    A name's own list is keyed by the name; a list held in one of its fields by
    `Z3Translator.field_collection_key`, "_field <name>.<field>".
    """
    for name in names:
        if key == name or key.startswith(f"_field {name}."):
            return True
    return False


@contextmanager
def contract_scope(tr, param_map, hidden_names: Iterable[str]):
    """Translate a callee's contract with its names meaning the call's terms.

    Each name in `param_map` is bound to its term. The version markers a
    caller's loop or assignment left on a name of the same spelling are lifted
    for the duration: the frozen-version check would refuse a perfectly
    ordinary reference to the callee's parameter, and the initial-version
    preference would answer it with the caller's value. The collections
    registered under `hidden_names` are hidden, so nothing reads the caller's
    list of that name; whatever this registers under them is dropped again.
    """
    hidden_names = tuple(hidden_names)
    saved_vars = {name: tr.variables.get(name, _MISSING) for name in param_map}
    saved_markers = {name: tr._pre_loop_variables.pop(name)
                     for name in param_map if name in tr._pre_loop_variables}
    hidden_seqs = {key: tr.list_seqs.pop(key)
                   for key in list(tr.list_seqs) if _keyed_by(key, hidden_names)}
    hidden_arrays = {key: tr.list_arrays.pop(key)
                     for key in list(tr.list_arrays) if _keyed_by(key, hidden_names)}
    for name, term in param_map.items():
        tr.variables[name] = term
    try:
        yield
    finally:
        for name, previous in saved_vars.items():
            if previous is _MISSING:
                tr.variables.pop(name, None)
            else:
                tr.variables[name] = previous
        for name in param_map:
            tr._pre_loop_variables.pop(name, None)
        tr._pre_loop_variables.update(saved_markers)
        for registry, hidden in ((tr.list_seqs, hidden_seqs), (tr.list_arrays, hidden_arrays)):
            for key in [k for k in registry if _keyed_by(k, hidden_names)]:
                del registry[key]
            registry.update(hidden)


def _translate_contract_term(tr, expr, patterns: bool):
    """A contract expression as a Bool term, with what translating it raised dropped.

    What translating a callee's contract appends to the translator's
    constraints - a definedness condition above all - is not the caller's to
    assume.
    """
    start = len(tr.constraints)
    try:
        if patterns:
            term = tr.translate_expr(expr)
        else:
            with tr.without_quantifier_patterns():
                term = tr.translate_expr(expr)
    except z3.Z3Exception:
        term = None
    finally:
        del tr.constraints[start:]
        tr.definedness_constraints.difference_update(
            {i for i in tr.definedness_constraints if i >= start})
    if term is None or not z3.is_expr(term) or term.sort() != z3.BoolSort():
        return None
    return term


def instantiate_callee_contract(tr, fn_name: str, call_term, arg_terms: Sequence[Any],
                                guard, *, result_term=None,
                                keep_post: Optional[Callable[[Any], bool]] = None,
                                keep_pre: Optional[Callable[[Any], bool]] = None,
                                patterns: bool = True) -> List[Any]:
    """`Implies(And(guard, *pre), post)` for each @post and @property of the call.

    `$result` is `call_term` and each parameter the matching term of
    `arg_terms`. `result_term`, when given, stands for `$result` instead: the
    caller's own `$result`, for a call that is the value the caller returns -
    then `$result`'s collections are the caller's too, and are left visible.

    If any @pre cannot be stated - it names something other than the
    parameters, reads one of their collections by name, or does not translate -
    nothing is assumed: a post without its precondition is a promise the call
    did not earn. A post that cannot be stated is skipped on its own.
    `keep_post(post)` may refuse a post this caller cannot read soundly, and
    `keep_pre(pre)` a precondition - which, like one that cannot be stated,
    leaves nothing assumed.
    """
    contract = callee_contract(tr, fn_name)
    if contract is None:
        return []
    params, pres, posts = contract
    if not posts or len(params) != len(arg_terms):
        return []
    if any(term is None for term in arg_terms) or call_term is None:
        return []
    result = call_term if result_term is None else result_term
    param_map = {'$result': result}
    param_map.update(zip(params, arg_terms))
    allowed = set(param_map)
    # `$result`'s collections belong to the caller only when it is the
    # caller's `$result`.
    hidden = set(params) if result_term is not None else set(params) | {'$result'}

    axioms: List[Any] = []
    with contract_scope(tr, param_map, hidden):
        pre_terms = []
        for pre in pres:
            if not contract_closed_over(tr, pre, allowed) or reads_collection_of(pre, hidden):
                return []
            if keep_pre is not None and not keep_pre(pre):
                return []
            term = _translate_contract_term(tr, pre, patterns)
            if term is None:
                return []
            pre_terms.append(term)
        assumption = z3.And(guard, *pre_terms) if pre_terms else guard
        # A post about a `mut` parameter is about the callee's own copy as it
        # left it, which is the argument only where the callee changed nothing
        # the post reads; a @pre reads the value passed in.
        mut_params = callee_mut_params(tr, fn_name)
        for post in posts:
            if not contract_closed_over(tr, post, allowed) or reads_collection_of(post, hidden):
                continue
            if (mut_params and _names_any(post, mut_params)
                    and not _mut_reads_unchanged(tr, fn_name, post, mut_params)):
                continue
            if keep_post is not None and not keep_post(post):
                continue
            term = _translate_contract_term(tr, post, patterns)
            if term is None:
                continue
            axioms.append(z3.Implies(assumption, term))
    return axioms
