"""Translator side facts and obligations, with their emission context."""

from dataclasses import dataclass
from typing import Any

from .z3_setup import z3


@dataclass(frozen=True)
class TranslationConstraint:
    term: Any
    guard: Any
    scope: str
    past_exit: bool = False
    obligation: bool = False
    source: Any = None

    def guarded(self):
        """None when the translation could not place this fact on a path."""
        if self.guard is None:
            return None
        return self.term if z3.is_true(self.guard) else z3.Implies(self.guard, self.term)


class TranslationConstraints(list):
    """The existing formula list, retaining metadata through append and rollback.

    Walkers consume formula slices and discard speculative suffixes. Keeping the
    records and obligation indices here makes that rollback atomic.
    """

    def __init__(self, context):
        super().__init__()
        self._context = context
        self.records = []
        self.obligations = set()

    def append(self, term):
        self.add(term)

    def extend(self, terms):
        for term in terms:
            self.append(term)

    def add(self, term, *, obligation=False, source=None):
        guard, scope, past_exit = self._context()
        if obligation:
            self.obligations.add(len(self))
        self.records.append(TranslationConstraint(
            term, guard, scope, past_exit, obligation, source))
        super().append(term)

    def __delitem__(self, key):
        del self.records[key]
        super().__delitem__(key)
        self.obligations.clear()
        self.obligations.update(i for i, record in enumerate(self.records) if record.obligation)
