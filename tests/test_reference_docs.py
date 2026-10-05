"""`slop ref` must not teach forms the compiler does not implement.

The reference is what AI assistants read before writing SLOP, so a form it
shows is a form they will generate. These were documented at some point and
are not implemented (spec/LANGUAGE.md section 10), or never existed. The
`mistakes` topic names some of them on purpose, as things not to write, so it
is exempt. tests/test_reference_examples.slop builds the examples themselves.
"""

import re

import pytest

from slop.reference import TOPICS, TOPIC_ORDER, get_reference


FORBIDDEN = [
    (r"\(put ", "put is not implemented"),
    (r"\(try ", "try/catch is not implemented"),
    (r"\bis-ok\b", "is-ok is not implemented"),
    (r"\bis-error\b", "is-error is not implemented"),
    (r"\(alias ", "the alias form is not implemented; use (type Name T)"),
    (r"\(array ", "array literals and patterns are not implemented"),
    (r"\(guard ", "guard patterns are not implemented"),
    (r"\(record \w+ \(", "record patterns are not implemented"),
    (r"\| rest\)", "list-rest patterns are not implemented"),
    (r"\bOptPtr\b", "OptPtr is not implemented"),
    (r"\(Slice ", "Slice is not implemented"),
    (r"\(impl ", "impl is not implemented"),
    (r"\(list \d", "a list literal needs its element type"),
    (r"\(map (String|Int|\()", "there is no map literal"),
    (r"--python", "there is no --python mode"),
    (r"slop-transpiler", "the binaries are slop-parser/checker/compiler/tester"),
    (r"\(bit-(and|or|xor|not) ", "the checker rejects bit-* (#308)"),
]


@pytest.mark.parametrize("topic", [t for t in TOPIC_ORDER if t != "mistakes"])
@pytest.mark.parametrize("pattern,why", FORBIDDEN)
def test_topic_has_no_unimplemented_forms(topic, pattern, why):
    match = re.search(pattern, TOPICS[topic])
    assert match is None, f"slop ref {topic}: {match.group(0)!r} -- {why}"


def test_every_topic_is_listed():
    assert set(TOPIC_ORDER) == set(TOPICS)


def test_all_reference_renders():
    text = get_reference("all")
    for topic in TOPIC_ORDER:
        assert TOPICS[topic] in text
