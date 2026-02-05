#!/usr/bin/env python3
"""SLOP parenthesis balance checker.

Counts ( and ) while skipping string literals and ;-comments.
Reports per-file balance and pinpoints the line/col of imbalances.
"""

import sys
import os


def check_balance(filepath):
    with open(filepath) as f:
        content = f.read()

    opens = 0
    closes = 0
    depth = 0
    in_string = False
    in_comment = False
    escape = False

    line = 1
    col = 1

    # Track where each unmatched open paren is
    open_stack = []  # (line, col)
    errors = []      # (line, col, message)

    for ch in content:
        if in_comment:
            if ch == '\n':
                in_comment = False
                line += 1
                col = 1
            else:
                col += 1
            continue

        if escape:
            escape = False
            if ch == '\n':
                line += 1
                col = 1
            else:
                col += 1
            continue

        if in_string:
            if ch == '\\':
                escape = True
                col += 1
            elif ch == '"':
                in_string = False
                col += 1
            elif ch == '\n':
                line += 1
                col = 1
            else:
                col += 1
            continue

        # Not in string or comment
        if ch == ';':
            in_comment = True
            col += 1
            continue

        if ch == '"':
            in_string = True
            col += 1
            continue

        if ch == '(':
            opens += 1
            depth += 1
            open_stack.append((line, col))
            col += 1
            continue

        if ch == ')':
            closes += 1
            depth -= 1
            if depth < 0:
                errors.append((line, col, "Unexpected closing paren — no matching open"))
                depth = 0  # reset to keep scanning
            else:
                open_stack.pop()
            col += 1
            continue

        if ch == '\n':
            line += 1
            col = 1
        else:
            col += 1

    # Any remaining unclosed parens
    for (ol, oc) in open_stack:
        errors.append((ol, oc, "Unclosed open paren"))

    balanced = opens == closes and len(errors) == 0
    return opens, closes, balanced, errors


def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <file.slop> [file2.slop ...]", file=sys.stderr)
        sys.exit(1)

    any_fail = False

    for filepath in sys.argv[1:]:
        if not os.path.isfile(filepath):
            print(f"{filepath} — NOT FOUND", file=sys.stderr)
            any_fail = True
            continue

        opens, closes, balanced, errors = check_balance(filepath)
        name = os.path.relpath(filepath)
        status = "YES" if balanced else "NO"
        print(f"{name} — Open: {opens}  Close: {closes}  Balanced: {status}")

        if not balanced:
            any_fail = True
            for (el, ec, msg) in errors:
                print(f"  {name}:{el}:{ec}: {msg}")

    sys.exit(1 if any_fail else 0)


if __name__ == "__main__":
    main()
