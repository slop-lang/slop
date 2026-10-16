---
name: slop-review
description: Review SLOP (.slop) code for contract quality, correctness and idiom. Use when asked to review SLOP code, a diff that touches .slop files, or a pull request in a SLOP project.
---

# Reviewing SLOP

In a SLOP review, check the contracts first: wrong contracts make the code
that satisfies them wrong too. Then look at the body.

## 1. Run the tools

Run these first, and include any failure as a finding:

- `check` on each changed `.slop` file. Any error is a blocking finding.
- `format` with `--check` (`slop format --check FILE`). Report a file that
  isn't formatted, as a minor finding.
- `slop test` from the project root. Report each failing `@example` with the
  function's name.
- `slop verify`, if Z3 is installed and the project uses it.

## 2. Contracts

For each new or changed `fn`:

- [ ] It has `@intent` and `@spec`. The `@intent` describes what the function
      does, matches what the body does, and doesn't describe the
      implementation.
- [ ] The `@spec` types are as narrow as the domain allows: a range type
      instead of `Int`, `(Result T E)` when the function can fail,
      `(Option T)` when a value may be missing.
- [ ] Each `@pre` rules out an input the body really can't handle, and none
      is missing. Look for divisions, indexes and dereferences that a `@pre`
      or range type doesn't protect.
- [ ] Each `@post` can fail: a wrong body would break it. Flag a tautology
      such as `(>= $result 0)` on an `(Int 0 ..)` result, or `true`.
- [ ] The `@example` cases cover each boundary and each branch, not just
      one typical input. Work out at least one expected value by hand.
- [ ] `@pure` is on the functions that have no side effects, and on no
      others.
- [ ] Annotations are in the canonical order (see `ref contracts`).

## 3. Body

- [ ] Nothing returns data allocated in a `with-arena` arena from that
      block. The compiler does not catch this.
- [ ] Each allocating function takes its `Arena` as a parameter and declares
      `@alloc`.
- [ ] No caller relies on a change made to a `mut` parameter. A change meant
      for the caller goes through `(Ptr T)`.
- [ ] Each Result is handled: `match` on it or pass it on with `?`, never
      ignore it.
- [ ] Error variants and enum patterns are quoted.
- [ ] No value stored into a range type can fall outside the range. If one
      can, the program aborts at run time.
- [ ] Every `match` handles every case, and the `else` branches are real
      rather than placeholders.
- [ ] Stdlib calls match `doc MODULE`. Flag any function you can't find
      there or in `ref builtins`.

## 4. Idiom

- `cond` instead of deep `if` nesting, and `match` instead of tag tests.
- Kebab-case names, CapitalCase types, UPPER_SNAKE constants.
- Exports limited to what other modules use.
- Any `hole` left in has `:complexity` and is deliberate.

## Reporting

Order the findings by severity: blocking (fails a tool, or wrong behaviour),
then contract weakness, then idiom. Give `file:line` and the form's name for
each. For a contract finding, include the input that shows the problem.
