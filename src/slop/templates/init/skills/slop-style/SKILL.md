---
name: slop-style
description: How to write idiomatic SLOP (.slop files) contract first. Use when writing new SLOP code, adding functions or types to a .slop file, or designing a SLOP module's API.
---

# Writing SLOP

SLOP code is contract first. The types and contracts state what the code
does, and the body is the least important part. Write SLOP in that order.

This skill covers judgment, not syntax. Get syntax and APIs from the `slop`
tools rather than from memory:
- `ref TOPIC` for language forms (no topic lists them)
- `doc MODULE` for the stdlib
- `check FILE` after every edit

Without the MCP tools, run `slop ref`, `slop doc` and `slop check` instead.

## Order of work

1. **Types.** Model the domain with `type`, `record`, `enum` and `union`
   before writing any function. A bounded value gets a range type, for
   example `(type Port (Int 1 .. 65535))`, not a bare `Int` plus a check.
2. **Signatures and contracts.** For each function write the parameters,
   then `@intent`, `@spec`, `@pre`, `@post` and `@example`. You can leave
   the body as a `(hole ...)`.
3. **Review point.** When the design is not obvious, show the user the types
   and signatures before you implement them. Reworking contracts is cheap;
   reworking implementations is not.
4. **Bodies.** Implement, run `check`, then run `slop test`.

## Contracts

- Every `fn` has `@intent` and `@spec`. Write `@intent` as one plain
  sentence about what the function does, not how it does it.
- Annotations go in this order: `@intent`, `@spec`, `@alloc`,
  `@pure`/`@trusted`, `@pre`, `@post`, `@assume`, `@example`, `@deprecated`.
  `ref contracts` has the details.
- Each `@pre` should rule out an input the body cannot handle. If a range
  type already says it, put it in the type rather than in a `@pre`.
- Each `@post` should say something a caller can rely on and a wrong
  implementation would break. `(@post (>= $result 0))` on a function whose
  return type is already `(Int 0 ..)` adds nothing.
- Give every pure function a few `@example` cases. Cover a typical case,
  each boundary, and each branch. `slop test` runs them, and they are the
  only contracts checked in a normal build.
- Mark side-effect-free functions with `@pure`.

## Types and values

- Use range types for every number with a known domain. They document the
  domain, and the compiler picks the smallest C type and checks the bounds
  at run time.
- Use `(Result T E)` for anything that can fail, with an `enum` of error
  cases. Handle a Result with `match` or `(? e)`. There is no unwrap.
- Use `(Option T)` for something that may be absent. Test it with
  `is-some`/`is-none` or `match`, never with `==`.
- A function that allocates takes `(arena Arena)` as its first parameter and
  declares `(@alloc arena)`. Use `with-arena` to scope short-lived
  allocations.

## Shape and naming

- Names of functions, variables and modules are kebab-case. Types are
  CapitalCase and constants are UPPER_SNAKE.
- Keep functions small enough that their contracts can say what they do. If
  you cannot write `@post` for a function, split it.
- Prefer `cond` to nested `if`, and `match` to chains of tag comparisons.
- Export only what other modules need.
- Run `format` on files you change. The canonical layout is 80 columns with
  2-space indent and contracts before the body. Write code close to it so
  your diffs stay small.

## Holes

`(hole Type "prompt" :complexity tier-N ...)` marks code for `slop fill`
or for a later pass. Always give `:complexity`. Use `:required` and
`:context` to name the variables the code must use. `ref holes` has the
tiers.

## Editing safely

S-expressions fail silently. A `)` in the wrong place can move a form into a
different parent and still parse. Edit whole forms: replace a whole `fn`, a
whole `let`, or a whole contract, rather than inserting single parentheses.
Run `check` after every edit. If a file stops parsing, go back to your last
good edit; do not hunt for a stray paren.
