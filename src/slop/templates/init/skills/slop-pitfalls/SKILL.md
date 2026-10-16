---
name: slop-pitfalls
description: Mistakes agents often make writing SLOP, and what to do instead. Use before writing or fixing .slop code, and when a slop check, slop build or slop test error is confusing.
---

# SLOP pitfalls

## First: the forms that don't exist

Call `ref mistakes` (or run `slop ref mistakes`) before your first edit in a
session. It lists the Lisp, Scheme and C habits that have no SLOP form, with
what to use instead: `begin`, `unwrap`, `try`, `strlen`, untyped
`(list ...)`, and so on. That table comes from your installed slop, so it is
current. Do not rely on memory of it.

Before calling any standard-library function, call `doc MODULE`. Some common
string and list functions are builtins and others need an `(import strlib ...)`.
`ref mistakes` says which.

## Memory

- **Returning arena data out of `with-arena`.** The arena is freed when the
  block exits, including when the block's value is the function's result.
  The compiler does not reject this yet. Build anything that must outlive
  the block in the caller's `Arena` parameter.
- **Collections grow in their own arena.** A List, Map or Set grows in the
  arena it was created in, wherever the push happens. To grow it in a
  different arena for one call, pass `:arena a`.
- **More than one Arena in scope and none named `arena`.** Literals and
  lambda environments then can't pick one. Pass `:arena a`, or bind
  `(let ((arena a)) ...)`.

## Mutation and parameters

- Parameters are read-only. `mut` gives the function a local copy, so the
  caller never sees the change. To change the caller's value, take a
  `(Ptr T)` and have the caller pass `(addr v)`. There is no `out` mode.
- A `for-each` or `match` binding is a copy. Pushing onto it, or onto a
  List field of it, is an error. Take a `(let ((mut c x)) ...)` copy, change
  it, and write it back, or hold elements as `(Ptr T)`.
- Only `let ((mut x ...))` bindings can be `set!`.
- A lambda passed to `spawn` must not capture a `mut` variable. Bind an
  immutable copy and capture that.

## Types

- Error variants are quoted: `(error 'not-found)`, not `(error not-found)`.
  Enum values in `match` patterns are quoted too. `ref patterns` has the
  rules.
- A list literal needs its element type: `(list Int 1 2 3)`.
- A value stored into a range type is checked at run time, at full width,
  in every build unless the build uses `--no-range-checks`. A value outside
  the range aborts the program. Clamp it or check it before storing.
- Integer division truncates.
- `true`, `false`, `nil`, `none` and `unit` are literals. Do not name
  anything after them.

## Contracts

- `@pre`, `@post` and `@assume` are compiled out of normal builds. They run
  only under `slop build --debug`, and `slop verify` proves them. A passing
  normal build tells you nothing about them.
- `@example` cases run under `slop test` and are the cheapest live check you
  have. A function without examples is untested.
- `$result` names the return value in `@post` only.

## Structure

- Every definition goes inside `(module ...)`. A form after the module's
  closing paren is an error. The usual cause is one `)` too many above it.
- Each `.slop` file holds one module. Name the module after the file:
  `(import foo ...)` looks for `foo.slop` on the include paths.
- A C compiler error from `slop build` is a toolchain bug, not something to
  work around. Report it with the smallest `.slop` file that reproduces it.
