# {{name}}

This project is written in SLOP. SLOP is a contract-first language with
S-expression syntax that transpiles to C. A human states the intent of the
code through types, `@intent`, `@spec`, `@pre`, `@post` and `@example`, and
an agent writes the implementation.

SLOP is new, and your training data has very little of it. Do not write SLOP
from memory of Lisp, Clojure or Scheme. Many forms that look right in those
languages do not exist in SLOP. Look forms up instead of guessing.

## Layout

| Path | What |
|------|------|
| `slop.toml` | Project config: name, entry, build, test |
| `{{source}}` | {{source_desc}} |
| `build/` | Build output (ignored by git) |

Every `.slop` file is a single `(module ...)` form. All types, functions and
constants go inside it.

## Commands

Run these from the project root, because `slop.toml` is read from the
current directory.

| Command | What it does |
|---------|--------------|
| `slop build` | Parse, type check, transpile to C, and compile |
| `slop test` | Run every `@example` under `src/` |
| `slop check FILE` | Type check one file |
| `slop format FILE` | Rewrite a file in the canonical layout (`--check` only reports) |
| `slop verify` | Prove contracts with Z3 (needs Z3 installed) |
| `slop ref [TOPIC]` | Language reference; `slop ref mistakes` lists forms that do not exist |
| `slop doc MODULE` | A stdlib module's API with contracts, for example `slop doc strlib` |

## SLOP tools (MCP)

{{mcp_registered}} If your tool list has `ref`, `doc`, `check` and `format` from
the `slop` server, use those tools. Otherwise, run the CLI commands above.

- **`ref`**: call it before writing any form you are unsure of. Call it with
  no topic to list the topics. Read `ref mistakes` once per session before
  your first edit.
- **`doc`**: call it with the module name before calling a standard-library
  function, for example `doc strlib`. Do not guess names or argument orders.
- **`check`**: call it on a `.slop` file after every edit. Fix every error
  before moving on.
- **`format`**: call it on a file you changed when you finish with it.

## Workflow

1. Define types first. Use range types such as `(Int 0 .. 100)` for bounded
   values.
2. Write each function's signature and contracts before its body:
   `@intent`, `@spec`, `@pre`, `@post`, and `@example` cases. Every function
   needs `@intent` and `@spec`.
3. Implement the body. You can also leave a `(hole Type "prompt" :complexity tier-N)`
   for later.
4. Run `check`, then `slop test`, then `slop build`.

Parentheses must balance. A single misplaced `)` can move a form into the
wrong parent and still parse. Edit whole forms rather than individual
characters, and run `check` after each change.

## Contracts

`@pre`, `@post` and `@assume` are compiled out of normal builds.
`slop build --debug` checks them at run time, and `slop verify` proves them.
`@example` cases always run under `slop test`. Range types are checked at run
time unless the build uses `--no-range-checks`.
