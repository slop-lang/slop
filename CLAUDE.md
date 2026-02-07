# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is SLOP?

SLOP (Symbolic LLM-Optimized Programming) is a language designed for hybrid human-machine code generation. Humans specify intent via contracts and types; machines generate implementation and transpile to C.

Key features:
- S-expression syntax (Lisp-like)
- Mandatory contracts (`@intent`, `@spec`, `@pre`, `@post`)
- Range types: `(Int 0 .. 100)` catches bounds errors at compile time
- Typed holes for LLM generation with complexity tiers
- Transpiles to C for performance

## Commands

```bash
# Run all tests
uv run pytest

# Run a single test file
uv run pytest tests/test_parser.py

# Run a single test
uv run pytest tests/test_parser.py::TestBasicParsing::test_symbol -v

# Parse a SLOP file
uv run slop parse examples/rate-limiter.slop

# Type check
uv run slop check examples/rate-limiter.slop

# Transpile to C
uv run slop transpile examples/rate-limiter.slop -o output.c

# Build to native binary (requires cc)
uv run slop build examples/rate-limiter.slop -o binary

# Build the native toolchain
make build-native
```

## Architecture

### Pipeline Flow
```
SLOP source → native parser → AST → native checker → native compiler → C code
                                           ↓
                                   hole_filler.py (LLM fills holes)
```

Type checking and transpilation are handled by the native toolchain (`slop-compiler`). The Python CLI orchestrates the pipeline but delegates compilation to native binaries.

### Core Modules (src/slop/)

- **parser.py**: S-expression parser producing AST (`SList`, `Symbol`, `String`, `Number`). Key functions: `parse()`, `is_form()`, `find_holes()`, `pretty_print()`. Used as fallback when native parser unavailable.

- **hole_filler.py**: Routes holes to LLM providers based on complexity tiers (tier-1 through tier-4). Validates generated code against type constraints.

- **providers.py**: LLM provider implementations (Ollama, OpenAI-compatible, Interactive, Multi-provider routing)

- **cli.py**: Command-line interface (`slop` command). Orchestrates the native toolchain.

- **resolver.py**: Module import/export resolution

- **paths.py**: Centralized path resolution with SLOP_HOME support

### Language Spec

The authoritative language specification is in `spec/LANGUAGE.md`. When modifying the language:
1. Update `spec/LANGUAGE.md`
2. Update `.claude/skills/slop/SKILL.md` (Claude's quick reference)
3. Update `src/slop/reference.py` (CLI reference for `slop ref` command)
4. Update native parser/checker/compiler as needed
5. Update `tree-sitter-slop/` grammar and highlights if syntax changes

### Tree-sitter Grammar

Located in `tree-sitter-slop/`:
- `grammar.js`: Grammar definition
- `queries/highlights.scm`: Syntax highlighting
- `slop-ts-mode.el`: Emacs major mode

## SLOP Syntax Quick Reference

```lisp
;; Module with exports
(module name (export fn-name) forms...)

;; Types
(type Name (record (field Type)...))
(type Name (enum val1 val2))
(type Name (Int min .. max))

;; Constants (integers → #define, others → static const)
(const NAME Type value)

;; Functions with contracts
(fn name ((param Type)...)
  (@intent "description")
  (@spec ((ParamTypes) -> ReturnType))
  (@pre condition)
  (@post condition)
  body)

;; Holes for LLM generation
(hole Type "prompt" :complexity tier-2 :required (var1 var2))

;; FFI
(ffi "header.h" (func-name ((param Type)) ReturnType))
(ffi-struct "header.h" name (field Type)...)
```

## Key Patterns

**Pointer tracking**: The compiler auto-detects pointers from `(Ptr T)` params and `arena-alloc` results. Uses `->` for pointer field access, `.` for values.

**Range types**: `(Int 0 .. 255)` maps to smallest C type (uint8_t) with runtime bounds checks via `SLOP_PRE`.

**Arena allocation**: Primary memory model. `(with-arena size body)` creates scoped arena, freed automatically.

**Result types**: `(Result T E)` is a tagged union. Use `(ok val)` / `(error e)` constructors, `match` to destructure.

## Self Hosting
The goal is a self-hosting slop parser, type checker, and transpiler.  When working on the slop native tooling
- It is always better to generate a transpiler error than to emit ambiguous C code and / or some hard-coded default when running into some unimplemented SLOP feature.
- Errors should be caught as early as possible.  First by the parser, then the type checker, then the transpiler.  It is a FAILURE if an error is caught by the C compiler.
- The goal is not simply to get something that builds.  We do not workaround code generation issues with hardcoding, default types, rewriting using a different SLOP construct, etc.  
- The SLOP native tools are the priority for new features.


## General guidance
- Paren balance is critical for a language based on S-expressions.  Verify balance BEFORE making multiple writes to a file to avoid large compounding imbalances that require extensive troubleshooting.  Use `python scripts/paren-balance.py <file>` to check paren balance of a `.slop` file.
- The native toolchain (slop-parser, slop-checker, slop-compiler) is required. The Python type checker and transpiler have been removed. Run `make build-native` to build the native tools.

Whenenver you are working with SLOP code, you are permanently in SLOP PAREDIT MODE — structural editing only for the Slop language (https://github.com/slop-lang/slop).

Core rules — break any and the edit is invalid:
1. ALL code output MUST have PERFECTLY balanced parentheses ( and ). Count obsessively.
2. Edit structurally ONLY: describe changes as slurp/barf/splice/raise/wrap/unwrap/kill-sexp/etc BEFORE showing code.
   - Treat @-forms (@intent, @spec, @pre, @post), (hole ...), (fn ...), (type ...), (module ...), (ffi ...), etc. as atomic units when possible.
   - For {infix conditions}, treat the entire {} as one balanced sexp unit — never insert parens inside {} unless explicitly structural.
3. Before ANY code block, insert <slop-paren-audit>:
   - Count every ( and ) across the entire proposed code.
   - Report: "Open parens: X    Close parens: X    Balanced: YES/NO"
   - If NO → do NOT output code; instead say "Unbalanced — retrying structurally" and fix in thinking.
4. When editing:
   - Show → BEFORE: the targeted form(s), marked →( like this )←
   - Describe: exact structural ops (e.g. "wrapping the body in (if ...)", "slurping next arg into fn params", "raising @pre one level", "inserting typed hole at end of body")
   - Then → AFTER: full balanced form/module snippet
5. If user request risks breaking Slop structure (e.g. raw text edits to infix {}, unbalanced ranges, missing @spec), refuse and suggest structural equivalent.
6. Favor Slop idioms: keep @-contracts together at top of fn, use range types, prefer holes for implementation, indent generously, align bindings/conditions.
7. This is Slop — symbolic, contract-first, LLM-optimized. No textual slop. Output clean, balanced s-expressions only.

Acknowledge: entering SLOP PAREDIT MODE now.
