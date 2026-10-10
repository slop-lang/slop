```
 ███████╗██╗      ██████╗ ██████╗
 ██╔════╝██║     ██╔═══██╗██╔══██╗
 ███████╗██║     ██║   ██║██████╔╝
 ╚════██║██║     ██║   ██║██╔═══╝
 ███████║███████╗╚██████╔╝██║
 ╚══════╝╚══════╝ ╚═════╝ ╚═╝
```

# Symbolic LLM-Optimized Programming

A programming language designed for minimal human involvement in coding.

```
Humans specify WHAT and WHY → Machines handle HOW
```

## Why SLOP?

This started as a thought experiment.  It's still very much an experiment :)

LLMs generate code fast—but without constraints they hallucinate APIs, ignore edge cases, and produce code that "looks right" but fails in production.

SLOP makes the spec the source of truth:

```lisp
(fn transfer ((from Account) (to Account) (amount (Int 1 ..)))
  (@intent "Transfer funds between accounts")
  (@spec ((Account Account (Int 1 ..)) -> (Result Receipt Error)))
  (@pre {from != to})
  (@pre {(. from balance) >= amount})
  (@post {(. from balance) + (. to balance) == (old (. from balance)) + (old (. to balance))})
  ...)
```

- **Contracts are mandatory.** No `@intent` or `@spec`, no compilation.
- **Range types catch bugs.** `(Int 1 .. 100)` — at compile time when the value is known, at run time otherwise.
- **Typed holes constrain generation.** LLMs fill gaps bounded by types, examples, and required variables.

## Status

The SLOP toolchain is **self-hosting**: the parser, type checker, and transpiler are all written in SLOP and compile themselves. The merged `slop-compiler` binary runs type checking and transpilation in a single pass and is the primary build tool.

## Philosophy

SLOP inverts the traditional programming model:

| Traditional | SLOP |
|-------------|------|
| Human writes code | Human writes specification |
| Compiler checks syntax | Machine generates implementation |
| Tests verify behavior | Contracts define correctness |
| Libraries provide code | Schemas generate types |

## Design Choices

- **S-expression syntax**: Zero parsing ambiguity, trivial for LLMs (I like Lisp)
- **Minimal spec**: ~50 built-ins, entire language fits in a prompt (~4K tokens)
- **Range types**: `(Int 0 .. 100)` catches bounds errors at compile time where it can and at run time otherwise, as Ada does (I also like Ada)
- **Mandatory contracts**: `@intent`, `@spec`, `@pre`, `@post` define correctness
- **Infix in contracts**: `{x > 0 and x < 100}` — readable math notation in `@pre`/`@post`
- **Generics**: `(@generic (T))` enables polymorphic functions with type-safe unification
- **Typed holes**: Explicit markers for LLM generation with complexity tiers
- **Transpiles to C**: Maximum performance, universal FFI, minimal runtime

## Quick Example

```lisp
(module rate-limiter
  (export acquire)

  (type Tokens (Int 0 .. 10000))
  (type Limiter (record (tokens Tokens)))
  (type AcquireResult (enum acquired rate-limited))

  (fn acquire ((limiter (Ptr Limiter)))
    (@intent "Try to acquire one token")
    (@spec (((Ptr Limiter)) -> AcquireResult))
    (@pre {limiter != nil})

    (if (> (. limiter tokens) 0)
      (do
        (set! limiter tokens (- (. limiter tokens) 1))
        'acquired)
      'rate-limited)))
```

Transpiles to:

```c
rate_limiter_AcquireResult rate_limiter_acquire(rate_limiter_Limiter* limiter) {
    SLOP_PRE(((limiter != NULL)), "(!= limiter nil)");
    if (limiter->tokens > 0) {
        limiter->tokens = SLOP_RANGE(int64_t, (limiter->tokens - 1), 1, 1, 0, 10000, "Tokens (Int 0 .. 10000) at rl.slop:15:30");
        return rate_limiter_AcquireResult_acquired;
    } else {
        return rate_limiter_AcquireResult_rate_limited;
    }
}
```

`Tokens` is stored in a `uint16_t`. Storing into it is a narrowing, so the new
value is range-checked first, at full width; a value out of range aborts with
its type and source position instead of wrapping.

## Project Structure

```
slop/
├── bin/                     Native compiler binaries (build artifacts)
│   ├── slop-parser          Native S-expression parser
│   ├── slop-checker         Native type checker
│   ├── slop-compiler        Native compiler (type check + transpile)
│   └── slop-tester          Native test runner
├── lib/
│   ├── compiler/            Self-hosted compiler (written in SLOP)
│   │   ├── compiler/        Merged compiler (checker + transpiler)
│   │   ├── parser/          Native parser source
│   │   ├── checker/         Native type checker source
│   │   ├── transpiler/      Native transpiler modules
│   │   ├── tester/          Native test runner source
│   │   └── common/          Shared compiler utilities
│   └── std/                 Standard library modules
│       ├── io/              File I/O
│       ├── strlib/          String manipulation
│       ├── math/            Math utilities
│       ├── os/              OS interface (env vars, etc.)
│       ├── path/            Path manipulation
│       ├── json/            JSON parse and emit
│       ├── xml/             XML parse and emit
│       └── thread/          Concurrency (channels, spawn/join)
├── spec/                    Language specifications
│   ├── LANGUAGE.md          Grammar, types, semantics
│   ├── REFERENCE.md         Quick reference (fed to the hole filler)
│   ├── VERIFICATION.md      What slop verify proves, and how
│   └── HYBRID_PIPELINE.md   Generation architecture
├── src/slop/                Python CLI and support toolchain
│   ├── runtime/
│   │   └── slop_runtime.h   C runtime: arenas, strings, collections, threads
│   ├── cli.py               Command-line interface
│   ├── parser.py            S-expression parser (format, doc, fill, verify)
│   ├── formatter.py         slop format
│   ├── reference.py         slop ref
│   ├── resolver.py          Module resolution for multi-module builds
│   ├── paths.py             SLOP_HOME and path resolution
│   ├── verifier/            Contract verification via Z3
│   ├── hole_filler.py       LLM integration with tiered routing
│   ├── providers.py         LLM providers (Ollama, OpenAI, etc.)
│   └── schema_converter.py  slop derive: JSON Schema, SQL, OpenAPI → SLOP
├── examples/                Example SLOP programs
│   ├── rate-limiter.slop    Token bucket rate limiter
│   ├── hello.slop           Minimal example
│   ├── fibonacci.slop       Fibonacci sequence
│   ├── http-server-threaded/ Multi-threaded HTTP server with worker pool
│   ├── c-interop/           Calling SLOP libraries from C
│   └── ...                  Additional examples
└── tests/                   Test suite
```

## Installation

### Install via Homebrew (macOS)

```bash
brew tap slop-lang/slop
brew trust slop-lang/slop   # Homebrew 6.0+ requires trusting third-party taps
brew install slop
```

Builds the native toolchain from source and installs the `slop` CLI in an
isolated virtualenv, alongside the standalone `slop-parser`, `slop-checker`,
`slop-compiler`, and `slop-tester` binaries. `slop build` transpiles to C and
calls `cc`, so install the Xcode Command Line Tools: `xcode-select --install`.

```bash
slop --version
slop build examples/fibonacci.slop -o fib && ./fib
```

### Download a release (recommended)

Pre-built toolchains for Linux x64, macOS arm64, and Windows x64 are attached to
each [GitHub Release](https://github.com/slop-lang/slop/releases). Each archive
bundles the native binaries (`slop-parser`, `slop-checker`, `slop-compiler`,
`slop-tester`), the standard library, the runtime header, specs, and examples.
Verify downloads against the `SHA256SUMS` file published with the release.

```bash
# Linux x64 (replace VERSION with the release tag, e.g. v0.1.1)
curl -LO https://github.com/slop-lang/slop/releases/download/VERSION/slop-VERSION-linux-x64.tar.gz
tar -xzf slop-VERSION-linux-x64.tar.gz
cd slop-VERSION-linux-x64

# Install to /usr/local (or set PREFIX=~/.local for a user install)
./install.sh

slop --help        # Python CLI wrapper (requires Python 3.11+)
slop-compiler      # standalone native compiler (no Python required)
```

> The `slop` command is a thin Python wrapper that orchestrates the native
> binaries; it needs Python 3.11+. The `slop-*` binaries run standalone.

#### macOS Gatekeeper

The release binaries are not yet Apple-notarized, so macOS flags them with a
quarantine attribute on download and blocks each one on first run. `install.sh`
clears this automatically. If you run the binaries directly from the extracted
folder instead of installing, clear the whole folder once:

```bash
xattr -dr com.apple.quarantine slop-VERSION-macos-arm64
```

#### Windows

Unzip the Windows archive and run `install.ps1`, or call `bin\slop.cmd` from
the extracted folder. Besides Python 3.11+, `slop build` and `slop test` need
a C compiler on PATH:

- MinGW-w64 gcc (MSYS2's `mingw-w64-x86_64-gcc`, for example), or
- LLVM clang, which targets MSVC and finds the Visual Studio headers and
  libraries itself.

The CLI uses `CC` when it is set (on every platform), and on Windows otherwise
the first of `cc`, `gcc` and `clang` it finds. `pthread` and `m` in a
`slop.toml`'s libraries are left out of the link there, since the C runtime and
the Win32 API cover them. Library builds (`--library`) aren't supported on
Windows yet. To build SLOP's generated C inside another build, such as a Rust
`-sys` crate, compile it with clang-cl or MinGW gcc against `slop_runtime.h`;
it needs no pthreads library.

### Build from source

```bash
# Cold-start the native toolchain from the bootstrap C snapshot, then self-host
make install        # build bootstrap C -> bin/
make selfhost       # two-stage rebuild from current SLOP source

uv pip install -e . # install the Python CLI wrapper
```

## Usage

```bash
# Install (using uv)
uv pip install -e .

# Parse and inspect
slop parse examples/rate-limiter.slop

# Show holes
slop parse examples/rate-limiter.slop --holes

# Transpile to C
slop transpile examples/rate-limiter.slop -o rate_limiter.c

# Type check
slop check examples/rate-limiter.slop

# Verify contracts with Z3 (requires: pip install z3-solver)
slop verify examples/rate-limiter.slop

# Full build (requires cc)
slop build examples/rate-limiter.slop -o rate_limiter

# Language reference (for AI coding assistants)
slop ref                      # Full reference
slop ref types                # Just type system
slop ref --list               # List available topics

# Generate documentation from source
slop doc examples/fibonacci.slop           # Markdown to stdout
slop doc examples/fibonacci.slop -o doc.md # Write to file
slop doc examples/fibonacci.slop -f json   # JSON output for tooling

# Validate a hole implementation against expected type
slop check-hole '(+ x 1)' -t Int -p '((x Int))'

# With context from a file
slop check-hole '(helper 42)' -t Int -c myfile.slop

# From stdin
echo '(ok value)' | slop check-hole -t '(Result T E)'

# Run the @example annotations as tests
slop test examples/fibonacci.slop

# Format source in place (comments are kept); --check for CI
slop format src/*.slop
slop format --check src/*.slop

# Show resolved paths (useful for debugging SLOP_HOME)
slop paths                     # SLOP_HOME, stdlib, and the four native binaries
slop paths -v                  # Include examples list
```

### Generating SLOP from Schemas (`slop derive`)

`slop derive` turns an external schema into a SLOP module deterministically
(no LLM). The output builds with the current compiler and is wrapped in a
`(module NAME (export ...) ...)` named after the `-o` file.

```bash
slop derive schema.json -o models.slop          # JSON Schema -> types
slop derive tables.sql -o tables.slop           # SQL DDL (CREATE TABLE / CREATE TYPE ... AS ENUM)
slop derive petstore.yaml -o petstore.slop      # OpenAPI 3 / Swagger 2: types + one fn per operation
slop derive petstore.yaml -s map -o store.slop  # ... with an in-memory Map-backed implementation
```

- **JSON Schema:** objects become records (optional properties are
  `(Option T)`), string enums become enums, `oneOf`/`anyOf` become unions,
  numeric bounds become range types, and `date`/`date-time` become `String`
  with a comment.
- **SQL:** one record per table; nullable columns are `(Option T)`, and
  `VARCHAR(n)` is `(String .. n)`.
- **OpenAPI:** each operation is a function with `@intent`, `@spec`, `@pre`
  and a hole returning `(Result T ApiError)`. `-s` picks the storage:
  `stub` (default; a `@requires storage` block you implement), `map` (a
  working in-memory implementation, no holes) or `none` (types and holes only).

Anything it cannot express is emitted as `String` with a `;;` comment, and
reported on stderr; it never emits an undefined type.

### Native Components

SLOP includes native (self-hosted) implementations of core compiler components written in SLOP itself:

```bash
# Build the native toolchain from source
make build-native
```

Native component sources are in `lib/compiler/`:
- `lib/compiler/parser/` - Native S-expression parser
- `lib/compiler/checker/` - Native type checker
- `lib/compiler/transpiler/` - Transpiler modules (used by compiler)
- `lib/compiler/compiler/` - Merged compiler (type check + transpile in one pass)
- `lib/compiler/tester/` - Native test runner

The merged `slop-compiler` binary is the primary build tool — it runs the type checker and transpiler together. Pre-built binaries are installed to `bin/` at the project root.

### SLOP_HOME Environment Variable

Set `SLOP_HOME` to specify a canonical location for SLOP resources. When set, the toolchain looks here first before falling back to package-relative paths:

```bash
export SLOP_HOME=/path/to/slop
```

Expected structure:
```
$SLOP_HOME/
├── lib/std/     # Standard library modules
├── examples/    # Example SLOP programs
├── bin/         # Native toolchain binaries
└── spec/        # Language specification files
```

Use `slop paths` to see resolved paths:

```bash
$ slop paths
SLOP Path Resolution
==================================================
SLOP_HOME: /home/user/slop (set and valid)

Resolved Directories:
--------------------------------------------------
  Spec dir        /home/user/slop/spec
  Examples dir    /home/user/slop/examples
  Stdlib dir      /home/user/slop/lib/std
  Bin dir         /home/user/slop/bin
  ...
```

### Compiler Warnings

`slop build` and `slop test` print the transpiler's warnings to stderr, such as
a closure allocated with no arena in scope, whether the build has one module
or many. When the checker leaves an expression without a type annotation, the
transpiler infers the type itself. It reports each place it did that only when
asked:

```bash
SLOP_WARN_FALLBACK=1 slop build src/main.slop
```

These lines help when working on the compiler; they are not something a
program can fix.

## Project Configuration

Create a `slop.toml` file to configure your project:

```toml
[project]
name = "my-project"
version = "0.1.0"
entry = "src/main.slop"        # Main module

[build]
output = "build/myapp"         # Output path (directory created if needed)
include = ["src", "lib"]       # Module search paths
type = "executable"            # "executable", "static", or "shared"
debug = false

[build.link]
libraries = ["pthread"]        # -l flags
library_paths = []             # -L flags
```

With a `slop.toml`, commands use project settings automatically:

```bash
slop build                     # Uses [project].entry, outputs to [build].output
slop build --debug             # CLI flags override config
slop fill                      # Uses entry from config
slop fill -c slop.toml         # Explicit config path
```

### Hole Filler Configuration

Configure LLM providers and tier routing for `slop fill`:

```toml
[providers.ollama]
type = "ollama"
base_url = "http://localhost:11434"

[providers.openai]
type = "openai-compatible"
base_url = "https://api.openai.com/v1"
api_key = "${OPENAI_API_KEY}"

[tiers.tier-1]
provider = "ollama"
model = "phi3:mini"

[tiers.tier-2]
provider = "ollama"
model = "llama3:8b"

[tiers.tier-3]
provider = "ollama"
model = "llama3:70b-q4"

[tiers.tier-4]
provider = "openai"
model = "gpt-4o"
```

See `slop.toml.example` for complete configuration options.

## Hybrid Generation Pipeline

```
┌─────────────────┐
│  JSON Schema    │  ← External specs
│  SQL DDL        │
│  OpenAPI        │
└────────┬────────┘
         │ Deterministic
         ▼
┌─────────────────┐
│  SLOP Types     │  ← Generated types + signatures
│  + Signatures   │
└────────┬────────┘
         │ LLM (tiered)
         ▼
┌─────────────────┐
│  SLOP + Impl    │  ← Holes filled by appropriate model
└────────┬────────┘
         │ Deterministic
         ▼
┌─────────────────┐
│  Verification   │  ← Type check, contract check
└────────┬────────┘
         │ Deterministic
         ▼
┌─────────────────┐
│  C Source       │  ← Transpiled output
└────────┬────────┘
         │ cc -O3
         ▼
┌─────────────────┐
│  Native Binary  │  ← Optimized executable
└─────────────────┘
```

## Contract Verification

SLOP can mathematically prove that implementations satisfy their contracts using Z3 SMT solving. Rather than just checking types or running tests, `slop verify` translates code and contracts into logical constraints and asks: *is there any input where the preconditions hold but the postcondition doesn't?* If no such input exists (UNSAT), the contract is proven. If one does (SAT), it's returned as a counterexample.

```bash
# Verify contracts (requires: pip install z3-solver)
slop verify examples/rate-limiter.slop
```

### Example

Consider a function that clamps a value to a range:

```lisp
(fn clamp ((val Int) (lo Int) (hi Int))
  (@intent "Clamp val to [lo, hi]")
  (@spec ((Int Int Int) -> Int))
  (@pre {lo <= hi})
  (@post {$result >= lo})
  (@post {$result <= hi})

  (if (< val lo)
    lo
    (if (> val hi)
      val        ;; Bug: should return hi
      val)))
```

The verifier catches the bug — when `val > hi`, returning `val` violates `$result <= hi`. It reports a counterexample (e.g., `val=10, hi=5`) showing exactly how the contract breaks. Fix `val` to `hi` in the second branch and verification passes.

### What It Verifies

- **`@pre` / `@post`** — preconditions and postconditions on functions
- **`@property`** — universal assertions over results (e.g., `(forall (t $result) (pred t))`)
- **Range types** — every value a function returns fits its range return type
- **Union types** — tag and payload axioms for `match` postconditions on `Option`/`Result` fields
- **`@callback-assume`** — properties of callback arguments in higher-order functions

### How It Works

The verifier translates a function body into Z3 constraints relating `$result` to the parameters, following `let` bindings and treating `if`/`cond`/`match` branches as path conditions, then asks the solver whether any input satisfying the preconditions can violate a postcondition. For loops, it detects common patterns (filter, map, count, fold) and automatically generates universally quantified axioms connecting outputs to inputs — no manual invariants needed for recognized patterns.

When automatic detection isn't enough, you can provide explicit guidance. A `@loop-invariant` is proved before it is used - it must hold when the loop starts and every iteration must keep it - while `@assume` is trusted:

```lisp
;; Inside a loop body
(@loop-invariant {count >= 0})

;; Or trust a postcondition the solver can't reach
(@assume {(forall (t $result) (valid t))})
```

### Limitations

- **Complex helper chains** — deeply nested function calls (e.g., `term-eq` → `literal-eq` → `option-string-eq`) can't be auto-verified. Use `@trusted` or `@assume`.
- **Unrecognized loop patterns** — loops that don't match filter/map/count/fold need `@loop-invariant` or `@assume`.
- **Recursion** — recursive functions aren't inlined; verification is limited to non-recursive bodies.
- **Solver timeouts** — very complex constraint systems may hit the Z3 timeout.

## Typed Holes

Holes are placeholders where LLMs generate code, constrained by types and contracts:

```lisp
(fn validate-age ((age Int))
  (@intent "Check if age is valid for registration")
  (@spec ((Int) -> (Result (Int 18 .. 120) String)))

  (hole (Result (Int 18 .. 120) String)
    "validate age is between 18 and 120, return error message if invalid"
    :complexity tier-2))
```

The hole specifies:
- **Return type**: `(Result (Int 18 .. 120) String)` — must return this exact type
- **Prompt**: Natural language description of what to generate
- **Complexity**: `tier-2` — routes to an appropriately-sized model

Running `slop fill` replaces the hole with a valid implementation:

```lisp
(if (and (>= age 18) (<= age 120))
    (ok age)
    (error "Age must be between 18 and 120"))
```

## Generics

Functions can be parameterized over types using `@generic`:

```lisp
(fn send ((ch (Ptr (Chan Int))) (value Int))
  (@intent "Send value to channel, blocking if full/unbuffered")
  (@generic (T))
  (@spec (((Ptr (Chan T)) T) -> (Result Unit ChanError)))
  (@pre {ch != nil})
  ...)
```

The type parameter `T` is declared in `@generic` and used in `@spec`. At call sites, the type checker unifies argument types to bind `T` and compute the return type. Multiple type parameters are supported: `(@generic (T U V))`.

**Current limitations:**

- **Functions only** — `@generic` annotates functions, not type definitions. Generic types like `Option`, `List`, `Result`, `Chan`, etc. are built-in.
- **No monomorphization** — Type parameters compile to `int64_t` in C. One C function is generated per generic function, not one per type instantiation.
- **Concrete types in function bodies** — The `fn` parameters and body must use concrete types; type variables only appear in `@spec`. The generics are a type-checking feature, not a code generation feature.

## Model Tiering

Holes are routed to appropriately-sized models:

| Tier | Model Size | Use Case |
|------|------------|----------|
| tier-1 | 1-3B | Boolean expressions, simple arithmetic |
| tier-2 | 7-8B | Single conditional, Result construction |
| tier-3 | 13-34B | Loops, multiple conditions |
| tier-4 | 70B+ | Algorithms, complex logic |

```lisp
(hole Bool "Check if user is adult"
  :complexity tier-1)  ; Small model handles this

(hole (Result User Error) "Validate and update user"
  :complexity tier-3   ; Needs larger model
  :required (input db-update validate-email))
```

## Why C?

Because that's what I want.  And also:

C's problems are **human** problems:
- Manual memory management? Machines don't forget
- No namespaces? Machines use prefixes consistently
- Buffer overflows? Transpiler generates safe patterns

C's benefits remain:
- 10-100x faster than interpreted languages
- Universal FFI to any library
- 50 years of optimizer engineering
- Runs everywhere

## Other Targets

Aside from C, an obvious choice for a future target would be typescript.
WASM would also be easy to do since we're already transpiling to C.

## FFI and C Interoperability

SLOP provides seamless bidirectional FFI with C.

### Calling C from SLOP

Import C functions from headers and map C struct layouts:

```lisp
;; Import C functions from headers
(ffi "sys/socket.h"
  (socket ((domain Int) (type Int) (protocol Int)) Int)
  (bind ((fd Int) (addr (Ptr Void)) (len U32)) Int))

;; Map C struct layouts for interop
(ffi-struct "netinet/in.h" sockaddr_in
  (sin_family U16)
  (sin_port U16)
  (sin_addr U32)
  (sin_zero (Array U8 8)))
```

The `ffi-struct` form defines the exact memory layout matching the C struct, enabling direct interop with system libraries. Nested structs are supported via inline `ffi-struct` definitions.

### Calling SLOP from C

Build SLOP modules as libraries and call them from C code using the `:c-name` attribute:

```lisp
(module mylib
  (type Config (record (timeout Int) (retries Int)))

  (fn add-numbers ((a Int) (b Int))
    (@intent "Add two numbers")
    (@spec ((Int Int) -> Int))
    (+ a b)
    :c-name "mylib_add")

  (fn create-config ((timeout Int) (retries Int))
    (@intent "Create a config struct")
    (@spec ((Int Int) -> Config))
    (Config timeout retries)
    :c-name "mylib_create_config"))
```

Build as a static or shared library:

```bash
# Build static library
slop build mylib.slop --library static -o libmylib

# Build shared library
slop build mylib.slop --library shared -o libmylib
```

This generates:
- `libmylib.a` or `libmylib.so` - The compiled library
- `slop_mylib.h` - Module header with type definitions and `#define` aliases for `:c-name` functions

Use the module header in your C code:

```c
#include "slop_mylib.h"

int main(void) {
    int64_t sum = mylib_add(10, 20);
    mylib_Config cfg = mylib_create_config(60, 5);
    return 0;
}
```

Compile and link:

```bash
cc -o main main.c -L. -lmylib -I/path/to/slop/src/slop/runtime
```

See `examples/c-interop/` for a complete working example.

## Memory Model

Arena allocation handles 90% of cases:

```lisp
(fn handle-request ((arena Arena) (req Request))
  (@alloc arena)
  (let ((user (parse-user arena req))
        (resp (process arena user)))
    (send resp)))
; Arena freed by caller
```

## Implementation Status

**Implemented:**
- ✓ Language specification
- ✓ S-expression parser with pretty-printing
- ✓ SLOP → C transpiler with type flow analysis
- ✓ Type checker with range inference and path-sensitive analysis
- ✓ Self-hosting compiler (parser, checker, transpiler, merged compiler — all written in SLOP)
- ✓ Generics (`@generic` with type parameter unification)
- ✓ Standard library (`lib/std/`: strlib, io, math, os, path, json, xml, thread)
- ✓ Bootstrap build system (build from pre-generated C — no SLOP installation required)
- ✓ Concurrency primitives (channels, spawn/join via `lib/std/thread`)
- ✓ Range types enforced: at compile time where the value is known, at run time otherwise
- ✓ Runtime contract assertions in `--debug` builds (`SLOP_PRE`/`SLOP_POST`)
- ✓ FFI struct mapping (`ffi-struct` for C struct layouts)
- ✓ C interop libraries (`:c-name` for clean exports, public header generation)
- ✓ Hole extraction, classification, and tiered model routing
- ✓ LLM providers (Ollama, OpenAI-compatible, Interactive, Multi-provider)
- ✓ Hole filler with quality scoring and pattern library
- ✓ CLI tooling (`slop` command): build, check, test, verify, fill, format, doc, derive, ref
- ✓ Editor support: tree-sitter grammar and an Emacs mode (`tree-sitter-slop/`)
- ✓ Runtime header with arena allocation
- ✓ Contract verification via Z3 (`slop verify`) — path-sensitive body analysis, loop invariants, pattern detection
- ✓ Test suite

**Not Yet Implemented:**
- Full generics (monomorphization, generic type definitions, type variable substitution in codegen)
- Property-based testing generation
- The forms listed in spec/LANGUAGE.md section 10 (`array`, `put`, `try`/`catch`, structured patterns, `Slice`, ...)

## License

Apache 2.0
