# SLOP - Symbolic LLM-Optimized Programming

A programming language designed for minimal human involvement in coding.

```
Humans specify WHAT and WHY → Machines handle HOW
```

## Philosophy

SLOP inverts the traditional programming model:

| Traditional | SLOP |
|-------------|------|
| Human writes code | Human writes specification |
| Compiler checks syntax | Machine generates implementation |
| Tests verify behavior | Contracts define correctness |
| Libraries provide code | Schemas generate types |

## Design Choices

- **S-expression syntax**: Zero parsing ambiguity, trivial for LLMs
- **Range types**: `(Int 0 .. 100)` catches bounds errors at compile time
- **Mandatory contracts**: `@intent`, `@spec`, `@pre`, `@post` define correctness
- **Typed holes**: Explicit markers for LLM generation with complexity tiers
- **Transpiles to C**: Maximum performance, universal FFI, minimal runtime

## Quick Example

```lisp
(module rate-limiter
  (export (acquire 1))
  
  (type Tokens (Int 0 .. 10000))
  
  (fn acquire ((limiter (Ptr Limiter)))
    (@intent "Try to acquire one token")
    (@spec (((Ptr Limiter)) -> AcquireResult))
    (@pre (!= limiter nil))
    
    (if (> (. limiter tokens) 0)
      (do
        (set! limiter tokens (- (. limiter tokens) 1))
        'acquired)
      'rate-limited)))
```

Transpiles to:

```c
AcquireResult acquire(Limiter* limiter) {
    SLOP_PRE(limiter != NULL, "limiter != nil");
    
    if (limiter->tokens.value > 0) {
        limiter->tokens = Tokens_new(limiter->tokens.value - 1);
        return AcquireResult_acquired;
    } else {
        return AcquireResult_rate_limited;
    }
}
```

## Project Structure

```
slop/
├── spec/                    Language specifications
│   ├── LANGUAGE.md          Grammar, types, semantics
│   └── HYBRID_PIPELINE.md   Generation architecture
├── runtime/
│   └── slop_runtime.h       Minimal C runtime (~400 lines)
├── examples/
│   ├── rate-limiter.slop    Complete example
│   ├── user-service-hybrid.slop  Hybrid generation demo
│   └── generated/           Example C output
├── tooling/src/
│   ├── parser.py            S-expression parser
│   ├── transpiler.py        SLOP → C transpiler
│   ├── hole_filler.py       LLM integration
│   ├── schema_converter.py  JSON Schema → SLOP types
│   └── slop_cli.py          Command-line interface
└── skill/                   Claude skill for SLOP generation
```

## Usage

```bash
# Parse and inspect
python tooling/src/slop_cli.py parse examples/rate-limiter.slop

# Show holes
python tooling/src/slop_cli.py parse examples/user-service-hybrid.slop --holes

# Transpile to C
python tooling/src/slop_cli.py transpile examples/rate-limiter.slop -o rate_limiter.c

# Validate
python tooling/src/slop_cli.py check examples/rate-limiter.slop

# Full build (requires cc)
python tooling/src/slop_cli.py build examples/rate-limiter.slop -o rate_limiter
```

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
  :must-use (input db-update validate-email))
```

## Why C?

C's problems are **human** problems:
- Manual memory management → Machines don't forget
- No namespaces → Machines use prefixes consistently
- Buffer overflows → Transpiler generates safe patterns

C's benefits remain:
- 10-100x faster than interpreted languages
- Universal FFI to any library
- 50 years of optimizer engineering
- Runs everywhere

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

## Status

**Implemented:**
- ✓ Language specification
- ✓ S-expression parser
- ✓ SLOP → C transpiler
- ✓ Hole extraction and classification
- ✓ Mock LLM provider
- ✓ CLI tooling
- ✓ Runtime header

**Not Yet Implemented:**
- Type checker with range inference
- Contract verification (SMT solver)
- Real LLM provider integration
- Property-based testing

## License

MIT
