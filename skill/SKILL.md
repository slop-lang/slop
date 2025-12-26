---
name: slop
description: |
  Generate code in SLOP (Symbolic LLM-Optimized Programming), a language designed for 
  minimal human involvement in coding. Use when: (1) User asks for SLOP code, (2) Need 
  strong contracts and range types, (3) Creating code with typed holes for incremental 
  generation, (4) Generating efficient C code. SLOP uses S-expression syntax and transpiles to C.
---

# SLOP Language Skill

SLOP is designed for hybrid generation where humans specify intent and machines generate code.

## Philosophy

```
Humans: Specify WHAT (intent, contracts, types, examples)
Machines: Handle HOW (implementation, verification, compilation)
```

## Quick Reference

### Syntax

```
;; Comment
(module name (export ...) forms...)
(type Name type-expr)
(fn name ((param Type)...) annotations... body)
```

### Types with Ranges

```
(Int)                  ; Any integer
(Int 0 ..)             ; Non-negative
(Int 1 .. 100)         ; Bounded range
(U8) (I32) (U64)       ; Explicit width
(String 1 .. 255)      ; Length-bounded string
(List T 1 ..)          ; Non-empty list
(Array T 10)           ; Fixed-size array
(Ptr T)                ; Pointer to T
(Option T)             ; T or nil
(Result T E)           ; Success or error
(enum a b c)           ; Enumeration (simple, no data)
(record (x T) (y U))   ; Struct
```

### Enums (Simple)

Simple enums are just symbolic values - NO data attached:

```
(type Status (enum pending active done))

;; Return enum value - just use the symbol directly
(fn get-status ()
  (@spec (() -> Status))
  active)              ; just the symbol name

;; Compare enum values
(== status active)
```

**DO NOT use `union-new` for simple enums.** That's only for tagged unions with data.

#### Matching Simple Enums

Simple enums have NO data, so you CANNOT bind variables in match patterns:

```
(type FizzBuzzResult (enum Fizz Buzz FizzBuzz Number))

;; CORRECT - bare symbols, no bindings
(match result
  (Fizz (println "Fizz"))
  (Buzz (println "Buzz"))
  (FizzBuzz (println "FizzBuzz"))
  (Number (println (int-to-string arena i))))  ; use outer variable 'i', NOT a binding

;; WRONG - trying to bind 'n' from Number (simple enums have no data!)
(match result
  ((Number n) (println n)))   ; ERROR: Number has no data to bind
```

### Tagged Unions (With Data)

Use `union-new` ONLY for unions that carry associated data:

```
(type Result (union
  (ok Int)
  (error String)))

;; Construct tagged union values
(union-new Result ok 42)       ; Result with ok=42
(union-new Result error "bad") ; Result with error="bad"

;; Match with bindings - tagged unions DO have data
(match result
  ((ok val) (println (int-to-string arena val)))   ; bind 'val' from ok variant
  ((error msg) (println msg)))                      ; bind 'msg' from error variant
```

### Required Annotations

```
(fn name ((params...))
  (@intent "Human-readable purpose")     ; REQUIRED
  (@spec ((ParamTypes) -> ReturnType))   ; REQUIRED
  body)
```

### Optional Annotations

```
(@pre condition)           ; Precondition
(@post condition)          ; Postcondition ($result = return value)
(@example (args) -> result) ; Test case
(@alloc arena)             ; Memory allocation strategy
(@pure)                    ; No side effects, does NOT take arena param
```

### Memory Model

```
;; Arena allocation (primary pattern)
(fn handle ((arena Arena) (input Input))
  (let ((data (arena-alloc arena (sizeof Data))))
    ...))

;; Scoped arena - creates 'arena' variable in scope
(with-arena 4096
  (let ((x (alloc ...)))
    ...))  ; Arena freed at end
```

**IMPORTANT:** The `arena` variable only exists inside `with-arena` blocks or when passed as a function parameter. Using `arena` outside these contexts is an error.

```
;; CORRECT - arena from with-arena block
(fn main ()
  (with-arena 1024
    (println (int-to-string arena 42))))

;; WRONG - arena not in scope
(fn main ()
  (println (int-to-string arena 42)))  ; ERROR: arena undefined
```

### Holes (For LLM Generation)

```
(hole Type "prompt"
  :complexity tier-N)          ; REQUIRED - selects appropriate model
```

#### Complexity Tiers (REQUIRED)

Specify `:complexity` based on the **control flow** needed:

| Tier | Heuristic | Control Flow |
|------|-----------|--------------|
| tier-1 | Single expression, no branching | Literals, arithmetic, field access, enum variant |
| tier-2 | One level of branching | `if`/`cond`/`match` without nesting |
| tier-3 | Iteration or recursion | `for`/`while`/`for-each`, recursive calls |
| tier-4 | Nested control flow + state | Nested loops, accumulators, multi-pass algorithms |

**Rules:**
- No branching → tier-1
- Branching without loops → tier-2
- Any loop or recursion → tier-3
- Nested loops or complex state → tier-4

#### Optional Hole Attributes

```
:must-use (var1 var2)          ; Identifiers that MUST appear
:examples ((in) -> out)        ; Example input/output pairs
```

### Common Patterns

```
;; Error handling
(match (might-fail x)
  ((ok val) (use val))
  ((error e) (handle e)))

;; Field access
(. record field)           ; record->field
record.field               ; record->field (shorthand)
(set! record field value)  ; record->field = value
(set! ptr.field value)     ; ptr->field = value

;; Loops
(for (i 0 10) body)
(for-each (x list) body)
(while cond body)
```

### FFI (Foreign Function Interface)

```
;; Declare C functions
(ffi "header.h"
  (func-name ((param Type)...) ReturnType)
  ...)

;; Declare C structs for field access
(ffi-struct "header.h" struct_name
  (field1 Type1)
  (field2 Type2))

;; Type casting
(cast Type expr)                   ; Cast to Type

;; C inline escape hatch
(c-inline "SOME_C_CONSTANT")
(c-inline "sizeof(struct foo)")
```

Example:
```
(ffi "unistd.h"
  (read ((fd Int) (buf (Ptr U8)) (n U64)) I64)
  (write ((fd Int) (buf (Ptr U8)) (n U64)) I64)
  (close ((fd Int)) Int))

(ffi-struct "netinet/in.h" sockaddr_in
  (sin_family U16)
  (sin_port U16)
  (sin_addr U32))

;; Use directly
(let ((addr (arena-alloc arena (sizeof sockaddr_in))))
  (set! addr.sin_family 2)
  (set! addr.sin_port (htons 8080)))
```

## C Mapping

```
SLOP                    C
────                    ─
(Int 0 .. 150)     →    struct { uint8_t value; } + range check
(Ptr User)         →    User*
(. user name)      →    user->name
(arena-alloc ...)  →    slop_arena_alloc(...)
(@pre cond)        →    SLOP_PRE(cond, "...")
```

## Generation Guidelines

1. Always include @intent and @spec
2. Use range types to constrain values
3. Pass Arena as first param for allocating functions
4. Use (Result T E) for fallible operations
5. ALWAYS specify `:complexity` on holes (tier-1: no branching, tier-2: branching, tier-3: loops, tier-4: nested/complex)
6. Prefer (. x field) over direct pointer syntax
7. ONLY use functions from references/builtins.md or defined via FFI
8. When unsure if a function exists, check builtins.md first
9. SLOP is minimal - no convenience functions. Convert types explicitly.

## See Also

- references/builtins.md - Complete built-in function list (CHECK THIS FIRST)
- references/types.md - Full type system
- references/patterns.md - Common patterns
