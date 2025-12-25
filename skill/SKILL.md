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
(enum a b c)           ; Enumeration
(record (x T) (y U))   ; Struct
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
(@pure)                    ; No side effects
```

### Memory Model

```
;; Arena allocation (primary pattern)
(fn handle ((arena Arena) (input Input))
  (let ((data (arena-alloc arena (sizeof Data))))
    ...))

;; Scoped arena
(with-arena 4096
  (let ((x (alloc ...)))
    ...))  ; Arena freed at end
```

### Holes (For LLM Generation)

```
(hole Type "prompt")
(hole Type "prompt" 
  :complexity tier-2          ; tier-1 to tier-4
  :must-use (var1 var2)
  :examples ((in) -> out))
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
5. Mark hole complexity for optimal model routing
6. Prefer (. x field) over direct pointer syntax

## See Also

- references/types.md - Full type system
- references/patterns.md - Common patterns
