# SLOP Quick Reference

Reference guide for LLM code generation. See LANGUAGE.md for the full specification.

## Common Mistakes

These functions/patterns do NOT exist in SLOP - use the alternatives:

| Don't Use | Use Instead |
|-----------|-------------|
| `print-int n` | `(println n)` -- println takes a String, Int, Bool or Float |
| `print-float n` | `(println x)`, or strlib `(float-to-string arena x precision)` |
| `(println enum-value)` | Use `match` to print different strings |
| `arena` outside with-arena | Wrap code in `(with-arena size ...)` |
| `(block ...)` | `(do ...)` for sequencing |
| `(begin ...)` | `(do ...)` for sequencing |
| `(progn ...)` | `(do ...)` for sequencing |
| `read-line` | FFI to stdio.h |
| `sqrt`, `sin`, `cos` | `(import mathlib (...))`, or FFI to math.h |
| `strlen s` | `(string-len s)` |
| `malloc` | `(arena-alloc arena size)` |
| `arr.length` | Arrays are fixed size - use declared size |
| `list.length` | `(list-len list)` |
| `list-append` | `(list-push list elem)` |
| `list-add` | `(list-push list elem)` |
| `map-set` | `(map-put map key val)` |
| `hash-get` | `(map-get map key)` |
| `(== opt (none))` | `(is-none opt)` -- `==` on an Option is an error |
| `(!= opt (none))` | `(is-some opt)` |
| `string->int`, `atoi` | strlib `(parse-int s)` -> `(Result Int ParseError)` |
| `json-parse` | `(import json (...))` |
| `string-find` | strlib `(index-of s needle)` |
| `(list 1 2 3)` | `(list Int 1 2 3)` -- the element type is required |
| `(Shape circle 5)`, `(circle 5)` | `(Shape (circle 5))` or `(union-new Shape circle 5)` |
| `(if c a b d)` | `(if c (do a b) d)` -- at most three operands |
| `(< a b c)` | `(and (< a b) (< b c))` |
| `3.14f`, `1.` | `3.14`, `1.0` |
| `(set! x v)` on a plain let | `(let ((mut x ...)) ...)` |
| `(list-push x v)` where x is a for-each/match binding | grow a `(let ((mut c x)))` copy and write it back, or use `(Ptr T)` elements |
| `(is-ok r)`, `(try ...)`, `(put ...)`, `(array ...)` | not implemented: `match` the Result; `(let ((mut c r)) (set! c f v) c)`; `(list T ...)` |
| Definitions outside `(module ...)` | All `(type)`, `(fn)`, `(const)` go inside the module form |

## Module Structure

All definitions must be inside the module form:

```lisp
(module my-module
  (export public-fn)
  (import other-module (helper))

  (type MyType (Int 0 ..))

  (fn public-fn (...)
    ...)

  (fn private-fn (...)
    ...))  ; <-- closing paren wraps entire module
```

**Wrong** (definitions outside module):
```lisp
(module my-module
  (export public-fn))

(fn public-fn ...)  ; ERROR: outside module form
```

## Built-in Functions

### I/O

```lisp
(print v)                ; print a String, Int, Bool or Float, no newline
(println v)              ; ... with newline
```

### String Operations

```lisp
(int-to-string arena n)   ; Int -> String (requires arena)
(string-len s)            ; String -> Int
(string-concat arena a b) ; String String -> String
(string-eq a b)           ; String String -> Bool
; More in strlib: substring, index-of, starts-with, contains, trim, replace, parse-int, ...
```

### Memory

```lisp
(arena-new size)         ; create arena
(arena-alloc arena size) ; allocate from arena
(arena-free arena)       ; free arena
(with-arena size body)   ; scoped arena (implicit 'arena' var), freed on every exit;
                         ; what the block returns must not point into it
(sizeof Type)            ; size of type in bytes
(addr expr)              ; address-of (&expr)
(deref ptr)              ; dereference pointer (*ptr)
```

### Data Construction

```lisp
(ok val)                 ; Result success
(error 'variant)         ; Result error (QUOTE the variant!)
(some val)               ; Option some
none                     ; Option none (also written (none))
(record-new Type (field1 val1) ...)  ; create record
(union-new Type tag v ...)           ; create a union value; also (Type (tag v ...))
(list Type elem1 ...)    ; create list literal (type required; built in the arena in scope)
(set Type elem1 ...)     ; create set literal
```

### Collections

```lisp
(list-new arena Type)    ; create empty list (type parameter required)
(list Type e1 e2...)     ; list literal
(list-push list elem)    ; append; grows in the list's own arena (:arena a overrides)
(list-pop list)          ; remove and return last element -> Option
(list-get list idx)      ; get element at index -> Option
(list-len list)          ; get list length

(map-new arena K V)      ; create empty map (type parameters required)
(map-put map key val)    ; insert/update key-value pair
(map-get map key)        ; get value -> Option
(map-has map key)        ; check if key exists -> Bool
(map-keys map)           ; all keys -> (List K)
(map-remove map key)     ; remove key (requires mutable map)
(map-len map)            ; number of entries

(set-new arena Type)     ; create empty set (type parameter required)
(set Type e1 e2...)      ; set literal
(set-put set elem)       ; add element
(set-has set elem)       ; check membership -> Bool
(set-remove set elem)    ; remove element
(set-len set)            ; number of elements
(set-elements set)       ; all elements -> (List T)
```

### Field Access

```lisp
(. record field)         ; field access (auto -> for pointers)
(set! record field val)  ; field mutation
(@ arr idx)              ; array indexing
```

A `for-each` or `match` binding is a copy: `list-push`/`list-pop` on it, or on a
List field of it, is an error.

## Loop Patterns

### Find Index Matching Predicate

```lisp
(let ((mut result -1))
  (for (i 0 SIZE)
    (when PREDICATE
      (do
        (set! result i)
        (break))))
  result)
```

### Count Matching Elements

```lisp
(let ((mut count 0))
  (for (i 0 SIZE)
    (when PREDICATE
      (set! count (+ count 1))))
  count)
```

### Sum Values

```lisp
(let ((mut total 0))
  (for (i 0 SIZE)
    (set! total (+ total ACCESSOR)))
  total)
```

### Find Empty Slot

```lisp
(let ((mut idx -1))
  (for (i 0 SIZE)
    (when (== (. (@ storage i) id) 0)
      (do
        (set! idx i)
        (break))))
  idx)
```

### Array Shift Delete

```lisp
(for (i idx (- SIZE 1))
  (set! (@ arr i) (@ arr (+ i 1))))
```

## Match Patterns

### Simple Enums (No Bindings)

Simple enums have no data - QUOTE the variant name. A bare name is a binding
that matches anything:

```lisp
(match status
  ('pending (println "waiting"))
  ('active (println "running"))
  ('done (println "finished")))
```

### Tagged Unions (With Bindings)

Union variants, Result and Option carry data - bind with parens, one name per
payload:

```lisp
(match shape
  ((circle r) (* 3.0 (* r r)))
  ((rect w h) (* w h))
  ((point) 0.0))
```

```lisp
(match result
  ((ok val) (use val))
  ((error e) (handle e)))

(match option
  ((some x) (use x))
  ((none) (handle-none)))
```

**Note:** Variant names must be globally unique across all enum and union types
in a module. Using the same variant name in different types will result in a
compile error.

**Recursive unions:** A variant cannot embed its parent union by value (this
creates an infinite-size C struct). Use `(Ptr T)` or `(List T)` for
self-referencing variants. `(Option T)` also embeds by value and is not allowed.

### Error Returns

IMPORTANT: Quote the error variant!

```lisp
(if (< fd 0)
  (error 'file-not-found)    ; CORRECT: quoted
  (ok data))

; WRONG: (error file-not-found) - unquoted is undefined variable
```

## Arena Allocation Pattern

```lisp
(fn handle-request ((req (Ptr Request)))
  (@intent "Process incoming request")
  (@spec (((Ptr Request)) -> (Ptr Response)))

  (with-arena 4096
    (let ((user (parse-user arena req))
          (result (process arena user)))
      (send-response result))))
;; Arena freed automatically at end
```

For functions that allocate:

```lisp
(fn create-user ((arena Arena) (name String) (email String))
  (@intent "Create a new user")
  (@spec ((Arena String String) -> (Ptr User)))
  (@alloc arena)

  (let ((user (cast (Ptr User) (arena-alloc arena (sizeof User)))))
    (set! user name name)
    (set! user email email)
    user))
```

## Result Pattern

```lisp
(fn read-file ((arena Arena) (path String))
  (@intent "Read file contents")
  (@spec ((Arena String) -> (Result (Ptr Bytes) IoError)))
  (@alloc arena)

  (let ((fd (open path)))
    (if (< fd 0)
      (error 'file-not-found)
      (let ((data (read-all arena fd)))
        (close fd)
        (ok data)))))
```

### Early Return with ?

```lisp
(fn process-all ((arena Arena) (paths (List String)))
  (@intent "Read every file, stopping at the first error")
  (@spec ((Arena (List String)) -> (Result (List Data) Error)))

  (let ((results (list-new arena Data)))
    (for-each (path paths)
      (let ((data (? (read-file arena path))))  ; returns early on error
        (list-push results data)))
    (ok results)))
```

## SMT Verification

SLOP uses Z3 for compile-time contract verification. This section details what's verified and how to help the verifier when automatic verification fails.

### What's Verified

The verifier checks:

- **Contract consistency**: Preconditions don't contradict postconditions
- **Range type bounds**: `(Int 0 .. 100)` generates constraints `0 <= x <= 100`
- **Type invariants**: `@invariant` on type definitions applied to parameters
- **Record field axioms**: `(record-new Type (field value))` implies `(. $result field) == value`
- **Union tag axioms**: `(union-new Type tag value)` establishes tag in match
- **Equality reflexivity**: `*-eq` functions have `(fn-eq x x) == true` axiom

### Loop Patterns

The verifier automatically detects common loop patterns and generates axioms:

**Filter pattern** - collecting items matching a predicate:

```lisp
(let ((mut result (list-new arena Int)))
  (for-each (x items)
    (if predicate (list-push result x)))
  result)
;; Axiom: (list-len result) <= (list-len items)
```

**Count pattern** - counting items matching a predicate:

```lisp
(let ((mut count 0))
  (for-each (x items)
    (if predicate (set! count (+ count 1))))
  count)
;; Axioms: count >= 0, count <= (list-len items)
```

**Fold pattern** - accumulating with an operator:

```lisp
(let ((mut acc init))
  (for-each (x items)
    (set! acc (max acc x)))
  acc)
;; Axiom for max: result >= init
```

### Escape Hatches

When automatic verification fails, use these annotations:

**`@assume`** - Trust an assertion without proof (for FFI behavior, complex invariants):

```lisp
(fn use-ffi-result ((ptr (Ptr Data)))
  (@intent "Read the value an FFI call returned")
  (@spec (((Ptr Data)) -> Int))
  (@assume (!= ptr nil))  ;; FFI guarantees non-null
  (. ptr value))
```

**`@loop-invariant`** - Provide invariant for patterns the verifier doesn't recognize:

```lisp
(fn complex-loop ((items (List Int)))
  (@intent "Sum of absolute values")
  (@spec (((List Int)) -> Int))
  (@post (>= $result 0))
  (let ((mut sum 0))
    (for-each (x items)
      (@loop-invariant (>= sum 0))  ;; Help the verifier
      (set! sum (+ sum (abs x))))
    sum))
```

**`@callback-assume`** - Declare properties of callback arguments in higher-order functions:

```lisp
(fn for-each-item ((g Graph) (callback (Fn (Item) -> Unit)))
  (@intent "Apply callback to each item in graph")
  (@spec ((Graph (Fn (Item) -> Unit)) -> Unit))
  (@callback-assume callback (graph-contains g $callback-arg))
  ...)
;; $callback-arg refers to each argument passed to the callback
```
