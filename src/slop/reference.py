"""
SLOP Language Reference - Optimized for AI coding assistants

When spec/LANGUAGE.md is updated, this file must be updated to match.
"""

TOPICS = {
    'types': """## Types

### Primitives
(Int)                   ; int64_t, any value
(I8) (I16) (I32) (I64)  ; Signed integers
(U8) (U16) (U32) (U64)  ; Unsigned integers
(Float) (F32)           ; double / float
(Bool)                  ; Boolean
(String)                ; slop_string
(Bytes)                 ; Byte buffer
(Unit)                  ; void / no value

### Range Types
(Int min ..)            ; >= min
(Int .. max)            ; <= max
(Int min .. max)        ; Bounded range
(String min .. max)     ; Length-bounded string
(Float min .. max)      ; Bounded float

; Examples
(type UserId (Int 1 ..))
(type Age (Int 0 .. 150))
(type Port (Int 1 .. 65535))

; C mapping: (Int 0 .. 255) -> uint8_t with runtime check

### Collections
(List T)                ; Dynamic array
(List T n)              ; Exactly n elements
(List T min ..)         ; At least min
(Array T n)             ; Fixed-size, stack-allocated
(Map K V)               ; Hash map
(Set T)                 ; Hash set

; Literals
(list Int 1 2 3)                    ; Explicit type
(list 1 2 3)                        ; Inferred type
(map String Int ("a" 1) ("b" 2))    ; Explicit types
(map ("a" 1) ("b" 2))               ; Inferred types

### Algebraic Types
(type Status (enum pending active done))
(type User (record (id Int) (name String)))
(type Shape (union (circle Float) (rect Float Float) (point)))

Note: Variant names must be globally unique across all enum and union types
in a module. Using the same variant name in different types causes a compile error.

Recursive unions: A variant cannot embed its parent union by value (infinite-size
struct). Use (Ptr T) or (List T) for self-referencing variants:
  (bad-node Tree)           ; ERROR — direct self-ref, infinite size
  (bad (Option Tree))       ; ERROR — Option embeds T by value
  (ok-children (List Tree)) ; OK — List is fixed-size (pointer to data)
  (ok-next (Ptr Tree))      ; OK — pointer is fixed size

### Pointers
(Ptr T)                 ; Borrowed pointer (T*)
(ScopedPtr T)           ; Scoped, auto-freed on scope exit
(OptPtr T)              ; Nullable pointer

### Utility Types
(Option T)              ; T or none
(Result T E)            ; Success or error
(Fn (A B) -> R)         ; Function pointer

### Concurrency Types (thread library)
(Chan T)                ; Typed channel
(Thread T)              ; Thread handle returning T

### Type Aliases
(type UserId (Int 1 ..))
(alias Handler (Fn (Request) -> Response))
""",

    'functions': """## Functions

### Basic Structure
(fn name ((param1 Type1) (param2 Type2))
  (@intent "Human-readable purpose")      ; REQUIRED
  (@spec ((Type1 Type2) -> ReturnType))   ; REQUIRED
  body)

### Parameter Modes
(fn example ((in x Type)         ; Read-only (default), pass by value
             (out result Type)   ; Write-only, pointer to uninitialized
             (mut state Type))   ; Read-write, pointer to initialized
  ...)

### With Arena (for allocating functions)
(fn create-user ((arena Arena) (name String))
  (@intent "Create a new user in arena")
  (@spec ((Arena String) -> (Ptr User)))
  (@alloc arena)
  (let ((user (arena-alloc arena (sizeof User))))
    (set! user.name name)
    user))

### Impl (implementation without annotations)
(impl helper ((x Int))
  (+ x 1))

### C Name Override (for external interop)
(fn slop-parse-int ((s (Ptr Char)))
  (@intent "Parse integer from string")
  (@spec (((Ptr Char)) -> Int))
  (strtol s nil 10)
  :c-name "parse_int")    ; Emits as parse_int() in C

The :c-name attribute specifies a clean C name for external code.
Transpiler emits both the clean name and a #define alias.
""",

    'contracts': """## Contracts

Contract annotations declare what a function does, its type signature, and
the conditions it requires and guarantees. They drive type checking, verification,
example testing, and LLM hole-filling.

### Required Annotations

Every `fn` must have @intent and @spec:

(@intent "Human-readable purpose")         ; What the function does
(@spec ((ParamTypes) -> ReturnType))       ; Type signature

### Annotation Ordering

Annotations should appear in this order at the top of a function body:

(fn name ((params...))
  (@intent "...")            ; 1. Purpose
  (@spec ((...) -> ...))     ; 2. Type signature
  (@alloc arena)             ; 3. Allocation (if applicable)
  (@pure)                    ; 4. Properties
  (@trusted)                 ; 4. (or @trusted, mutually exclusive with @pure)
  (@pre ...)                 ; 5. Preconditions (zero or more)
  (@post ...)                ; 6. Postconditions (zero or more)
  (@assume ...)              ; 7. Assumptions (zero or more)
  (@example ...)             ; 8. Examples (zero or more)
  (@deprecated "...")        ; 9. Deprecation (if applicable)
  body)

### Preconditions (@pre)

(@pre condition) checks a constraint on entry. Multiple @pre are AND-ed.
Use prefix `(op ...)` or infix `{...}` syntax.

; Non-nil pointer checks
(@pre (!= ptr nil))

; Non-empty string
(@pre (> (string-len name) 0))
(@pre (> (. name len) 0))            ; Field access form

; Numeric bounds
(@pre {x >= 0.0})
(@pre {x <= 1.0})
(@pre (>= max-tokens 1))

; Field access on record params
(@pre {(. config worker-count) >= 1})
(@pre (>= (. g size) 0))

; Boolean field check
(@pre (. (deref f) is-open))

; Multiple @pre chain — all must hold
(fn clamp ((value Int) (min-val Int) (max-val Int))
  (@intent "Clamp integer to range")
  (@spec ((Int Int Int) -> Int))
  (@pre {min-val <= max-val})
  (@post {$result >= min-val})
  (@post {$result <= max-val})
  ...)

### Postconditions (@post)

(@post condition) guarantees a property of the return value.
Use $result to refer to the return value.

; Simple value constraints
(@post (!= $result nil))
(@post (>= $result 0))
(@post {$result >= min-val})

; Field access on $result (record return type)
(@post {$result.offset == 0})
(@post {$result.line == 1})
(@post {$result.count == 0})

; Relating $result fields to parameters
(@post {$result.offset == state.offset + 1})
(@post (>= $result.count pm.count))
(@post (== (. $result iteration) iteration))

; Function calls in @post — predicate on result
(@post (xml-is-element $result))
(@post (starts-with $result "?"))
(@post (graph-contains $result t))
(@post {(string-len $result) > 0})

; Match on $result — for union/Option/Result return types
(@post (match $result
         ((term-iri _) true)
         (_ false)))

(@post (match $result
         ((ok doc) (!= (. doc root) nil))
         ((error _) true)))

(@post (match $result
         ((none) true)
         ((some r) {(string-len (. r reason)) > 0})))

; Match on $result record fields containing Option
(@post (match $result.current-formula-id
         ((some id) {id == formula-id})
         ((none) false)))

; Complex multi-part postcondition
(@post
  (and
    (term-eq (triple-subject $result) subject)
    (term-eq (triple-predicate $result) predicate)
    (term-eq (triple-object $result) object)))

; Multiple @post — all must hold
(@post {$result >= 0})
(@post {$result == n or $result == (- 0 n)})

### Infix Notation

Contracts support optional infix notation with curly braces:

(@pre {x > 0})                    ; Equivalent to (@pre (> x 0))
(@pre {x >= 0 and x <= 100})      ; Equivalent to (@pre (and (>= x 0) (<= x 100)))
(@post {$result == a + b})        ; Equivalent to (@post (== $result (+ a b)))

; Precedence: *, /, % > +, - > comparisons > and > or
; Use () for grouping: {(a + b) * c}
; Function calls stay prefix inside {}: {(string-len s) > 0}

; Both styles work in the same function
(fn divide ((a Int) (b Int))
  (@intent "Divide a by b")
  (@spec ((Int Int) -> Int))
  (@pre {b != 0})                  ; Infix
  (@post (== (* $result b) a))     ; Prefix
  (/ a b))

### Function Properties

(@pure)                    ; No side effects, deterministic
(@alloc arena)             ; Allocates in specified arena
(@alloc static)            ; Returns static/global data
(@alloc none)              ; No allocation

; @pure — function produces same output for same inputs, no side effects.
; Enables verifier inlining (single-expression @pure fns are expanded).
(fn iri-eq ((a IRI) (b IRI))
  (@intent "Check if two IRIs are equal")
  (@spec ((IRI IRI) -> Bool))
  (@pure)
  (string-eq (. a value) (. b value)))

; @alloc — declares which arena the function allocates into.
(fn make-iri ((arena Arena) (value String))
  (@intent "Create an IRI term from a string")
  (@spec ((Arena String) -> Term))
  (@alloc arena)
  (@pre (> (string-len value) 0))
  ...)

### @trusted — Skip Verification

Skip Z3 verification entirely for functions that cannot be auto-verified:

(fn term-eq ((a Term) (b Term))
  (@intent "Check if two terms are equal")
  (@spec ((Term Term) -> Bool))
  (@trusted)                             ; Too complex for auto-verify
  (@pure)
  ...)

Use @trusted for:
- Complex recursive equality (nested union traversal)
- FFI wrappers with unprovable contracts
- Platform-specific implementations

### @assume — Verification Hints

(@assume condition) is an axiom the verifier trusts without proof.
Runtime still checks it.

; FFI behavior the verifier can't deduce
(fn sqrt ((x Float))
  (@intent "Compute square root")
  (@spec ((Float) -> Float))
  (@pre {x >= 0.0})
  (@assume {$result >= 0.0})
  (@pure)
  (c-inline "sqrt(x)"))

; Collection membership semantics
(@assume (implies
  (exists (t2 (. g triples)) (triple-eq t t2))
  $result))

; Field properties of result
(@assume {(. $result len) >= 1})
(@assume {(. $result data) != nil})

### @example — Executable Test Cases

(@example (args...) -> expected)

Examples serve as documentation AND executable tests. Provide multiple
examples covering normal cases, edge cases, and error paths.

`slop test` compiles each example against the module's own compiled code, so
arguments and expected values are ordinary expressions — a literal, or a call
to any function in the module or its imports. An example that cannot be
compiled (an unresolved name, or `...` in an argument) is reported as an
ERROR and fails the run; it is never counted as a pass.

; Basic: args match function params (skip arena params)
(fn abs ((n Int))
  (@intent "Return absolute value of integer")
  (@spec ((Int) -> (Int 0 ..)))
  (@pure)
  (@example (5) -> 5)
  (@example (-5) -> 5)
  (@example (0) -> 0)
  ...)

; Arena parameter — include arena in args
(fn path-dirname ((arena Arena) (path String))
  (@intent "Extract directory portion of path")
  (@spec ((Arena String) -> String))
  (@pure)
  (@example (arena "foo/bar/baz.slop") -> "foo/bar")
  (@example (arena "baz.slop") -> ".")
  (@example (arena "/") -> "/")
  ...)

; Option return types — use (some val) and none
(fn index-of ((haystack String) (needle String))
  (@intent "Find first occurrence of needle in haystack")
  (@spec ((String String) -> (Option (Int 0 ..))))
  (@pure)
  (@example ("hello world" "world") -> (some 6))
  (@example ("hello" "xyz") -> none)
  (@example ("" "a") -> none)
  ...)

; Result return types — use (ok val) and (error variant)
(fn parse-int ((s String))
  (@intent "Parse string as decimal integer")
  (@spec ((String) -> (Result I64 ParseError)))
  (@pure)
  (@example ("123") -> (ok 123))
  (@example ("-456") -> (ok -456))
  (@example ("abc") -> (error 'invalid-format))
  (@example ("") -> (error 'empty-string))
  ...)

; Union constructor returns
(@example
  ("http://example.org/foo")
  ->
  (term-iri (IRI "http://example.org/foo")))

; Calls as arguments — build whatever the function needs
(fn xml-get-attribute ((n (Ptr XmlNode)) (name String))
  (@intent "Get an attribute value by local name")
  (@spec (((Ptr XmlNode) String) -> (Option String)))
  (@example ((example-elem-with-href arena) "href") -> (some "http://example.com"))
  (@example ((example-elem-with-href arena) "missing") -> none)
  ...)
; Note the doubled parens: the outer pair is the argument list, so a single
; argument that is itself a call needs both.

; Custom equality function (for types without built-in ==)
(@example :eq triple-eq
  (arena (fixture-graph arena) (fixture-delta arena)) -> expected-triples)

; `_` means "do not compare this position" — for fields that are not
; reproducible, or that this example is not about
(@example (3) -> (some (Node 3 _)))     ; asserts presence and the first field
(@example ("bad") -> (error (ParseError "unexpected token" _)))

; A bare _ as the whole expected value asserts nothing. The call still runs, so
; a crash is caught, but the outcome is reported as RAN (no assertion) rather
; than as a pass.
(@example (arena "" "div" "") -> _)

### Deprecation

(@deprecated "message")

(fn old-api ((x Int))
  (@intent "Old API function")
  (@spec ((Int) -> Int))
  (@deprecated "use new-api instead")
  x)

; Calling deprecated functions emits a warning during type checking.

### Callback Assumptions

(@callback-assume <callback-param> <property-expr>)

; Specify properties that hold for every argument passed to a callback.
; $callback-arg refers to the callback argument value.
(fn for-each-triple ((g Graph) (callback (Fn (Triple) -> Unit)))
  (@callback-assume callback (indexed-graph-contains g $callback-arg))
  ...)

; Conditional callback assumptions
(@callback-assume callback
  (implies (!= subj (none))
    (term-eq (triple-subject $callback-arg) (unwrap subj))))

### Loop Invariants

(@loop-invariant condition) inside a loop body:

(while (and (not done) {(. state iteration) < (. config max-iterations)})
  (@loop-invariant {(. state iteration) <= (. config max-iterations)})
  ...)

### Properties

Named assertions for formal reasoning:

(@property (forall (x T) expr))

(@property novelty
  (forall (t $result) (not (graph-contains g t))))

(@property soundness
  (forall (t $result)
    (exists (dt (. delta triples))
      (and (term-eq (triple-predicate dt) pred)
           (term-eq (triple-subject t) (triple-subject dt))))))

### Full Example

(fn merge-into-graph ((arena Arena) (g IndexedGraph) (d Delta))
  (@intent "Add all triples from delta into graph")
  (@spec ((Arena IndexedGraph Delta) -> IndexedGraph))
  (@alloc arena)
  (@pre {(indexed-graph-size g) >= 0})
  (@post {(indexed-graph-size $result) >= (indexed-graph-size g)})
  (@post {(indexed-graph-size $result) <=
          (+ (indexed-graph-size g) (list-len (. d triples)))})
  ...)
""",

    'verification': """## Verification (Z3 SMT Solver)

The verifier uses Z3 to prove that functions satisfy their contracts.

### Running Verification
slop verify file.slop                   ; Verify a file
slop verify file.slop -I path -v        ; With includes, verbose

### What the Verifier Can Prove

#### 1. String Literal Lengths
(fn error-code ((arena Arena))
  (@spec ((Arena) -> String))
  (@post {(> (string-len $result) 0)})  ; PASSES: "error" has length 5
  "error")

#### 2. Pure Function Inlining
Functions marked @pure with single-expression bodies are inlined:

(fn iri-eq ((a IRI) (b IRI))
  (@pure)
  (@spec ((IRI IRI) -> Bool))
  (string-eq (. a value) (. b value)))  ; Inlined during verification

; When verifying (iri-eq x y), the verifier expands to (string-eq (. x value) (. y value))

#### 3. Postcondition Propagation
When calling a function, its postconditions become axioms:

(fn make-delta ((arena Arena) (iteration Int))
  (@spec ((Arena Int) -> (Ptr Delta)))
  (@post {(. $result iteration) == iteration})  ; Postcondition
  ...)

(fn use-delta ((arena Arena))
  (let ((d (make-delta arena 5)))
    ; Verifier knows: d.iteration == 5 (from make-delta's postcondition)
    ...))

### Function Inlining Criteria
A function is inlined if ALL of these are true:
1. Marked with @pure
2. Body is a single expression (no let, do, if, match, for-each)
3. Not recursive

### When to Use @assume
Use @assume for properties the verifier cannot deduce:

(fn count-items ((items (List Item)))
  (@spec (((List Item)) -> Int))
  (@post {(>= $result 0)})               ; Want to prove this
  (@assume {(>= (list-len items) 0)})    ; Verifier needs this hint
  (list-len items))

Common uses:
- Loop invariants: Properties preserved through iterations
- FFI properties: External function behavior
- Collection bounds: List/array length properties
- Algebraic identities: Mathematical properties

### When to Use @trusted
Skip verification entirely for functions that cannot be verified:

(fn platform-random ((arena Arena))
  (@trusted)                             ; Skip verification
  (@spec ((Arena) -> Int))
  (ffi-call "random"))

Use @trusted for:
- FFI wrappers with unprovable contracts
- Performance-critical code verified manually
- Platform-specific implementations

### Verification Limitations
The verifier CANNOT prove:
- Loop-dependent properties (use @loop-invariant)
- Quantified predicates over collections
- Complex recursive function properties
- Properties requiring induction

### Example: Fully Verified Function
(fn increment-counter ((mut counter Int))
  (@intent "Add 1 to counter, clamped to 100")
  (@spec (((Int 0 .. 100)) -> (Int 0 .. 100)))
  (@pre {(>= counter 0)})
  (@pre {(<= counter 100)})
  (@post {(>= $result counter)})         ; Result >= input
  (@post {(<= $result 100)})             ; Result <= 100
  (if (< counter 100) (+ counter 1) 100))
""",

    'holes': """## Holes (LLM Generation Points)

Holes support two modes: generation (new code) and refactoring (improve existing code).

### Generation Mode (no existing code)
(hole Type "prompt")

(hole Type "prompt"
  :complexity tier-2          ; tier-1 to tier-4
  :context (var1 fn1)         ; Whitelist of available identifiers
  :required (var1)            ; Identifiers that MUST appear in output
  :examples ((in) -> out))    ; Example behavior

### Refactoring Mode (existing code provided)
(hole Type "prompt"
  existing-code               ; Code to refactor
  :complexity tier-2)

### Complexity Tiers
tier-1: 1-3B models   ; Trivial expressions, simple arithmetic
tier-2: 7-8B models   ; Simple conditionals, basic logic
tier-3: 13-34B models ; Loops, moderate conditionals
tier-4: 70B+ models   ; Complex algorithms, multi-step logic

### Examples

; Generation: Simple hole
(hole Int "calculate the sum of x and y"
  :context (x y))

; Generation: Complex hole with constraints
(hole (List Int) "sort the input list"
  :complexity tier-3
  :context (input compare)
  :required (input)
  :examples (((list 3 1 2)) -> (list 1 2 3)))

; Refactoring: Simplify nested conditionals
(hole Bool "simplify this logic"
  (if (> x 0)
    (if (> y 0) true false)
    false)
  :complexity tier-2)
; Result: (and (> x 0) (> y 0))

### Best Practices
; Use :context to whitelist what the LLM can use
; Use :required for identifiers that MUST appear
; Match tier to actual complexity needed
; For refactoring, existing code must type-check
""",

    'memory': """## Memory Model

### Arena Allocation (Primary Pattern)
(arena-new size)                 ; Create arena with capacity
(arena-alloc arena size)         ; Allocate from arena
(arena-free arena)               ; Free entire arena

; With arena parameter
(fn process ((arena Arena) (data Input))
  (@alloc arena)
  (let ((result (arena-alloc arena (sizeof Output))))
    ...))

### Scoped Arena
(with-arena 4096
  (let ((x (arena-alloc arena size)))
    ...))  ; Arena auto-freed at end, binds 'arena'

;; Named arena - binds custom name instead of 'arena'
(with-arena :as scratch 4096
  (arena-alloc scratch 256))

;; Nested named arenas avoid shadowing
(with-arena :as output 8192
  (with-arena :as temp 4096
    (build-result output (parse temp input))))

### Pointer Types
(Ptr T)                          ; Borrowed, non-owning
(ScopedPtr T)                    ; Auto-freed on scope exit
(OptPtr T)                       ; Nullable

### Pointer Operations
(deref ptr)                      ; Dereference: (Ptr T) -> T
(addr expr)                      ; Address-of: T -> (Ptr T)
(. ptr field)                    ; Field access (auto -> vs .)

### Slices (Borrowed Views)
(Slice T)                        ; Non-owning view into array/list
(string-slice s start end)       ; Create slice from string
""",

    'ffi': """## FFI (Foreign Function Interface)

### Function Declaration
(ffi "header.h"
  (func-name ((param Type)...) ReturnType)
  (CONSTANT_NAME Type))          ; Constants: just (name Type)

; Example
(ffi "unistd.h"
  (read ((fd Int) (buf (Ptr U8)) (n U64)) I64)
  (write ((fd Int) (buf (Ptr U8)) (n U64)) I64)
  (close ((fd Int)) Int))

### Struct Declaration
(ffi-struct "header.h" struct_name
  (field1 Type1)
  (field2 Type2))

; With C name override
(ffi-struct "sys/stat.h" stat_buf :c-name "stat"
  (st_size I64)
  (st_mode U32))

; Example
(ffi-struct "netinet/in.h" sockaddr_in
  (sin_family U16)
  (sin_port U16)
  (sin_addr U32))

### C Inline Escape
(c-inline "CONSTANT")            ; Emit C constant
(c-inline "sizeof(struct foo)")  ; Emit C expression

### FFI-Only Types

#### Char
For C functions expecting `char*` (distinct from `int8_t*` and `uint8_t*`):
```lisp
(ffi "stdlib.h"
  (strtol ((s (Ptr Char)) (endptr (Ptr (Ptr Char))) (base Int)) I64))
```
Use only at FFI boundaries. For general code, use `U8` or `String`.

### Type Casting
(cast Type expr)                 ; Cast expression to Type
""",

    'builtins': """## Builtins

Language primitives that are always available without imports.

### Memory
(arena-new size) -> Arena
(arena-alloc arena size) -> (Ptr U8)
(arena-free arena) -> Unit
(with-arena size body) -> T              ; Scoped arena, binds 'arena'
(with-arena :as name size body) -> T     ; Named arena, binds 'name'

### Strings
(string-new arena cstr) -> String
(string-len s) -> (Int 0 ..)
(string-concat arena a b) -> String
(string-eq a b) -> Bool
(string-slice s start end) -> (Slice U8)
(string-split arena s delim) -> (List String)
(string-push-char arena s c) -> String             ; append a U8 char to a string
(int-to-string arena n) -> String

### Lists
(list-new arena Type) -> (List Type)
(list Type e1 e2...) -> (List Type)     ; Literal
(list-push list item) -> Unit
(list-pop list) -> (Option T)
(list-get list idx) -> (Option T)
(list-len list) -> (Int 0 ..)
(list-set list idx val) -> Unit

### Maps
(map-new arena K V) -> (Map K V)
(map K V (k1 v1)...) -> (Map K V)       ; Literal
(map-put map k v) -> Unit
(map-get map k) -> (Option V)
(map-has map k) -> Bool
(map-keys map) -> (List K)
(map-remove map k) -> Unit              ; Requires mutable map

### Results
(ok val) -> (Result T E)
(error e) -> (Result T E)
(is-ok r) -> Bool
(is-error r) -> Bool
(unwrap r) -> T                          ; Panics on error

### I/O
(print val) -> Unit                      ; Print to stdout (no newline)
(println val) -> Unit                    ; Print to stdout with newline

### Time
(now-ms) -> (Int 0 ..)
(sleep-ms ms) -> Unit
""",

    'stdlib': """## Standard Library Modules

Use `slop ref <module>` for detailed documentation, or `slop doc <path>`.

| Module    | Description                      | Import                          |
|-----------|----------------------------------|---------------------------------|
| strlib    | String manipulation              | `(import strlib (...))`         |
| mathlib   | Math functions and constants     | `(import mathlib (...))`        |
| file      | File I/O operations              | `(import file (...))`           |
| thread    | Concurrency primitives           | `(import thread (...))`         |
| env       | Environment variables            | `(import env (...))`            |
| path      | Path manipulation                | `(import path (...))`           |

### Example Usage

```lisp
(module my-app
  (import strlib (starts-with trim))
  (import file (read-file write-file))

  (fn main ()
    (@intent "Process a file")
    (@spec (() -> Int))
    ...))
```

### See Also

- `slop ref builtins` - Language primitives (always available, no import needed)
- `slop doc lib/std/<module>/<module>.slop` - Full module documentation
""",

    'expressions': """## Expressions

### Bindings
(let ((name expr)...) body)              ; Immutable
(let ((mut name expr)...) body)          ; Mutable
(let ((mut name Type expr)...) body)     ; Mutable with explicit type
(set! var value)                         ; Mutation (requires mut)

### Control Flow
(if cond then else)
(if cond then)                           ; else is Unit
(cond (test1 e1) (test2 e2) (else default))
(match expr ((pat1) body1) ((pat2) body2)...)

### Loops
(for (i start end) body)                 ; i from start to end-1
(for-each (x collection) body)           ; Iterate List/Set/Map-keys
(for-each ((k v) map) body)              ; Iterate Map key-value pairs
(while cond body)
(break)                                  ; Exit loop
(continue)                               ; Next iteration
(return expr)                            ; Early return

### Sequencing
(do e1 e2 e3...)                         ; Evaluate in order, return last

### Data Construction
(array e1 e2...)                         ; Array literal
(list Type e1 e2...)                     ; List literal
(map K V (k1 v1)...)                     ; Map literal
(record-new Type (f1 v1) (f2 v2)...)     ; Record constructor
(TypeName v1 v2...)                      ; Positional constructor

### Data Access
(. expr field)                           ; Field access
expr.field                               ; Shorthand
(@ expr idx)                             ; Index access
(put expr field val)                     ; Functional update (new copy)
(set! expr.field val)                    ; Mutation (in-place)

### Operators
(+ - * / %)                              ; Arithmetic
(== != < <= > >=)                        ; Comparison
(and or not)                             ; Boolean
(& | ^ << >> ~)                          ; Bitwise
(min a b) (max a b)                      ; Min/max

### Error Handling
(? fallible-expr)                        ; Early return on error
(try expr (catch e body))                ; Try-catch
""",

    'patterns': """## Pattern Matching

### Basic Patterns
_                           ; Wildcard (matches anything)
identifier                  ; Binding (captures value)
literal                     ; Literal match (number, string)
'symbol                     ; Quoted symbol (for enum variants)

### Enum Matching (IMPORTANT: use quotes)
(match status
  ('active ...)             ; Quote the variant
  ('inactive ...)
  (_ ...))                  ; Wildcard for default

### Structured Patterns
(array p1 p2...)           ; Array destructuring
(list p1 p2... | rest)     ; List with rest binding
(record Type (f1 p1)...)   ; Record destructuring
(union Tag pat)            ; Union variant matching

### Guarded Patterns
(guard pat when expr)      ; Pattern with condition

; Example
(match value
  ((guard n when (> n 0)) (handle-positive n))
  ((guard n when (< n 0)) (handle-negative n))
  (0 (handle-zero)))

### Result/Option Matching
(match result
  ((ok val) (use val))
  ((error e) (handle e)))

(match option
  ((some x) (use x))
  ((none) (default)))

### Exhaustiveness
All variants must be covered, or use wildcard (_).
Type checker enforces exhaustive matching.
""",

    'mistakes': """## Common Mistakes

These DO NOT exist in SLOP - use the alternatives:

| Don't Use | Use Instead |
|-----------|-------------|
| `print-int n` | `(println (int-to-string arena n))` |
| `print-float n` | `(println (float-to-string arena n))` |
| `(println enum-value)` | Use `match` to print different strings |
| `arena` outside with-arena | Wrap code in `(with-arena size ...)` |
| `(block ...)` | `(do ...)` for sequencing |
| `(begin ...)` | `(do ...)` for sequencing |
| `strlen s` | `(string-len s)` |
| `malloc` | `(arena-alloc arena size)` |
| `list.length` | `(list-len list)` |
| `list-append` | `(list-push list elem)` |
| `map-set` | `(map-put map key val)` |
| `hash-get` | `(map-get map key)` |
| Deeply nested `(or (or ...))` | `(cond ...)` for multi-way conditionals |
| Nested `(string-concat ...)` | `(string-build arena ...)` from strlib |
| Definitions outside module | All `(type)`, `(fn)`, `(const)` inside `(module ...)` |

### Module Structure

All definitions must be INSIDE the module form:

; CORRECT:
(module my-module
  (export public-fn)

  (type MyType (Int 0 ..))

  (fn public-fn (...)
    ...))  ; <-- closing paren wraps entire module

; WRONG:
(module my-module
  (export public-fn))

(fn public-fn ...)  ; ERROR: outside module form

### Error Returns

IMPORTANT: Quote error variants!

(error 'not-found)     ; CORRECT: quoted
(error not-found)      ; WRONG: undefined variable

### Builtin vs Library Functions

These string/list functions are BUILTINS - do NOT import from strlib:

| Builtin (no import) | What it does |
|---------------------|--------------|
| `(string-len s)` | Get string length |
| `(string-concat arena a b)` | Concatenate strings |
| `(string-eq a b)` | Compare strings |
| `(string-new arena cstr)` | Create string from C string |
| `(string-slice s start end)` | Get substring slice |
| `(string-split arena s delim)` | Split string |
| `(int-to-string arena n)` | Convert int to string |
| `(list-len list)` | Get list length |
| `(list-get list idx)` | Get element at index |
| `(list-push list item)` | Append to list |

These ARE in strlib and need `(import strlib ...)`:

| strlib function | What it does |
|-----------------|--------------|
| `starts-with`, `ends-with` | String prefix/suffix check |
| `contains`, `index-of` | Substring search |
| `trim`, `trim-start`, `trim-end` | Whitespace removal |
| `substring`, `replace`, `replace-all` | String manipulation |
| `to-upper`, `to-lower`, `capitalize` | Case conversion |
| `parse-int`, `parse-float` | String to number |
| `float-to-string` | Float to string |
| `compare`, `compare-ignore-case` | String comparison |
| `join`, `string-build`, `reverse`, `repeat` | Advanced operations |
| `fill-bytes` | Fill memory region with byte value |
""",

    'cli': """## CLI Reference

### Commands

| Command | Description |
|---------|-------------|
| `slop parse FILE` | Parse and display AST |
| `slop check FILE` | Type check without transpiling |
| `slop transpile FILE` | Convert to C source |
| `slop build FILE` | Full pipeline: parse, check, transpile, compile |
| `slop fill FILE` | Fill holes with LLM-generated code |
| `slop verify FILE` | Verify contracts with Z3 |
| `slop ref [TOPIC]` | Show language reference |
| `slop doc FILE` | Generate documentation |

### Native Components (default)

SLOP includes self-hosted compiler components written in SLOP. **Native tools are used by default.** Use `--python` to fall back to Python implementations:

```bash
slop parse FILE               # Uses native parser (default)
slop check FILE               # Uses native type checker (default)
slop build FILE               # Uses native parser + transpiler (default)

slop parse FILE --python      # Use Python parser
slop check FILE --python      # Use Python type checker
slop build FILE --python      # Use Python toolchain
```

Native components are in `lib/compiler/`:
- `slop-parser` - S-expression parser (outputs JSON AST)
- `slop-checker` - Type checker with diagnostics
- `slop-transpiler` - SLOP to C transpiler

If a native component isn't found, automatically falls back to Python.

### Common Options

| Option | Commands | Description |
|--------|----------|-------------|
| `-o, --output` | transpile, build | Output file path |
| `-I, --include` | transpile, build | Add module search path |
| `--python` | parse, check, build | Use Python fallback |
| `--debug` | build | Include debug symbols |
| `--holes` | parse | Show only holes |
| `-v, --verbose` | fill, verify | Increase verbosity |

### Build Configuration

With `slop.toml`, commands use project settings:

```bash
slop build                    # Uses [project].entry, native tools
slop build --python           # Python toolchain + config
slop fill                     # Uses entry from config
```

See `slop.toml.example` for configuration options.
""",
}

# Ordered list of topics for display
TOPIC_ORDER = [
    'types',
    'functions',
    'contracts',
    'verification',
    'holes',
    'memory',
    'ffi',
    'builtins',
    'stdlib',
    'expressions',
    'patterns',
    'mistakes',
    'cli',
]


def list_topics() -> list:
    """Return list of available topics in display order."""
    return TOPIC_ORDER


def get_reference(topic: str = 'all') -> str:
    """Get reference content for a topic or all topics.

    Args:
        topic: Topic name or 'all' for full reference

    Returns:
        Reference content as string
    """
    if topic == 'all':
        sections = []
        for t in TOPIC_ORDER:
            sections.append(TOPICS[t])
        return '\n\n'.join(sections)

    if topic in TOPICS:
        return TOPICS[topic]

    return f"Unknown topic: {topic}\nAvailable: {', '.join(TOPIC_ORDER)}"
