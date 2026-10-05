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
(Float) (F32) (F64)     ; double / float / double
(Bool)                  ; Boolean
(String)                ; slop_string
(Bytes)                 ; Byte buffer
(Unit)                  ; void / no value

### Range Types
(Int min ..)            ; >= min
(Int .. max)            ; <= max
(Int min .. max)        ; Bounded range; (Int 0..9) also reads as a range
(String min .. max)     ; Length-bounded string (accepted, not enforced yet)
(Float min .. max)      ; Bounded float (accepted, not enforced yet)
; Only (Int ...) ranges are enforced. A range over any other base type is
; accepted with a warning. Bounds must be integer literals: (Int 0 .. MAX),
; (Int 0 127) and an empty (Int 5 .. 3) are errors.

; Examples
(type UserId (Int 1 ..))
(type Age (Int 0 .. 150))
(type Port (Int 1 .. 65535))
(type Digit (Int 0..9))

; Bounds are integer literals. A literal, constant, or arithmetic on them that
; flows outside a range -- an argument, return, typed let, set!, record field,
; container element or cast -- is a checker error; a value whose interval can
; never fit is a warning. Anything else is checked at run time, at full width
; before it is stored, in every build; slop build --no-range-checks (or
; no_range_checks = true under [build] in slop.toml) removes the checks (a value
; outside its range is then undefined). A failed check aborts with
;   SLOP range check failed: 130 is not in Pct (Int 0 .. 100) at r.slop:7:5
; Widening into a larger range is free. Each range type also gets a C
; constructor, TypeName_new(v), that checks.
; C mapping: (Int 0 .. 255) -> uint8_t

### Collections
(List T)                ; Dynamic array
(List T n)              ; Exactly n elements
(List T min ..)         ; At least min (not enforced yet)
(Array T n)             ; Fixed-size, stack-allocated
(Map K V)               ; Hash map
(Set T)                 ; Hash set

; Literals: the element type is required and never inferred
(list Int 1 2 3)                    ; (List Int)
(set String "a" "b")                ; (Set String)
(list Int 1 2 3 :arena a)           ; built in arena a
; A literal is built in the arena in scope: arena, else the only Arena
; variable in scope; with several, name one with :arena. No arena in scope is
; an error. There is no map literal: map-new, then map-put.

### Algebraic Types
(type Status (enum pending active done))
(type User (record (id Int) (name String)))
(type Shape (union (circle Float) (rect Float Float) (point)))

; Building a union value
(union-new Shape circle 2.0)
(Shape (rect 2.0 3.0))
(Shape point)                       ; variant with no payload
; (Shape circle 2.0) and a bare (circle 2.0) are errors.

Note: Variant names must be globally unique across all enum and union types
in a module. Using the same variant name in different types causes a compile error.

Recursive unions: A variant cannot embed its parent union by value (infinite-size
struct). Use (Ptr T) or (List T) for self-referencing variants:
  (bad-node Tree)           ; ERROR — direct self-ref, infinite size
  (bad (Option Tree))       ; ERROR — Option embeds T by value
  (ok-children (List Tree)) ; OK — List is fixed-size (pointer to data)
  (ok-next (Ptr Tree))      ; OK — pointer is fixed size

### Pointers
(Ptr T)                 ; Borrowed pointer (T*); may be nil
(ScopedPtr T)           ; Scoped, auto-freed on scope exit

### Utility Types
(Option T)              ; T or none
(Result T E)            ; Success or error
(Fn (A B) -> R)         ; Function pointer

### Concurrency Types (thread library)
(Chan T)                ; Typed channel
(Thread T)              ; Thread handle returning T

### Type Aliases
(type UserId (Int 1 ..))
(type Handler (Fn (Request) -> Response))
(type Ids (Map String Int))              ; interchangeable with (Map String Int)

### Constants
(const MAX_CONN Int 128)                 ; integer -> #define
(const GREETING String "hi\n")           ; other types -> static const; escaped like a literal
(const PRIMES (List Int) (list Int 2 3 5))
; A module-level list constant needs literal elements and has no arena.
""",

    'functions': """## Functions

### Basic Structure
(fn name ((param1 Type1) (param2 Type2))
  (@intent "Human-readable purpose")      ; REQUIRED
  (@spec ((Type1 Type2) -> ReturnType))   ; REQUIRED
  body)

### Parameter Modes
(fn example ((x Type)            ; Read-only (default; `in` is the same)
             (mut state Type)    ; Mutable local copy of a value type
             (out-p (Ptr T)))    ; Change the caller's value: caller passes (addr v)
  ...)
- Unmarked: reassigning it, setting its fields, or list-push/list-pop on it or a
  List field of it is an error -- the change would be lost to the caller.
  Map/Set contents, list-set elements, and writes through a Ptr are allowed.
- mut: the caller never sees the change (functional update: change, return).
  Not allowed on List/Map/Set parameters, whose copies share storage.
- There is no `out` mode: use a (Ptr T) parameter. No other word may sit in
  first position of a 3-element parameter.
- let bindings without mut, and for/for-each/match/with-arena names, cannot be set!.
  Pushing onto an immutable let's own list is fine.
- A for-each or match binding is a copy of the element or payload: list-push or
  list-pop on it, or on a List field of it, is an error (the change would be lost).
  Grow a (let ((mut c x))) copy and write it back (list-set, map-put), or hold
  elements as (Ptr T).

; Change the caller's list through a pointer
(fn add-one ((ys (Ptr (List Int))))
  (@intent "Append 1 to the caller's list")
  (@spec (((Ptr (List Int))) -> Unit))
  (list-push (deref ys) 1))
; caller: (add-one (addr ys))

### Lambdas and Captures
(fn ((x Int)) (+ x n))           ; a lambda; uses n from the enclosing scope
- An immutable binding is captured by value (a copy made where the lambda is
  created); a mut local or parameter is captured by reference.
- A lambda passed to spawn / spawn-closure / spawn-with-chan must not capture a
  mut variable (compile error): bind an immutable copy and capture that:
    (let ((share part)) (spawn arena (fn () (work share))))
- A capturing lambda's environment is allocated in the arena in scope; name
  one with (let ((arena a)) (fn ...)).

### Generic Functions
(fn choose ((a T) (b T) (first Bool))
  (@intent "Pick one of two values of the same type")
  (@generic (T))
  (@spec ((T T Bool) -> T))
  (if first a b))
; At a call the checker binds T from the arguments: (choose 1 2 true) is an Int.

### With Arena (for allocating functions)
(fn create-user ((arena Arena) (name String))
  (@intent "Create a new user in arena")
  (@spec ((Arena String) -> (Ptr User)))
  (@alloc arena)
  (let ((user (arena-alloc arena (sizeof User))))
    (set! user.name name)
    user))

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

(@doc "...") attaches longer documentation; module-level @intent/@doc describe a module.

### When Contracts Run
@pre, @post and @assume are compiled into runtime checks only in debug builds
(slop build --debug, which defines SLOP_DEBUG). A normal build compiles them
out; slop verify proves them statically. @example is checked by slop test.

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
A --debug build still checks it at run time.

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

A record, union, Option or Result result is compared structurally, so write
its expected value as a constructor — `(record-new R (f v) ...)`, `(R v ...)`,
a variant, `(some ...)`, `(ok ...)` — or name an equality function:
`(@example :eq r-eq (3) -> (make-r 3))` calls `(r-eq result expected)`.
For a List result, `:eq` compares element by element.

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
  (implies (is-some subj)
    (term-eq (triple-subject $callback-arg) (unwrap subj))))

### Loop Invariants

(@loop-invariant condition) as the first form(s) of a loop body. The verifier
proves it - it must hold where the loop starts and every iteration must keep
it - and only then assumes it where the loop ends. A failure reports
"loop invariant not established on entry" or "not preserved"; an invariant
the check cannot follow reports "could not check loop invariant" and is not
assumed.

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
slop verify file.slop --mode warn       ; Report failures as warnings (default: error)
slop verify file.slop --timeout 10000   ; Per-check Z3 timeout in ms (default 5000)

### What the Verifier Proves
- @post on every return path, using @pre and the callee contracts it can see.
- Range return types: a function returning (Int 0 .. 100) must provably stay
  in range ("return value within Pct (Int 0 .. 100)"). Parameter, field and
  callee ranges are assumed.
- Loop invariants: (@loop-invariant ...) is proved on entry and preserved by
  each iteration before it is used. In a for-each, (list-visited xs) names the
  prefix already visited, for completeness claims.

#### String literal lengths
(fn error-code ((arena Arena))
  (@intent "An error code")
  (@spec ((Arena) -> String))
  (@post {(string-len $result) > 0})    ; PASSES: "error" has length 5
  "error")

#### Pure function inlining
Functions marked @pure with single-expression bodies are inlined:

(fn iri-eq ((a IRI) (b IRI))
  (@intent "IRIs are equal")
  (@spec ((IRI IRI) -> Bool))
  (@pure)
  (string-eq (. a value) (. b value)))  ; Inlined during verification

#### Postcondition propagation
When calling a function, its postconditions become facts at the call:

(fn make-delta ((arena Arena) (iteration Int))
  (@intent "A delta for an iteration")
  (@spec ((Arena Int) -> (Ptr Delta)))
  (@post {(. $result iteration) == iteration})
  ...)
; After (let ((d (make-delta arena 5))) ...) the verifier knows d.iteration == 5.

### Function Inlining Criteria
A function is inlined if ALL of these are true:
1. Marked with @pure
2. Body is a single expression (no let, do, if, match, for-each)
3. Not recursive

### When to Use @assume
Use @assume for a fact the verifier cannot deduce and you vouch for:

(fn count-items ((items (List Item)))
  (@intent "Count the items")
  (@spec (((List Item)) -> Int))
  (@assume {(list-len items) >= 0})     ; Verifier needs this hint
  (@post {$result >= 0})
  (list-len items))

Common uses: FFI behaviour, collection bounds, algebraic identities. For
loops, write a @loop-invariant, which is proved rather than assumed.

### When to Use @trusted
Skip verification entirely for functions that cannot be verified:

(fn platform-random ((arena Arena))
  (@intent "A random number from the platform")
  (@spec ((Arena) -> Int))
  (@trusted)                             ; Skip verification
  (c-random))

Use @trusted for FFI wrappers with unprovable contracts and
platform-specific code.

### Verification Limitations
The verifier CANNOT prove:
- Quantified predicates over collections without an invariant
- Complex recursive function properties
- Properties requiring induction

### Example: Fully Verified Function
(fn increment-counter ((counter (Int 0 .. 100)))
  (@intent "Add 1 to counter, clamped to 100")
  (@spec (((Int 0 .. 100)) -> (Int 0 .. 100)))
  (@post {$result >= counter})           ; Result >= input
  (@post {$result <= 100})               ; Result <= 100
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
  :constraints (expr...)      ; Conditions the result must satisfy
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
  :examples (((list Int 3 1 2)) -> (list Int 1 2 3)))

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

The arena is freed on every exit from the block, including when its value is
the function's return value, on (return x), and on a (break) or (continue)
that leaves it (only arenas opened inside the loop being left are freed).
What leaves the block must not point into its arena: return a scalar, or build
the result in an arena that outlives the block (usually a caller's Arena
parameter). The compiler does not yet reject returning arena data.
(break)/(continue) outside a loop, including inside a lambda written in a
loop, is an error: "break outside a loop".

;; Named arena - binds custom name instead of 'arena'
(with-arena :as scratch 4096
  (arena-alloc scratch 256))

;; Nested named arenas avoid shadowing
(with-arena :as output 8192
  (with-arena :as temp 4096
    (build-result output (parse temp input))))

### Collections and Arenas
A List, Map or Set records the arena it was created in, and every push or put
grows it there, wherever the push happens. To grow into another arena for one
call: (list-push xs v :arena a), (map-put m k v :arena a), (set-put s v :arena a).
Literals, map-keys, set-elements and lambda environments use the arena in
scope: a variable named arena, else the only Arena variable in scope. With
several in scope and none named arena it is an error; pass :arena a, or bind
(let ((arena a)) ...).

### Arena Cap
All arenas together are capped at 256 MB by default; past it, allocation aborts.
slop build --arena-cap BYTES or arena_cap = N in slop.toml changes it;
--no-arena-cap / no_arena_cap = true removes it.

### Pointer Types
(Ptr T)                          ; Borrowed, non-owning; may be nil
(ScopedPtr T)                    ; Auto-freed on scope exit

### Pointer Operations
(deref ptr)                      ; Dereference: (Ptr T) -> T
(addr expr)                      ; Address-of: T -> (Ptr T)
(. ptr field)                    ; Field access (auto -> vs .)

; There is no Slice type; use (List T), or a (Ptr T) plus a length.
; For strings use strlib's substring.
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

### Variadic Functions
(ffi "stdio.h"
  (printf ((fmt (Ptr Char))) Int :variadic))   ; extra arguments allowed

### Linking
slop build app.slop -o app -lssl -lcrypto      ; -l flags on the command line
; or in slop.toml:  [build.link]  libraries = ["ssl", "crypto"]

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
(arena-alloc arena (sizeof T)) -> (Ptr T) ; also (arena-alloc arena T)
(arena-free arena) -> Unit
(with-arena size body) -> T              ; Scoped arena, binds 'arena'
(with-arena :as name size body) -> T     ; Named arena, binds 'name'

### Strings
(string-new arena cstr) -> String
(string-len s) -> (Int 0 ..)
(string-concat arena a b) -> String
(string-eq a b) -> Bool
(string-push-char arena s c) -> String             ; append a U8 char to a string
(int-to-string arena n) -> String

### Lists
(list-new arena Type) -> (List Type)   ; The list grows in arena
(list Type e1 e2...) -> (List Type)     ; Literal, built in the arena in scope (error if none)
                                        ; A module-level const list needs literal elements
(list Type e1 e2... :arena a)           ; Literal built in a
(list-push list item) -> Unit           ; Grows in the list's own arena
(list-push list item :arena a) -> Unit  ; Grows in a for this push
(list-pop list) -> (Option T)
(list-get list idx) -> (Option T)
(list-set list idx value) -> Bool       ; Overwrite in place; false if out of range
(list-len list) -> (Int 0 ..)

### Maps
(map-new arena K V) -> (Map K V)        ; Type parameters required
(map-put map k v) -> Unit               ; Grows in the map's own arena
(map-put map k v :arena a) -> Unit      ; Grows in a for this put
(map-get map k) -> (Option V)
(map-has map k) -> Bool
(map-keys map) -> (List K)              ; Built in the arena in scope
(map-keys map :arena a) -> (List K)     ; Built in a
(map-remove map k) -> Unit              ; Requires mutable map
(map-len map) -> (Int 0 ..)             ; Entry count, O(1)

There is no map literal. A Map or Set is a handle: copies share one table.
map-put copies the key and value in; map-get and for-each copy them out.
Iteration order is deterministic but unspecified; do not change a map
inside a for-each over it. A put grows the table in the arena map-new was
given, unless it names another with :arena. Only one thread may allocate from
an arena at a time: a thread growing a collection whose arena another thread
uses names its own.

The arena in scope (for literals, map-keys, set-elements and a capturing
lambda's environment) is the variable named `arena`, else the one Arena
variable in scope. Two or more with none named `arena` is an error: name it
with :arena, or for a lambda bind it, (let ((arena a)) (fn ...)).

### Sets
(set-new arena T) -> (Set T)            ; Type parameter required
(set T e1 e2...) -> (Set T)             ; Literal, built in the arena in scope
(set T e1 e2... :arena a)               ; Literal built in a
(set-put set e) -> Unit                 ; Grows in the set's own arena
(set-put set e :arena a) -> Unit        ; Grows in a for this put
(set-has set e) -> Bool
(set-remove set e) -> Unit
(set-elements set) -> (List T)          ; Built in the arena in scope
(set-elements set :arena a) -> (List T) ; Built in a
(set-len set) -> (Int 0 ..)             ; Element count, O(1)

### Options
(some val) -> (Option T)
(none) -> (Option T)
(is-some opt) -> Bool                   ; Does it hold a value?
(is-none opt) -> Bool                   ; Is it empty?

is-some/is-none read the tag only, never the payload, so they work for any T.
Use match when you need the value. == on an (Option T) is an error -- it is a
container, like (List T).

Both names are reserved, like every other builtin. Every builtin is lowered by
name -- the transpiler decides what a call means from the head symbol, before it
consults the function registry -- so a definition could never take effect.
Defining a function, type, FFI function or ffi-struct called list-len, map-get,
record-new, with-arena or any other builtin is a compile error. Library
functions such as starts-with or substring are ordinary functions and are not
reserved.

(unwrap opt) -> T                       ; Option only; aborts on none in --debug builds

### Results
(ok val) -> (Result T E)
(error e) -> (Result T E)
(? r)                                    ; Early-return the error, else the ok value
; Inspect a Result with match.

### I/O
(print val) -> Unit                      ; Print to stdout (no newline)
(println val) -> Unit                    ; Print to stdout with newline
; val may be a String, Int, Bool or Float.

### Time
(now-ms) -> (Int 0 ..)
(sleep-ms ms) -> Unit

### Other Forms the Compiler Lowers
(record-new T (f v)...)  (union-new T tag v...)   ; construction
(when cond body...)                      ; if without else, runs several forms
(let* ((a e1) (b e2)) body)              ; sequential bindings
(sizeof T) -> U64
(quote x) / 'x                           ; quoted symbol (enum value)
(& a b) (| a b) (^ a b) (<< a n) (>> a n)   ; bitwise

### Threads (import thread)
(import thread (chan chan-buffered chan-close send recv try-recv spawn join))
(chan T arena) -> (Ptr (Chan T))                 ; unbuffered
(chan-buffered T arena cap) -> (Ptr (Chan T))
(send ch v) -> (Result Unit ChanError)
(recv ch) -> (Result T ChanError)                ; blocks; error once closed and empty
(try-recv ch) -> (Result T ChanError)            ; never blocks
(chan-close ch) -> Unit
(spawn arena (fn () ...)) -> (Ptr (Thread T))    ; also spawn-closure, spawn-with-chan
(join t) -> T
; spawn aborts with "SLOP: spawn: cannot start a thread" if the thread cannot
; be created; join aborts likewise. A spawned lambda that captures a mut
; variable is a compile error: capture an immutable copy.
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
| json      | JSON parse and emit              | `(import json (...))`           |
| xml       | XML parse and emit               | `(import xml (...))`            |

strlib works on a String's len, never a terminating NUL: compare (-1/0/1) is
bytewise then shorter-first, and parse-int/parse-float read only the String.

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

A call resolves within the calling module: a local binding, then the module's
own function or FFI declaration, then what it imports, then a builtin. Another
module's function is callable only if it is imported. Two errors follow from
this: a name imported from two modules, and a name that is both defined in the
module and imported into it.

Type names, type aliases and enum or union variants resolve the same way: the
module's own, then what it imports, then builtins. Two modules may each define
a `Pt` or a `red`. What a module gets is decided by what it imports, never by
build order. A variant in a `match` arm is taken from the scrutinee's type,
and a quoted variant the module can't see from the type expected where it
appears (a parameter, field, typed let or return type). Any other name that
reaches a module without an import is accepted only if exactly one module in
the build defines it; otherwise the error asks you to import the one you mean.

Module names are global within a build: two files that declare the same
module name are an error naming both files.

### See Also

- `slop ref builtins` - Language primitives (always available, no import needed)
- `slop doc <module>` - Full module documentation; files live under lib/std/
  (strlib/strlib.slop, io/file.slop, math/mathlib.slop, os/env.slop, path/path.slop,
  thread/thread.slop, json/json.slop, xml/xml.slop)
""",

    'expressions': """## Expressions

### Literals
42  -7                                   ; Int
3.14  1.5e-3  2E10                       ; Float: a dot or an exponent
"text"                                   ; String; escapes \\n \\t \\r \\" \\\\
'red                                     ; Quoted symbol (enum value)
true false nil unit
; A number must be followed by a space or delimiter: 3.14f, 1. and 0x1F are
; parse errors. (Int 0..9) is fine: .. after a number is a range.

### Bindings
(let ((name expr)...) body)              ; Immutable
(let ((name Type expr)...) body)         ; Immutable with explicit type
(let ((mut name expr)...) body)          ; Mutable
(let ((mut name Type expr)...) body)     ; Mutable with explicit type
(let* ((a e1) (b e2)) body)              ; Sequential bindings
(set! var value)                         ; Mutation (requires mut)
(set! expr field value)                  ; Field mutation (in place)
(set! expr.field value)                  ; Same, shorthand

### Control Flow
(if cond then else)                      ; At most three operands
(if cond then)                           ; else is Unit
(when cond body...)                      ; if without else, several forms
(cond (test1 e1...) (test2 e2...) (else default))
(match expr ((pat1) body1) ((pat2) body2)...)
; A cond or match whose value is used and that no clause covers aborts at
; run time; every form of a multi-form clause or arm runs.

### Loops
(for (i start end) body)                 ; i from start to end-1
(for-each (x collection) body)           ; Iterate List/Set/Map-keys
(for-each ((k v) map) body)              ; Iterate Map key-value pairs
(while cond body)
(break)                                  ; Leave the innermost loop (frees its arenas)
(continue)                               ; Next iteration of the innermost loop
(return expr)                            ; Early return
; break/continue outside a loop is an error.

### Sequencing
(do e1 e2 e3...)                         ; Evaluate in order, return last

### Data Construction
(list Type e1 e2...)                     ; List literal (needs an arena in scope)
(set Type e1 e2...)                      ; Set literal
(record-new Type (f1 v1) (f2 v2)...)     ; Record constructor
(TypeName v1 v2...)                      ; Positional record constructor
(union-new Type tag v1 v2...)            ; Union value
(Type (tag v1 v2...))                    ; Union value, by type name
(Type tag)                               ; Union variant with no payload
; (Type tag v) and a bare (tag v) are errors; every payload is required.
(some v)  none  (ok v)  (error e)        ; Option and Result

### Data Access
(. expr field)                           ; Field access (auto -> vs .)
expr.field                               ; Shorthand
(@ expr idx)                             ; Index access
(deref ptr)  (addr expr)                 ; Pointers
(cast Type expr)                         ; Conversion

### Operators
(+ - * / %)                              ; Arithmetic
(== != < <= > >=)                        ; Comparison: exactly two operands
(and or not)                             ; Boolean
(& a b) (| a b) (^ a b) (<< a n) (>> a n) ; Bitwise; for NOT use (^ a -1)
(min a b) (max a b)                      ; Min/max
; Chain comparisons with and: (and (< a b) (< b c)); (< a b c) is an error.

Arithmetic operands must be numeric. Integer widths, range types and their
aliases mix and give Int; a Float/F32/F64 operand gives the widest floating
type present. % is integer-only. Bool, Char, enums, records and String are
rejected. There is no pointer arithmetic: write (cast (Ptr T) (+ (cast Int p) n)).

== and != are structural: String compares by contents, a record compares
field by field, a union compares its tag then the payloads of the matching
variant. Both recurse into nested records and unions. A (Ptr T) compares by
identity, as in C.

Two caveats. A container field -- (List T), (Map K V), (Set T), (Option T),
(Result T E) -- inside a record is compared by identity rather than contents;
the transpiler warns and names the field. And == on a container itself is a
transpiler error: match on the variants, or compare the fields you mean.

### Error Handling
(? fallible-expr)                        ; Early return on error
; Handle an error in place with match on the Result.
""",

    'patterns': """## Pattern Matching

### Basic Patterns
_  else                     ; Wildcard (matches anything)
identifier                  ; Binding (captures value)
literal                     ; Literal match (number, string)
'symbol                     ; Quoted symbol (for enum variants)

### Enum Matching (IMPORTANT: use quotes)
(match status
  ('active ...)             ; Quote the variant
  ('inactive ...)
  (_ ...))                  ; Wildcard for default
; ((active) ...) on an enum variant is an error: it has no payload.

### String Matching (compares by value)
(match token
  ("U64" 64)
  ("U32" 32)
  (_ 0))                    ; Wildcard for default

### Union Matching
(match shape
  ((circle r) (* 3.14 (* r r)))
  ((rect w h) (* w h))      ; one name (or _) per payload
  ((point) 0.0))
(match tok
  ((word "if") 'keyword)    ; a string literal in a payload position
  ((word _) 'identifier))
; A pattern with more names than the variant has payloads, or a variant the
; type does not have, is an error. Bound names are copies: no list-push or
; list-pop on them.

### Result/Option Matching
(match result
  ((ok val) (use val))
  ((error e) (handle e)))

(match option
  ((some x) (use x))
  ((none) (default)))

### Exhaustiveness
All variants must be covered, or use wildcard (_).
The checker warns about a non-exhaustive match.
Literal arms over Int or String need a wildcard. A match whose value is used
aborts ("non-exhaustive match reached") on a value no arm covers.
""",

    'mistakes': """## Common Mistakes

These DO NOT exist in SLOP - use the alternatives:

| Don't Use | Use Instead |
|-----------|-------------|
| `print-int n` | `(println n)` -- println takes an Int, Bool or Float directly |
| `print-float n` | `(println x)`, or `(float-to-string arena x precision)` from strlib |
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
| `(== opt (none))` | `(is-none opt)` -- `==` on an Option is an error |
| `(!= opt (none))` | `(is-some opt)` |
| Deeply nested `(or (or ...))` | `(cond ...)` for multi-way conditionals |
| Nested `(string-concat ...)` | `(string-build arena (list String a b c))` from strlib |
| Definitions outside module | All `(type)`, `(fn)`, `(const)` inside `(module ...)` |
| `(list 1 2 3)` | `(list Int 1 2 3)` -- the element type is required |
| `(map ...)` literal | `(map-new arena K V)` then `map-put` |
| `(Shape circle 5.0)` / `(circle 5.0)` | `(Shape (circle 5.0))` or `(union-new Shape circle 5.0)` |
| `(if c a b d)` | `(if c (do a b) d)` -- at most three operands |
| `(< a b c)` | `(and (< a b) (< b c))` |
| `3.14f`, `1.` | `3.14`, `1.0` |
| `~x` | `(^ x -1)` -- there is no ~ |
| `(is-ok r)`, `(unwrap result)` | `(match r ((ok v) ...) ((error e) ...))` |
| `(put r f v)` | `(let ((mut c r)) (set! c f v) c)` |
| `(try e (catch ...))` | `match` on the Result, or `(? e)` |
| `(list-push x v)` on a for-each/match binding | grow a `(let ((mut c x)))` copy and write it back, or use `(Ptr T)` elements |
| a `mut` variable captured by a spawned lambda | `(let ((share v)) (spawn arena (fn () ... share ...)))` |
| `(break)` outside a loop | `(return ...)`, or restructure the loop |

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
| `(int-to-string arena n)` | Convert int to string |
| `(list-len list)` | Get list length |
| `(list-get list idx)` | Get element at index |
| `(list-set list idx value)` | Overwrite element at index |
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
| `slop parse FILE [--holes]` | Parse and print the S-expressions (or only the holes) |
| `slop check FILE [--json] [-I DIR]` | Type check without transpiling |
| `slop transpile FILE [-o OUT] [-I DIR]` | Convert to C source |
| `slop build [FILE]` | Full pipeline: parse, check, transpile, compile |
| `slop test [FILE] [-I DIR] [-v] [--rebuild]` | Run the @example annotations |
| `slop verify [FILE] [--mode error/warn] [--timeout MS]` | Prove contracts with Z3 |
| `slop fill [FILE]` | Fill holes with LLM-generated code |
| `slop check-hole EXPR -t TYPE` | Check an expression against an expected type |
| `slop format FILE... [--stdout] [--check]` | Format source in place (comments kept) |
| `slop doc FILE [-f markdown/json] [-o OUT]` | Generate documentation |
| `slop derive SCHEMA [-f FORMAT] [-s MODE] [-o OUT]` | Generate SLOP types from JSON Schema, SQL or OpenAPI |
| `slop ref [TOPIC] [--list]` | Show this language reference |
| `slop paths [-v]` | Show SLOP_HOME, the native binaries and stdlib paths |

### Native Toolchain
Parsing, checking and transpiling run on the native, self-hosted tools in
bin/: slop-parser, slop-checker, slop-compiler (checker + transpiler) and
slop-tester. Build them with `make build-native`. Without them, check, build
and transpile stop with "Native SLOP compiler not found"; only parse falls back
to the Python parser.

### build Options
| Option | Description |
|--------|-------------|
| `-o, --output` | Output binary or library path |
| `-c, --config` | slop.toml to use |
| `-I, --include` | Add a module search path |
| `--debug` | Debug symbols, and SLOP_DEBUG: @pre/@post/@assume checked at run time |
| `-O {0,1,2,3,s}` | C optimization level (default 2) |
| `--arena-cap N` / `--no-arena-cap` | Cap all arenas at N bytes (default 256MB) / no cap |
| `--no-range-checks` | Compile out run-time range checks |
| `--library {static,shared}` | Build a library instead of an executable |
| `--skip-check` | Skip type checking (bootstrapping only) |
| `-lNAME` | Link a C library |

### fill Options
`-o OUT`, `--stdout`, `-c CONFIG`, `-v`/`-vv`, `-q`, `-p` (parallel),
`--max-workers N`, `--batch-interactive`, `-I DIR`.

### Build Configuration

With `slop.toml`, commands use project settings:

```bash
slop build                    # Uses [project].entry
slop fill                     # Uses entry from config
slop test                     # Uses [test] settings
```

[build] keys include no_range_checks, arena_cap and no_arena_cap; [build.link]
libraries lists C libraries. See `slop.toml.example`.
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
