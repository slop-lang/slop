# SLOP Verification Guide

Practical guide to the SLOP contract verifier. For annotation syntax, see `REFERENCE.md`. For the full language specification, see `LANGUAGE.md`.

## 1. Overview

`slop verify` uses Z3 (an SMT solver) to prove that function implementations satisfy their contracts. The verification pipeline is:

```
SLOP source → parse → type check → contract verification (Z3) + range verification
```

The verifier checks:

- **@post** — postconditions hold given preconditions
- **@property** — named properties hold universally
- **@invariant** — type invariants maintained across construction and use
- **Range types** — bounds propagated through arithmetic
- **Record field axioms** — `(record-new Type (field value))` implies `(. $result field) == value`

Each function is verified independently. The verifier translates the function body and contracts to Z3 constraints, then asks Z3 whether the postconditions can be violated.

## 2. What the Verifier Proves Automatically

### Postconditions

Given `@pre` as assumptions, the verifier proves `@post` holds for all valid inputs. The function body is translated to Z3 constraints with `$result` bound to the body's return value.

```lisp
(fn clamp ((x Int) (lo Int) (hi Int))
  (@spec ((Int Int Int) -> Int))
  (@pre {lo <= hi})
  (@post {$result >= lo})
  (@post {$result <= hi})
  (if {x < lo} lo
    (if {x > hi} hi x)))
```

### Range Types

Range type bounds are propagated through arithmetic. `(Int 0 .. 255)` generates the constraint `0 <= x <= 255` and maps to `uint8_t` in C.

```lisp
(fn safe-add ((a (Int 0 .. 100)) (b (Int 0 .. 100)))
  (@spec (((Int 0 .. 100) (Int 0 .. 100)) -> (Int 0 .. 200)))
  (@post {$result == (+ a b)})
  (+ a b))
```

### Type Invariants

`@invariant` on type definitions is assumed for parameters and checked for return values:

```lisp
(type Counter (record (count (Int 0 ..)) (max-count (Int 1 ..)))
  (@invariant {(. $self count) <= (. $self max-count)}))
```

### Record Field Axioms

The verifier knows that `(record-new Type (field value))` produces a value where `(. $result field) == value`. Similarly, imported constructor functions with `@post` annotations mapping parameters to fields are understood.

### Path-Sensitive Reasoning

The body is translated to Z3 with full path sensitivity. `if`/`match`/`cond` branches create separate Z3 paths, each with the appropriate conditions.

A `match` arm binds every payload position to its own accessor, at the sort the variant's declaration gives it (Real for `Float`, Bool for `Bool`, Int otherwise), and only for that arm. A quoted enum arm, `('red ...)`, is read by its tag. A match naming a tag the verifier has no index for is not translated.

### Early Returns

A function may leave through `(return v)` as well as through its last form, and each exit is checked against every `@post` and `@property`. There are three kinds of `return`:

- **Guarded early returns** — a bare `(return v)`, `(when C ... (return v))` or `(if C (return v) ...)` among the statements before the last form. The test is read as it stood at the top of the body, so it (and `v`) must read nothing an earlier statement may have changed: no name a `set!`, a push or a loop wrote (a write through a field or an index counts; one through a pointer makes a read through it, `(deref p)` or `p.n`, stale), nothing a `let` rebinds over a parameter, and no assignment in the test itself. After a write through any place or a call to a function that is not `@pure`, only a test made of plain names and arithmetic is still read as it stood. The body's translation carries these: `$result` is `v` on the path where `C` holds (and no earlier guard did), and the last form's value otherwise.
- **Other returns** — inside a loop, in a `match` arm, deeper inside an `if`, in a `let` initializer, or past a change to what the guard reads. There is no single condition to negate for these, so the body's translation reasons only about the runs that take none of them, and a forward walk of the body (the one that checks `@loop-invariant`, section 4) checks the contract where each of them leaves. There it knows the path that leads to the return, the loop's element and what is known of it, a proved invariant of each enclosing loop, every `@assume` that names nothing the body changes, and the value returned. A `@property` is checked there without the `@pre`s, as it is everywhere. A contract naming a parameter that a local shadows at the return (a loop variable, a match binder) is not checked there.
- **A return in a callback's lambda** leaves the callback, not the function, and nothing is claimed about `$result` for a function with one.

A `(return v)` that is the body's last form is just its value.

What the walk does not model it does not guess at: a value it could not follow (a loop's variable with no invariant to describe it, a construct it does not handle) makes the check at that return `unknown` rather than `failed`, and so does a counterexample of the main model in a function with such returns - that model runs on past them, so its run may be one that returned. A list literal `(list T ...)` written as the value itself - a record field, the value returned - has its length, not its elements; one bound to a name has neither, since the name may be pushed to.

`?` is not yet treated as an exit.

### Push-Built Results

A result built by pushes with no loop is modelled exactly: the verifier knows which elements it contains and in what order, as a function of the branch conditions. The shape is

```lisp
(let ((mut r (list-new arena T)))
  ... (list-push r e) inside do / let / when / if / cond / match ...
  r)
```

Each push under its path condition contributes `If(g, Concat(s, Unit(e)), s)`. A pushed `record-new` or `union-new` carries its fields and payloads. A callee's `@post`s and `@property`s are assumed where the call runs and its `@pre` holds.

Calls in the modelled terms follow three rules:
- **A `@pure` callee** is an uninterpreted function: the same arguments give the same value.
- **Any other callee** is allowed only if every parameter is a plain value (no list, map, set or pointer anywhere inside it, and no `mut`/`out` mode). Each such call is its own value, so two calls to a counter never collapse into one.
- **Anything else abandons the model.** That includes a builtin or function the verifier has no signature for, such as `arena-new`. So both directions of a claim about the elements are decidable:

```lisp
(fn cr1 ((arena Arena) (ctx Context) (b Node) (ax Ax))
  (@spec ((Arena Context Node Ax) -> (List Msg)))
  (@alloc arena)
  ;; nothing unlicensed is emitted
  (@property sound (forall (m $result) (== (. m to) (. ctx root))))
  ;; nothing licensed is missing
  (@property complete
    (match ax ((sub-name b2 a) (or (not (node-eq b b2))
                                   (exists (m $result) (== (. m to) (. ctx root)))))
              (_ true)))
  (let ((mut result (list-new arena Msg)))
    (do (match ax
          ((sub-name b2 a)
            (when (node-eq b b2) (list-push result (record-new Msg (to (. ctx root)) (v 1)))))
          (_ (do)))
        result)))
```

Write completeness as `exists` over field equalities, or as `list-contains` of a name: a `record-new` in a *contract* is a fresh value that no pushed element can equal.

The model is all or nothing. The body falls back to the loop patterns of section 3 (or to `unknown`, section 10) if any of these appear:
- a loop, `return`, `break`, lambda, `with-arena` or `c-inline`;
- a mutation of anything other than a local the body binds: `list-set`, `list-pop`, `set-put`, `map-put` and the like, or `set!` of a parameter;
- the result list passed to a call, aliased, read in a guard, or rebound;
- a push to another list, or a push inside a `let` initializer;
- a call made for its effect in statement position, or a call to a function that is neither `@pure` nor value-only;
- a guard that is not a Bool, or a term that cannot be translated.

A body that reads collection state (`set-has`, `map-get`, `list-len` and so on) must also call only `@pure` functions, since those reads are uninterpreted functions of the collection.

## 3. Automatic Loop Analysis

The verifier recognizes six loop patterns and generates Z3 axioms automatically. No `@loop-invariant` is needed for these patterns. A push-built result with no loop at all is modelled exactly instead (section 2, Push-Built Results).

### Filter

Conditional push of elements matching a predicate:

```lisp
(let ((mut result (list-new arena Triple)))
  (for-each (t items)
    (when (pred t)
      (list-push result t)))
  result)
```

**Generated axioms:**
- `(list-len result) <= (list-len items)`
- `(list-len result) >= 0`
- For each element in result: element came from source and satisfies `pred`
- Exclusion: if predicate is `(not (eq item x))`, then `x` is not in result

### Map/Transform

Unconditional push of a constructed element:

```lisp
(let ((mut result (list-new arena Triple)))
  (for-each (dt source)
    (list-push result
      (make-triple arena
        (triple-object dt)
        (triple-predicate dt)
        (triple-subject dt))))
  result)
```

**Generated axioms:**
- For each result element: exists a source element with field correspondence
- `(list-len result) <= (list-len source)`
- Completeness: for each filtered source element, a matching result exists

### Count

Conditional increment of a counter:

```lisp
(let ((mut count 0))
  (for-each (x items)
    (when (pred x)
      (set! count (+ count 1))))
  count)
```

**Generated axioms:**
- `$result >= 0`
- `$result <= (list-len items)`

### Fold

Accumulation with an operator:

```lisp
(let ((mut best init))
  (for-each (x items)
    (set! best (max best x)))
  best)
```

**Generated axioms (operator-dependent):**
- `max`: `$result >= init`
- `min`: `$result <= init`

### Find-First

Conditional assignment when result is nil:

```lisp
(let ((mut found nil))
  (for-each (item items)
    (when (and (== found nil) (pred item))
      (set! found item)))
  found)
```

### Nested Loop (Join)

Inner loop iterates over a collection derived from the outer loop variable. The verifier performs field provenance analysis, classifying each constructor field as OUTER, INNER, or CONSTANT:

```lisp
(let ((same-as (make-iri arena OWL_SAME_AS))
      (mut result (list-new arena Triple)))
  (for-each (dt (. delta triples))
    (when (term-eq (triple-predicate dt) same-as)
      (let ((x (triple-subject dt))
            (y (triple-object dt)))
        (let ((matches (indexed-graph-match arena g (some y) (some same-as) no-term)))
          (for-each (m matches)
            (let ((z (triple-object m)))
              (list-push result (make-triple arena x same-as z))))))))
  result)
```

**Field provenance:**
- `subject` → OUTER (from `x = triple-subject(dt)`)
- `predicate` → CONSTANT (from `same-as` in outer let)
- `object` → INNER (from `z = triple-object(m)`)

**Generated axioms:**
- For each result element: exists an outer source element satisfying the outer filter, with field correspondence based on provenance
- Size: `(list-len result) <= (list-len outer-source)`
- Imported postconditions from the inner collection's constructor function are instantiated

## 4. When @loop-invariant Is Needed

### Automatic @property Propagation

When a function has `@property` annotations but no explicit `@loop-invariant` on any loop, the verifier automatically uses the property body as the loop invariant at every `for-each` nesting level. The `$result` reference in the property is substituted with the actual mutable result variable name.

For example, given:

```lisp
(fn filter-items ((arena Arena) (items (List Item)))
  (@spec ((Arena (List Item)) -> (List Item)))
  (@property soundness
    (forall (t $result)
      (exists (src items)
        (item-valid src))))

  (let ((mut result (list-new arena Item)))
    (for-each (x items)
      (when (item-valid x)
        (list-push result x)))
    result))
```

The verifier automatically generates a loop invariant equivalent to:

```lisp
(forall (t result)
  (exists (src items)
    (item-valid src)))
```

This eliminates the need for manually writing identical `@loop-invariant` annotations. The automatic propagation applies when:
- The function has `@property` but no explicit `@loop-invariant`
- The function body contains a `for-each` loop
- The function returns a mutable variable (the standard accumulator pattern)

A propagated invariant is **not** checked the way an explicit one is (see How @loop-invariant Works below). It is left out when the property it came from is checked, so a property is never proved from itself (#125), but the postcondition check still assumes it.

### When Manual @loop-invariant Is Still Needed

The automatic analysis covers the six patterns above plus property auto-propagation. Most loops verify without manual invariants.

`@loop-invariant` is needed when:

- The postcondition involves **forall/exists** over the result relating to **multiple source collections** — the verifier cannot automatically express that each result element traces back to a specific source element through a specific join path
- **Complex relational invariants** that span the accumulated result and the current iteration state
- **Domain-specific semantic properties** that go beyond structural patterns

### Rule of Thumb

- Simple bounds and predicates (size, non-negativity, element membership) → **automatic**
- Forall/exists provenance tracing across nested loops → **@loop-invariant**

### Example: When It's Needed

The `eq-trans` function infers transitive `sameAs` triples via two nested loops (forward and backward). Its `@property completeness` states that every result triple traces back to a delta triple and a graph match. This requires `@loop-invariant` because:

1. There are two sibling inner loops (forward and backward patterns)
2. The property uses a disjunction (`or`) over two join paths
3. The verifier needs to know the invariant is maintained across both inner loops

```lisp
(for-each (dt (. delta triples))
  (@loop-invariant
    (forall (t result)
      (exists (src-dt (. delta triples))
        (and
          (term-eq (triple-predicate src-dt) (make-iri arena OWL_SAME_AS))
          (or
            (and ...)   ;; forward path
            (and ...)))))) ;; backward path
  ...)
```

As written, this invariant cannot be checked: it calls `make-iri`, which is not `@pure`, inside a quantifier (see the limits below). It reports `could not check loop invariant` and is not assumed.

### How @loop-invariant Works

An invariant is a claim that holds every time the loop is about to run its body, and therefore also where the loop ends. The verifier **proves** each one by induction before using it:

1. **Base case** — it holds where the loop is entered, given the function's `@pre`, the parameters' type invariants and range types, and what the code before the loop did.
2. **Inductive step** — starting from an arbitrary iteration where it holds (and, for a `while`, where the loop condition holds), one run of the body leaves it holding. Everything the loop may assign is a fresh value there; the loop variable of a `for-each` is an element of the collection, and a desugared callback's `@callback-assume` facts describe it.

Only a proved invariant is used afterwards, as a fact about the values each name had **where its loop ended** — not the values the function ends with, which a later loop or assignment may have changed. Since the base case assumed `@pre`, it is asserted under `@pre`, so a `@property` (checked without `@pre`) does not inherit it.

The check walks the function forward. A list the function makes with `list-new` and only pushes to, reads the length of, loops over, or returns is followed exactly: each push is `Concat(s, Unit(e))` under the conditions it runs under. A call's `@post` (and `@property`) is assumed about a value of the call's own. A call to a function that is not `@pure` may change collection state - through what it is handed, or through C - and so may a write through a place (`(set! (. p n) v)`, `(set! (@ xs 0) v)`); after either, a read of that state - `list-len` of an untracked list, `@`, a quantifier over a parameter's list, a field through a pointer - is something the check can no longer vouch for. A local whose address is taken (`addr`, of it or of a field), or that a lambda assigns, may be written by any such call, so an invariant naming one is not checked. A declared range is assumed of the parameters and their own fields, as the main verifier assumes it, but not of a local after an assignment nor of a field of a record the body builds: neither `set!` nor `record-new` checks it.

**Placement.** `@loop-invariant` must be the first form (or forms) of a `for-each`, `while` or `for` body. For a callback desugared into a loop, write it first in the lambda's body. Anywhere else is an error:

```
@loop-invariant must be the first form(s) of a for-each, for or while body: <expr>
```

Nested loops each carry their own; an inner loop's invariant is checked for every outer iteration and may rely on the outer one. A loop's invariants stand or fall together.

**Outcomes.**

| Message | Status | Meaning |
|---|---|---|
| `loop invariant not established on entry: <expr>` | failed | The base case has a counterexample: the loop can start where it does not hold. |
| `loop invariant not preserved: <expr>` | failed | The step has a counterexample: an iteration can start where it holds and end where it does not. |
| `could not check loop invariant: <expr> (<reason>)` | unknown / timeout | The check needs something it does not model; the reason says what. The invariant is not assumed. |

A failed invariant fails the function whatever its postconditions say. An unchecked one leaves the function unknown unless something else already failed it, since a postcondition that did not verify may have needed it.

**What is not checked** (reported as `could not check`):
- a loop body with `c-inline`, `break` or `continue`, or a `for` loop;
- a callback loop whose body has `return` (it leaves the callback, not the function);
- an invariant that reads collection state a call in the function may change (the reason names the call);
- an invariant that calls a function that is not `@pure` inside a quantifier - an uninterpreted function of its arguments is only right for one that is;
- a quantifier over a collection that is neither a tracked list nor a parameter (or a field of one) that is never reassigned;
- an invariant naming `$result` or the loop variable;
- a quantifier over a parameter whose name some binding in the function reuses;
- an invariant inside a lambda that is not desugared into a loop, or inside a `let` initializer that has statements in it;
- a loop the walk cannot reach through a construct it does not follow (`with-arena`, `spawn`, `try`, `?`).

A proved invariant over a tracked list is not used if the list is pushed to after the loop, nor one reading collection state if anything after the loop may change it; nor one needing the array encoding (`all-triples-have-predicate`, `list-ref`) - write those as a `forall` over the list instead. With a guarded `return` before the loop (section 2, Early Returns) it is stated only for the runs that took no early return, and not used at all when an assignment or a `?` also precedes the loop, when the loop is nested in another or does not run on every path (a loop inside an `if` arm), or when the function body has more than one form.

When a postcondition then fails, the result is `unknown`, not `failed`, with a line `loop invariant proved but not used: <expr> (<reason>)` - the counterexample may be one the invariant rules out.

## 5. @property vs @post

**@post** is verified against the function body with preconditions assumed:

```lisp
(fn f ((x Int))
  (@pre {x > 0})
  (@post {$result > 0})
  (* x 2))
```

**@property** is verified independently of preconditions. Properties are named, which aids diagnostics:

```lisp
(fn eq-trans (...)
  (@property completeness
    (forall (t $result)
      (exists (dt (. delta triples))
        ...))))
```

Use `@post` for direct input/output contracts. Use `@property` for universal assertions that should hold regardless of preconditions, or when you want named diagnostics in verification output.

## 6. @assume — Trusted Assertions

`@assume` declares an axiom that is trusted without proof:

```lisp
(fn use-ffi-result ((ptr (Ptr Data)))
  (@spec (((Ptr Data)) -> Int))
  (@assume (!= ptr nil))
  (. ptr value))
```

Use cases:
- **FFI behavior**: the verifier cannot see into C functions
- **Complex loop invariants**: when automatic analysis is insufficient and writing a full invariant is impractical
- **Breaking circular dependencies**: when two functions' contracts depend on each other

Assumptions are reported as "Verified via @assume (trusted)" in verification output.

**Soundness warning**: every `@assume` is a potential source of unsoundness. If an assumption is false, the verifier may accept incorrect code. Use sparingly.

## 7. @callback-assume — Higher-Order Function Reasoning

`@callback-assume` specifies properties that hold for every argument passed to a callback parameter in higher-order functions.

**Syntax:**

```lisp
(@callback-assume <callback-param> <property-expr>)
```

Where `$callback-arg` is a magic variable referring to each argument passed to the callback.

**Example:**

```lisp
(fn for-each-item ((g Graph) (callback (Fn (Item) Unit)))
  (@intent "Apply callback to each item in graph")
  (@spec ((Graph (Fn (Item) Unit)) -> Unit))
  (@callback-assume callback (graph-contains g $callback-arg))
  ...)
```

This declares that every `Item` passed to `callback` satisfies `(graph-contains g item)`.

**How it works:** The verifier desugars callback-taking function calls into `for-each` loops and transforms the `@callback-assume` into a `(forall (t $result) ...)` axiom. This enables Z3 to reason about what properties hold for the values the callback processes.

**Note:** The callback parameter itself is excluded from call-site argument matching — only the non-callback arguments are matched against `@spec` parameter types.

## 8. Imported Function Reasoning

When a module imports functions, the verifier uses their contracts as axioms.

### Postcondition Propagation

An imported function's `@post` becomes an axiom available to callers:

```lisp
;; In module rdf:
(fn make-triple ((arena Arena) (s Term) (p Term) (o Term))
  (@post (== (triple-subject $result) s))
  (@post (== (triple-predicate $result) p))
  (@post (== (triple-object $result) o))
  ...)

;; In the importing module, the verifier knows:
;; (triple-subject (make-triple arena s p o)) == s
```

### Equality Function Semantics

Functions matching the pattern `*-eq` with postcondition `(@post (== $result (== a b)))` generate a Z3 axiom `ForAll a, b: fn(a, b) == (a == b)`, enabling the verifier to reason about equality.

### Collection Postconditions

Imported functions with `(forall (t $result) ...)` postconditions generate universally quantified axioms over their results, enabling verification of properties that depend on query results.

### Containment Congruence

When a nested loop iterates over query results contained in a collection `g`, and a property checks `contains(g, constructor(arena, fields...))`, the verifier generates **containment congruence axioms** that bridge element containment to constructed element containment. For each element `elem` in the inner sequence known to be in `g`:

```
contains(g, constructor(arena, field1(elem), field2(elem), ...))
```

This works with any record type that has:
1. A constructor function with `@post` mapping parameters to fields
2. A contains predicate (e.g., `indexed-graph-contains`, or any `*-contains` function)

The axioms are sound because containment checks by field equality, not object identity.

## 9. Verifier-Only Predicates

### list-contains

`(list-contains lst elem)` is a verifier-only predicate for membership testing. It is usable in `@post`, `@property`, `@loop-invariant`, and `@assume` annotations, but has no runtime representation (no C codegen).

It translates to the Z3 constraint:

```
Exists idx: 0 <= idx < Length(lst) && lst[idx] == elem
```

Example usage in a postcondition:

```lisp
(fn collect-valid ((arena Arena) (items (List Item)) (target Item))
  (@spec ((Arena (List Item) Item) -> (List Item)))
  (@pre (list-contains items target))
  (@post (list-contains $result target))

  (let ((mut result (list-new arena Item)))
    (for-each (x items)
      (list-push result x))
    result))
```

Since `list-contains` is verifier-only, it cannot appear in runtime code — only in contract annotations.

`(list-contains $result x)` reads the result as a sequence, exactly as `(forall (m $result) ...)` does, so for a push-built result (section 2) it is proved or refuted rather than left uninterpreted. The element is compared by identity: `x` should be a name or a field of one. A `record-new` in the contract is a fresh value, so use `exists` over its fields instead.

## 10. Troubleshooting Verification Failures

### timeout

The Z3 solver exceeded its time limit (default: 5 seconds).

**Common causes:**
- Quantifier-heavy properties (nested forall/exists)
- Non-linear arithmetic
- Large function bodies with many paths

**Fixes:**
- Add `@loop-invariant` to guide the solver
- Simplify postconditions
- Break the function into smaller pieces
- Use `@assume` as a last resort

### failed + counterexample

The verifier found concrete input values that violate the postcondition. The counterexample shows variable assignments.

**Common causes:**
- The postcondition is genuinely wrong
- Missing `@pre` — the postcondition doesn't hold for all inputs
- The function body has a bug

**Reading counterexamples:** variable names map to Z3's internal representation. Look for the function parameters and `$result` to understand the failing case.

### unknown

Z3 could not determine satisfiability.

**Common causes:**
- Non-linear arithmetic (`*`, `/`, `mod` on symbolic values)
- Complex quantifier instantiation patterns
- "the body's pushes are not modelled": a claim about a push-built result's elements, where the body is neither a recognized loop pattern (section 3) nor loop-free (section 2, Push-Built Results). The listed fallback shapes are the usual reasons.

### Loop invariant messages

- **`loop invariant not established on entry`** — the counterexample shows the invariant's names where the loop starts. Usually a missing `@pre`, or an initializer that does not satisfy the invariant.
- **`loop invariant not preserved`** — the counterexample shows the names where an iteration ends. The body can break the invariant, or the invariant is true but not inductive: strengthen it with what the body needs to keep it (a bound on a counter, a callee's `@post`).
- **`could not check loop invariant`** — the reason in parentheses names what the check does not model (section 4, How @loop-invariant Works). Move the construct out of the loop, give the callee a contract, or restate the invariant over something the check follows.

### Messages at a return

- **`postcondition does not hold at the return on line N`** (or `property ... does not hold`) — a return inside a loop, a `match` arm or past an assignment (section 2, Early Returns) yields a value the contract does not allow. The counterexample shows `$result` and the names the returned value is built from.
- **`could not check postcondition at the return on line N`** — the reason in parentheses says what the walk could not follow there. The usual one is a value a loop computes with no `@loop-invariant` to describe it.

### "Could not translate"

The verifier encountered a SLOP construct it cannot represent in Z3.

**Fix:** simplify the expression, or use `@assume` to bypass verification for that contract.

### Verifier Suggestions

When verification fails, the verifier prints actionable suggestions:

- **Unrecognized loop**: "Function contains a loop that the verifier cannot analyze automatically. Add `(@loop-invariant condition)` inside the loop body, or add `(@assume postcondition)` to trust the postcondition."
- **Filter pattern insufficient**: "Loop resembles filter pattern but postcondition may need additional axioms."
- **Field relationship**: "Consider adding `@invariant` to the type definition."
- **Complex equality**: "This equality function uses nested match — too complex for automatic verification. Consider breaking into smaller functions."
- **Conditional insert with contains**: "Consider `(@assume (predicate-name $result item))` to trust the invariant."

## 11. Practical Examples

### Simple: Arithmetic with Range Types

```lisp
(fn percentage ((part (Int 0 ..)) (total (Int 1 ..)))
  (@spec (((Int 0 ..) (Int 1 ..)) -> (Int 0 ..)))
  (@pre {part <= total})
  (@post {$result >= 0})
  (@post {$result <= 100})
  (/ (* part 100) total))
```

The verifier uses range constraints (`part >= 0`, `total >= 1`) and the precondition (`part <= total`) to prove both postconditions.

### Intermediate: Filter Loop Verified Automatically

```lisp
(fn eq-sym ((arena Arena) (g IndexedGraph) (delta Delta))
  (@spec ((Arena IndexedGraph Delta) -> (List Triple)))
  (@post {(list-len $result) >= 0})
  (@post (all-triples-have-predicate $result OWL_SAME_AS))

  (let ((same-as (make-iri arena OWL_SAME_AS))
        (mut result (list-new arena Triple)))
    (for-each (dt (. delta triples))
      (when (term-eq (triple-predicate dt) same-as)
        (let ((inferred (make-triple arena
                (triple-object dt) same-as (triple-subject dt))))
          (when (not (indexed-graph-contains g inferred))
            (list-push result inferred)))))
    result))
```

The verifier detects a filter+map pattern: conditional push of a constructed element. It automatically generates axioms establishing that every result element has `same-as` as its predicate (from the `make-triple` postcondition) and that the result size is bounded.

### Advanced: Nested Loop with @loop-invariant

The `eq-trans` function (from `eq.slop`) uses two nested loops to find transitive `sameAs` inferences. Its `@property completeness` requires `@loop-invariant` because the property traces each result triple back through a specific delta triple and graph match, with a disjunction over forward and backward paths.

See `eq.slop` for the full implementation with invariants.

### Escape Hatch: @assume for FFI

```lisp
(fn graph-load ((arena Arena) (path String))
  (@spec ((Arena String) -> IndexedGraph))
  (@assume {(indexed-graph-size $result) >= 0})
  ;; FFI call to C graph loader
  (ffi-graph-load arena path))
```

The verifier cannot analyze FFI calls, so `@assume` declares the expected behavior. This is reported as trusted in verification output.
