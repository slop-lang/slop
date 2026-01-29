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

## 3. Automatic Loop Analysis

The verifier recognizes six loop patterns and generates Z3 axioms automatically. No `@loop-invariant` is needed for these patterns.

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

### How @loop-invariant Works

The invariant expression is extracted and trusted as an assumption — it is **not** proven by the verifier. It serves as a bridge: the verifier assumes the invariant holds at each iteration and uses it to prove the postcondition after the loop completes.

Place `@loop-invariant` as the first expression inside the loop body. For nested loops, each loop level can have its own invariant.

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

## 7. Imported Function Reasoning

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

## 8. Verifier-Only Predicates

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

## 9. Troubleshooting Verification Failures

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

## 10. Practical Examples

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
