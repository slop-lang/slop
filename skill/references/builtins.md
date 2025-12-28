# SLOP Built-in Functions

SLOP is minimal. These are the ONLY built-in functions.

**Remember: Every function needs `@intent` and `@spec` annotations!**

## I/O (Strings Only)

```
(print str)              ; print string, no newline
(println str)            ; print string with newline
```

To print other types, convert to string first:
```
(println (int-to-string arena n))   ; print integer
```

## String Operations

```
(int-to-string arena n)   ; Int -> String (requires arena)
(string-len s)            ; String -> Int
(string-concat arena a b) ; String String -> String
(string-eq a b)           ; String String -> Bool
```

## Arithmetic

```
(+ a b)  (- a b)  (* a b)  (/ a b)  (% a b)
```

## Comparison

```
(== a b)  (!= a b)  (< a b)  (> a b)  (<= a b)  (>= a b)
```

## Logical

```
(and a b ...)   ; variadic, short-circuit
(or a b ...)    ; variadic, short-circuit
(not a)
```

## Memory

```
(arena-new size)         ; create arena
(arena-alloc arena size) ; allocate from arena
(arena-free arena)       ; free arena
(with-arena size body)   ; scoped arena (implicit 'arena' var)
(sizeof Type)            ; size of type in bytes
(addr expr)              ; address-of (&expr)
(deref ptr)              ; dereference pointer (*ptr)
```

## Data Construction

```
(ok val)                 ; Result success
(error e)                ; Result error
(some val)               ; Option some
(none)                   ; Option none
(record-new Type (field1 val1) ...)  ; create record
(union-new Type variant val)         ; create union variant
(list elem1 elem2 ...)   ; create list literal
(array elem1 elem2 ...)  ; create array literal
```

## Field Access

```
(. record field)         ; field access (record->field)
(set! record field val)  ; field mutation
(@ arr idx)              ; array indexing (arr[idx])
```

## List Operations

```
(list-new arena)         ; create empty list
(list-push list elem)    ; append element to list
(list-get list idx)      ; get element at index
(list-len list)          ; get list length
```

Note: `list-append` does NOT exist. Use `list-push` to add elements.

## Map Operations

```
(map-new arena)          ; create empty map
(map-put map key val)    ; insert/update key-value pair
(map-get map key)        ; get value (returns Option)
(map-has map key)        ; check if key exists -> Bool
```

## Control Flow

```
(if cond then else)
(cond (test1 body1) ... (else body))
(match expr (pattern body)...)
(when cond body)         ; no else branch
(for (i start end) body) ; exclusive end
(for-each (x list) body)
(while cond body)
(do expr1 expr2 ...)     ; sequence expressions, returns last
(break)
(continue)
(return val)
```

### Match Patterns

**Simple enums** - bare symbols only, NO bindings (enums have no data):
```
(match status
  (Pending (println "waiting"))
  (Active (println "running"))
  (Done (println "finished")))
```

**Tagged unions** - bindings allowed (unions carry data):
```
(match result
  ((ok val) (use val))      ; bind 'val' from ok variant
  ((error e) (handle e)))   ; bind 'e' from error variant
```

**WRONG** - trying to bind from simple enum:
```
(match status
  ((Active x) ...))   ; ERROR: Active has no data to bind
```

## Error Handling

```
(? result)               ; early return on error
(try expr)               ; catch errors
```

## Let Bindings

```
(let ((x val1) (y val2)) body)   ; parallel binding
(let* ((x val1) (y (+ x 1))) body) ; sequential binding
```

## NOT Built-in (Common Mistakes)

These do NOT exist - use alternatives:

| Don't Use | Use Instead |
|-----------|-------------|
| `print-int n` | `(println (int-to-string arena n))` |
| `print-float n` | `(println (float-to-string arena n))` |
| `(println enum-value)` | Use `match` to print different strings |
| `(union-new Type variant ())` for enum | Just use `variant` directly |
| `((EnumVariant x) ...)` in match | `(EnumVariant ...)` - simple enums have no data |
| `arena` outside with-arena | Wrap code in `(with-arena size ...)` |
| `(block ...)` | `(do ...)` for sequencing |
| `(begin ...)` | `(do ...)` for sequencing |
| `(progn ...)` | `(do ...)` for sequencing |
| `read-line` | FFI to stdio.h |
| `sqrt`, `sin`, `cos` | FFI to math.h |
| `strlen s` | `(string-len s)` |
| `malloc` | `(arena-alloc arena size)` |
| `arr.length` | Arrays are fixed size - use declared size (e.g., 100 for `Array T 100`) |
| `list.length` | `(list-len list)` |
| `list-append` | `(list-push list elem)` - push adds to end |
| `list-add` | `(list-push list elem)` |
| `map-set` | `(map-put map key val)` |
| `hash-get` | `(map-get map key)` |
