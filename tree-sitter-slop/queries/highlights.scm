; SLOP syntax highlighting queries for tree-sitter
;
; Ordering: when several patterns capture the same node, the LAST matching
; pattern wins in the tree-sitter CLI (tree-sitter-highlight), Neovim, Zed and
; Helix (25.07+, which reversed its old first-match order). So the catch-alls
; (`(type_name) @type`, `(identifier) @variable`) come FIRST and the specific
; head-of-list / definition rules follow and override them. Do not move the
; catch-alls to the bottom: every head would then be colored as a variable.
;
; The definition rules capture the head (fn, type, const, module) as @keyword
; rather than a private @_name capture: in tree-sitter-highlight a later private
; capture on the head would replace @keyword and leave it uncolored.

; Comments
(comment) @comment

; Strings
(string) @string

; Numbers
(number) @number

; Boolean and nil
(boolean) @constant.builtin
(nil) @constant.builtin

; Quoted symbols (enum values like 'ok, 'Fizz)
(quoted_symbol) @constant

; Keywords (:complexity, :required, :c-name, :arena, etc.)
(keyword) @property

; Annotations (@intent, @spec, @pre, @post, @callback-assume, ...)
(annotation) @attribute

; Range dots
(range_dots) @operator

; Type names (PascalCase). Catch-all: overridden by the rules below.
(type_name) @type

; Generic identifiers (variables, function calls). Catch-all: overridden by
; the rules below.
((identifier) @variable
  (#not-match? @variable "^\\$"))

; Compiler-provided names ($result, $callback-arg, ...)
((identifier) @variable.builtin
  (#match? @variable.builtin "^\\$"))

; Special forms - first identifier in a list
((list
  .
  (identifier) @keyword)
  (#any-of? @keyword
    "fn" "impl" "module" "export" "import"
    "type" "const" "alias" "record" "enum" "union"
    "let" "let*" "mut" "in"
    "if" "cond" "match" "when" "while"
    "for" "for-each" "do"
    "break" "continue" "return" "else" "guard" "catch"
    "forall" "exists" "implies"
    "hole" "ffi" "ffi-struct" "c-inline"))

; Built-in operators as first element (also prefix calls inside infix:
; {(. $result len) >= 1})
([
  (list
    .
    (identifier) @operator)
  (infix_group
    .
    (identifier) @operator)
  ]
  (#any-of? @operator
    ; Arithmetic
    "+" "-" "*" "/" "%"
    ; Bitwise
    "&" "|" "^" "<<" ">>"
    ; Comparison
    "==" "!=" "<" "<=" ">" ">="
    ; Boolean
    "and" "or" "not"
    ; Min/Max
    "min" "max"
    ; Data access
    "." "@" "set!" "deref"
    ; Result/Option
    "ok" "error" "?" "is-ok" "unwrap" "some" "none" "is-some" "is-none"
    ; Type/Memory
    "cast" "sizeof" "addr"
    ; Data construction
    "quote" "list" "set" "record-new" "union-new"
    ; Arena
    "arena-new" "arena-alloc" "arena-free" "with-arena"
    ; String operations
    "string-new" "string-len" "string-concat" "string-eq" "string-slice"
    "string-split" "string-push-char" "int-to-string"
    ; List operations
    "list-new" "list-push" "list-get" "list-set" "list-pop" "list-len"
    ; Map operations
    "map-new" "map-put" "map-get" "map-has" "map-keys" "map-remove" "map-len"
    ; Set operations
    "set-new" "set-put" "set-has" "set-remove" "set-elements" "set-len"
    ; Concurrency
    "chan" "chan-buffered" "chan-close" "send" "recv" "try-recv" "spawn" "join"
    ; Time
    "now-ms" "sleep-ms"
    ; Console I/O
    "print" "println"))

; Function name (second element after 'fn')
((list
  .
  (identifier) @keyword
  .
  (identifier) @function)
  (#eq? @keyword "fn"))

; Type name in type definition
((list
  .
  (identifier) @keyword
  .
  (type_name) @type.definition)
  (#eq? @keyword "type"))

; Constant name in const definition (MAX_CONN or max-conn)
((list
  .
  (identifier) @keyword
  .
  [(identifier) (type_name)] @constant)
  (#eq? @keyword "const"))

; Module name
((list
  .
  (identifier) @keyword
  .
  (identifier) @module)
  (#eq? @keyword "module"))

; Brackets
"(" @punctuation.bracket
")" @punctuation.bracket
"{" @punctuation.bracket
"}" @punctuation.bracket

; Infix operators
(infix_binary
  ["and" "or"] @keyword.operator)

(infix_binary
  ["==" "!=" "<" "<=" ">" ">=" "+" "-" "*" "/" "%"] @operator)

(infix_unary
  "not" @keyword.operator)

(infix_unary
  "-" @operator)
