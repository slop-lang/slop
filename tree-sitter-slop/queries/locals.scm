; SLOP local variable scoping queries

; Function definitions create a new scope
(list
  .
  (identifier) @_fn
  (#eq? @_fn "fn")
  (identifier) @local.definition.function) @local.scope

; Let bindings create local definitions
(list
  .
  (identifier) @_let
  (#any-of? @_let "let" "let*")
  (list
    (list
      (identifier) @local.definition.var))) @local.scope

; For loop variables
(list
  .
  (identifier) @_for
  (#eq? @_for "for")
  (list
    (identifier) @local.definition.var)) @local.scope

; For-each loop variables
(list
  .
  (identifier) @_foreach
  (#eq? @_foreach "for-each")
  (list
    (identifier) @local.definition.var)) @local.scope

; Match creates a scope
(list
  .
  (identifier) @_match
  (#eq? @_match "match")) @local.scope

; Function parameters create local definitions
(list
  .
  (identifier) @_fn
  (#eq? @_fn "fn")
  .
  (identifier)
  .
  (list
    (list
      (identifier) @local.definition.parameter)))

; References to identifiers
(identifier) @local.reference
