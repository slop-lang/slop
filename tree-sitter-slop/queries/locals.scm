; SLOP local variable scoping queries

; Function definitions create a new scope: (fn name (params) ...)
((list
  .
  (identifier) @_fn
  .
  (identifier) @local.definition.function)
  (#eq? @_fn "fn")) @local.scope

; Let creates a scope
((list
  .
  (identifier) @_let)
  (#any-of? @_let "let" "let*")) @local.scope

; Let bindings create local definitions. Only the bound name is a
; definition: (let ((x expr) (x Type expr)) ...)
((list
  .
  (identifier) @_let
  .
  (list
    (list
      .
      (identifier) @local.definition.var)))
  (#any-of? @_let "let" "let*")
  (#not-eq? @local.definition.var "mut"))

; ... or the name after a leading `mut`: (let ((mut x Type expr)) ...)
((list
  .
  (identifier) @_let
  .
  (list
    (list
      .
      (identifier) @_mut
      .
      (identifier) @local.definition.var)))
  (#any-of? @_let "let" "let*")
  (#eq? @_mut "mut"))

; For loop variables: (for (i start end) ...)
((list
  .
  (identifier) @_for
  .
  (list
    .
    (identifier) @local.definition.var))
  (#eq? @_for "for")) @local.scope

; For-each loop variables: (for-each (item coll) ...) and
; (for-each ((key value) map) ...)
((list
  .
  (identifier) @_foreach
  .
  (list
    .
    [
      (identifier) @local.definition.var
      (list (identifier) @local.definition.var)
    ]))
  (#eq? @_foreach "for-each")) @local.scope

; Match creates a scope
((list
  .
  (identifier) @_match)
  (#eq? @_match "match")) @local.scope

; Function parameters create local definitions: (x T), (in x T)
((list
  .
  (identifier) @_fn
  .
  (identifier)
  .
  (list
    (list
      .
      (identifier) @local.definition.parameter)))
  (#eq? @_fn "fn")
  (#not-any-of? @local.definition.parameter "in" "mut"))

; ... and (mut x T) / (in x T): the name after the mode
((list
  .
  (identifier) @_fn
  .
  (identifier)
  .
  (list
    (list
      .
      (identifier) @_mode
      .
      (identifier) @local.definition.parameter)))
  (#eq? @_fn "fn")
  (#any-of? @_mode "in" "mut"))

; References to identifiers
(identifier) @local.reference
