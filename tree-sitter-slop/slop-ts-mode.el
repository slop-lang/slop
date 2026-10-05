;;; slop-ts-mode.el --- Tree-sitter support for SLOP -*- lexical-binding: t; -*-

;; Copyright (C) 2024

;; Author: SLOP Authors
;; Keywords: languages, lisp, tree-sitter
;; Version: 0.4.0
;; Package-Requires: ((emacs "29.1"))

;;; Commentary:

;; Major mode for editing SLOP (Symbolic LLM-Optimized Programming) files,
;; powered by tree-sitter.

;; Installation:
;;
;; 1. Add tree-sitter-slop to your load path
;; 2. Add to your init.el:
;;
;;    (add-to-list 'treesit-language-source-alist
;;      '(slop . ("/path/to/slop/tree-sitter-slop")))
;;    (treesit-install-language-grammar 'slop)
;;    (require 'slop-ts-mode)

;;; Code:

(require 'treesit)

(defgroup slop nil
  "Support for SLOP."
  :group 'languages)

(defcustom slop-ts-mode-indent-offset 2
  "Number of spaces for each indentation step in `slop-ts-mode'."
  :type 'integer
  :group 'slop)

;; Keep these lists in sync with queries/highlights.scm.
(defconst slop-ts-mode--keywords
  '("fn" "impl" "module" "export" "import"
    "type" "const" "alias" "record" "enum" "union"
    "let" "let*" "mut" "in"
    "if" "cond" "match" "when" "while"
    "for" "for-each" "do"
    "break" "continue" "return" "else" "guard" "catch"
    "forall" "exists" "implies"
    "hole" "ffi" "ffi-struct" "c-inline")
  "Special forms highlighted as keywords when they head a list.")

(defconst slop-ts-mode--builtins
  '(;; Arithmetic
    "+" "-" "*" "/" "%"
    ;; Bitwise
    "&" "|" "^" "<<" ">>"
    ;; Comparison
    "==" "!=" "<" "<=" ">" ">="
    ;; Boolean
    "and" "or" "not"
    ;; Min/Max
    "min" "max"
    ;; Data access
    "." "@" "set!" "deref"
    ;; Result/Option
    "ok" "error" "?" "is-ok" "unwrap" "some" "none" "is-some" "is-none"
    ;; Type/Memory
    "cast" "sizeof" "addr"
    ;; Data construction
    "quote" "list" "set" "record-new" "union-new"
    ;; Arena
    "arena-new" "arena-alloc" "arena-free" "with-arena"
    ;; String operations
    "string-new" "string-len" "string-concat" "string-eq" "string-slice"
    "string-split" "string-push-char" "int-to-string"
    ;; List operations
    "list-new" "list-push" "list-get" "list-set" "list-pop" "list-len"
    ;; Map operations
    "map-new" "map-put" "map-get" "map-has" "map-keys" "map-remove" "map-len"
    ;; Set operations
    "set-new" "set-put" "set-has" "set-remove" "set-elements" "set-len"
    ;; Concurrency
    "chan" "chan-buffered" "chan-close" "send" "recv" "try-recv" "spawn" "join"
    ;; Time
    "now-ms" "sleep-ms"
    ;; Console I/O
    "print" "println")
  "Built-in operators and functions highlighted when they head a list.")

(defun slop-ts-mode--word-regexp (words)
  "Return a regexp matching exactly one of WORDS."
  (concat "\\`" (regexp-opt words) "\\'"))

;; Font-lock settings
(defvar slop-ts-mode--font-lock-settings
  (treesit-font-lock-rules
   :language 'slop
   :feature 'comment
   '((comment) @font-lock-comment-face)

   :language 'slop
   :feature 'string
   '((string) @font-lock-string-face)

   :language 'slop
   :feature 'number
   '((number) @font-lock-number-face)

   :language 'slop
   :feature 'constant
   '((boolean) @font-lock-constant-face
     (nil) @font-lock-constant-face
     (quoted_symbol) @font-lock-constant-face)

   :language 'slop
   :feature 'type
   '((type_name) @font-lock-type-face)

   :language 'slop
   :feature 'property
   '((keyword) @font-lock-property-name-face)

   :language 'slop
   :feature 'annotation
   '((annotation) @font-lock-preprocessor-face)

   :language 'slop
   :feature 'keyword
   `((list
      :anchor
      (identifier) @font-lock-keyword-face
      (:match ,(slop-ts-mode--word-regexp slop-ts-mode--keywords)
              @font-lock-keyword-face)))

   :language 'slop
   :feature 'operator
   `((list
      :anchor
      (identifier) @font-lock-operator-face
      (:match ,(slop-ts-mode--word-regexp slop-ts-mode--builtins)
              @font-lock-operator-face))
     ;; Prefix calls inside infix: {(. $result len) >= 1}
     (infix_group
      :anchor
      (identifier) @font-lock-operator-face
      (:match ,(slop-ts-mode--word-regexp slop-ts-mode--builtins)
              @font-lock-operator-face))
     (range_dots) @font-lock-operator-face)

   :language 'slop
   :feature 'function
   '((list
      :anchor
      (identifier) @_fn
      (:match "^fn$" @_fn)
      :anchor
      (identifier) @font-lock-function-name-face))

   :language 'slop
   :feature 'definition
   '((list
      :anchor
      (identifier) @_type
      (:match "^type$" @_type)
      :anchor
      (type_name) @font-lock-type-face))

   ;; Override: a MAX_CONN-style name is a type_name, already faced by the
   ;; `type' feature.
   :language 'slop
   :feature 'definition
   :override t
   '((list
      :anchor
      (identifier) @_const
      (:match "^const$" @_const)
      :anchor
      [(identifier) (type_name)] @font-lock-constant-face))

   ;; Compiler-provided names: $result, $callback-arg, ...
   :language 'slop
   :feature 'definition
   '(((identifier) @font-lock-builtin-face
      (:match "^\\$" @font-lock-builtin-face)))

   ;; NOTE: no `:override t' here. The variable feature runs in the last
   ;; feature-list level, so with override it would re-fontify every head
   ;; identifier as a variable, clobbering the keyword/operator/function/
   ;; definition faces applied earlier. Without override it only fills
   ;; identifiers that nothing more specific has already faced.
   :language 'slop
   :feature 'variable
   '((identifier) @font-lock-variable-name-face)

   :language 'slop
   :feature 'bracket
   '(["(" ")" "{" "}"] @font-lock-bracket-face)

   :language 'slop
   :feature 'infix
   '((infix_binary ["and" "or"] @font-lock-keyword-face)
     (infix_binary ["==" "!=" "<" "<=" ">" ">=" "+" "-" "*" "/" "%"] @font-lock-operator-face)
     (infix_unary "not" @font-lock-keyword-face)
     (infix_unary "-" @font-lock-operator-face)))
  "Tree-sitter font-lock settings for SLOP.")

;; Indentation
(defvar slop-ts-mode--indent-rules
  '((slop
     ((parent-is "source_file") column-0 0)
     ((node-is ")") parent-bol 0)
     ((node-is "}") parent-bol 0)
     ((parent-is "list") parent-bol slop-ts-mode-indent-offset)
     ((parent-is "infix_expr") parent-bol slop-ts-mode-indent-offset)))
  "Tree-sitter indentation rules for SLOP.")

;; Navigation
(defconst slop-ts-mode--defun-heads '("fn" "type" "module")
  "Heads of the list forms that `slop-ts-mode' treats as defuns.")

(defun slop-ts-mode--head (node)
  "Return the text of NODE's leading identifier, or nil if it has none."
  (let ((head (treesit-node-child node 0 t)))
    (when (and head (equal (treesit-node-type head) "identifier"))
      (treesit-node-text head t))))

(defun slop-ts-mode--defun-p (node)
  "Return non-nil if NODE is a top-level fn, type or module form.
Top level means a direct child of the source file or of a module form,
so nested lists such as (fn ...) inside a body do not count."
  (and (member (slop-ts-mode--head node) slop-ts-mode--defun-heads)
       (let ((parent (treesit-node-parent node)))
         (and parent
              (or (equal (treesit-node-type parent) "source_file")
                  (equal (slop-ts-mode--head parent) "module"))))))

(defun slop-ts-mode--defun-name (node)
  "Return the name of the fn, type or module form NODE, or nil."
  (when (member (slop-ts-mode--head node) slop-ts-mode--defun-heads)
    (let ((name (treesit-node-child node 1 t)))
      (and name (treesit-node-text name t)))))

;;;###autoload
(define-derived-mode slop-ts-mode prog-mode "SLOP"
  "Major mode for editing SLOP files, powered by tree-sitter.

\\{slop-ts-mode-map}"
  :group 'slop

  (unless (treesit-ready-p 'slop)
    (error "Tree-sitter grammar for SLOP is not available"))

  (treesit-parser-create 'slop)

  ;; Comments
  (setq-local comment-start "; ")
  (setq-local comment-end "")
  (setq-local comment-start-skip ";+ *")

  ;; Font-lock
  (setq-local treesit-font-lock-settings slop-ts-mode--font-lock-settings)
  (setq-local treesit-font-lock-feature-list
              '((comment string)
                (keyword type annotation)
                (constant number property operator function definition infix)
                (variable bracket)))

  ;; Indentation
  (setq-local treesit-simple-indent-rules slop-ts-mode--indent-rules)

  ;; Navigation: top-level fn/type/module forms are defuns
  (setq-local treesit-defun-type-regexp
              (cons "\\`list\\'" #'slop-ts-mode--defun-p))
  (setq-local treesit-defun-name-function #'slop-ts-mode--defun-name)

  (treesit-major-mode-setup))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.slop\\'" . slop-ts-mode))

(provide 'slop-ts-mode)
;;; slop-ts-mode.el ends here
