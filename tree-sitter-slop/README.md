# tree-sitter-slop

Tree-sitter grammar for SLOP (Symbolic LLM-Optimized Programming).

## Installation

### Neovim (with nvim-treesitter)

Add to your nvim-treesitter config:

```lua
local parser_config = require("nvim-treesitter.parsers").get_parser_configs()
parser_config.slop = {
  install_info = {
    url = "/path/to/slop/tree-sitter-slop",
    files = {"src/parser.c"},
  },
  filetype = "slop",
}
```

Then run `:TSInstall slop`

### Helix

Add to `~/.config/helix/languages.toml`:

```toml
[[language]]
name = "slop"
scope = "source.slop"
injection-regex = "slop"
file-types = ["slop"]
roots = []
comment-token = ";"
indent = { tab-width = 2, unit = "  " }

[[grammar]]
name = "slop"
source = { path = "/path/to/slop/tree-sitter-slop" }
```

Then run `hx --grammar fetch` and `hx --grammar build`

### Emacs (with tree-sitter)

```elisp
(add-to-list 'treesit-language-source-alist
  '(slop . ("/path/to/slop/tree-sitter-slop")))
(treesit-install-language-grammar 'slop)
```

## Development

```bash
# Install dependencies (tree-sitter-cli 0.26)
npm install

# Generate parser (ABI 14, so Emacs 29/30 can load it)
npm run generate

# Run tests
npm run test

# Parse a file
npm run parse -- /path/to/file.slop
```

`src/parser.c` is generated with `tree-sitter generate --abi 14`. Keep the
ABI at 14 when regenerating: Emacs 29 and 30 link tree-sitter runtimes that
cannot load ABI 15 grammars.

## Node Types

The grammar is deliberately shallow. Special forms (`fn`, `let`, `match`, ...)
and operators (`+`, `list-push`, ...) are not separate node types: they are
`identifier` nodes at the head of a `list`, and the queries pick them out by
position and text.

| Node | Matches |
|------|---------|
| `source_file` | A whole file: a sequence of forms |
| `list` | `( ... )` |
| `infix_expr` | `{ ... }` infix contract expression |
| `infix_binary` | `a op b` inside `{}` (`or`, `and`, `==`/`!=`, `<`/`<=`/`>`/`>=`, `+`/`-`, `*`/`/`/`%`, loosest first) |
| `infix_unary` | `not x` or `-x` inside `{}` |
| `infix_group` | `( ... )` inside `{}`: grouping `(a + b)` or a prefix call `(len xs)` |
| `identifier` | Names, special forms and operators: `x`, `list-push`, `$result`, `@`, `+`, `->`, `...` |
| `type_name` | Capitalized names: `Int`, `Result`, `MAX_CONN` |
| `number` | `42`, `-7`, `3.14`, `1.5e-3` |
| `string` | `"text"` with escapes |
| `quoted_symbol` | `'red`, `'Fizz` |
| `boolean` | `true`, `false` |
| `nil` | `nil` |
| `annotation` | `@intent`, `@spec`, `@pre`, `@post`, `@callback-assume`, ... |
| `keyword` | `:complexity`, `:c-name`, `:arena`, ... |
| `range_dots` | `..` in range types: `(Int 0 .. 9)`, `(Int 0..9)` |
| `comment` | `; ...` to end of line |

## Highlighting

The grammar includes queries for:

- **highlights.scm** - Syntax highlighting
- **locals.scm** - Local scopes and definitions
- **indents.scm** - Automatic indentation

The tree-sitter CLI, Neovim, Zed and Helix (25.07+) all let the last matching
pattern win, so `highlights.scm` lists its catch-all rules first and the
specific rules after them.

### Highlight Groups

| Node | Highlight Group |
|------|----------------|
| `identifier` heading a list, special form (`fn`, `let`, `match`, ...) | `@keyword` |
| `identifier` heading a list or infix call, built-in (`+`, `list-push`, ...) | `@operator` |
| `identifier` after `fn` | `@function` |
| `type_name` after `type` | `@type.definition` |
| `identifier` or `type_name` after `const` | `@constant` |
| `identifier` after `module` | `@module` |
| `identifier` starting with `$` (`$result`) | `@variable.builtin` |
| other `identifier` | `@variable` |
| other `type_name` | `@type` |
| `annotation` | `@attribute` |
| `keyword` | `@property` |
| `number` | `@number` |
| `string` | `@string` |
| `comment` | `@comment` |
| `quoted_symbol` | `@constant` |
| `boolean`, `nil` | `@constant.builtin` |
| `range_dots`, infix operators | `@operator` |
| infix `and`, `or`, `not` | `@keyword.operator` |

## SLOP Syntax Overview

```slop
; Comments start with semicolon

; Module definition
(module my-module
  (export greet validate))

; Type definitions
(type Age (Int 0 .. 150))
(type User (record (name String) (age Age)))
(type Status (enum active inactive))

; Function with contracts
(fn greet ((arena Arena) (name String))
  (@intent "Greet a user by name")
  (@spec ((Arena String) -> String))
  (@pre {(string-len name) > 0})
  (@post {(string-len $result) > (string-len name)})
  (string-concat arena "Hello, " name))

; Holes for LLM generation
(fn validate ((user User))
  (hole Bool "Check if user is valid"
    :complexity tier-1
    :required (user)))
```
