; SLOP indentation queries for tree-sitter

; Indent inside lists
(list) @indent

; Align closing paren with opening
")" @indent_end
