#include "../runtime/slop_runtime.h"
#include "slop_parser.h"

#define parser_PREC_OR (1)
#define parser_PREC_AND (2)
#define parser_PREC_COMPARE (3)
#define parser_PREC_ADD (4)
#define parser_PREC_MUL (5)
#define parser_PREC_UNARY (6)

uint8_t parser_string_contains_dot(slop_string s);
slop_string parser_string_copy(slop_arena* arena, slop_string s);
parser_LexerState parser_lexer_new(slop_string source);
uint8_t parser_lexer_at_end(parser_LexerState* state);
strlib_AsciiChar parser_lexer_peek(parser_LexerState* state);
strlib_AsciiChar parser_lexer_peek_next(parser_LexerState* state);
void parser_lexer_advance(parser_LexerState* state);
void parser_lexer_skip_whitespace(parser_LexerState* state);
void parser_lexer_skip_comment(parser_LexerState* state);
void parser_lexer_skip_whitespace_and_comments(parser_LexerState* state);
slop_result_parser_Token_parser_ParseError parser_lexer_read_string(slop_arena* arena, parser_LexerState* state);
slop_result_parser_Token_parser_ParseError parser_lexer_read_number(slop_arena* arena, parser_LexerState* state);
parser_Token parser_lexer_read_symbol(slop_arena* arena, parser_LexerState* state);
parser_Token parser_lexer_read_operator(slop_arena* arena, parser_LexerState* state);
slop_result_parser_Token_parser_ParseError parser_lexer_next_token(slop_arena* arena, parser_LexerState* state);
slop_result_list_parser_Token_parser_ParseError parser_tokenize(slop_arena* arena, slop_string source);
parser_ParserState parser_parser_new(slop_list_parser_Token tokens);
uint8_t parser_parser_at_end(parser_ParserState* state);
parser_Token parser_parser_peek(parser_ParserState* state);
void parser_parser_advance(parser_ParserState* state);
slop_result_parser_Token_parser_ParseError parser_parser_expect(parser_ParserState* state, parser_TokenType expected);
slop_result_types_SExpr_ptr_parser_ParseError parser_parse_expr(slop_arena* arena, parser_ParserState* state);
slop_result_types_SExpr_ptr_parser_ParseError parser_parse_list(slop_arena* arena, parser_ParserState* state);
int64_t parser_get_precedence(slop_string op);
slop_result_types_SExpr_ptr_parser_ParseError parser_parse_infix_primary(slop_arena* arena, parser_ParserState* state);
slop_result_types_SExpr_ptr_parser_ParseError parser_parse_infix_prec(slop_arena* arena, parser_ParserState* state, int64_t min_prec);
slop_result_types_SExpr_ptr_parser_ParseError parser_parse_infix(slop_arena* arena, parser_ParserState* state);
slop_result_list_types_SExpr_ptr_parser_ParseError parser_parse(slop_arena* arena, slop_string source);
int64_t parser_sexpr_line(types_SExpr* expr);
int64_t parser_sexpr_col(types_SExpr* expr);
uint8_t parser_sexpr_is_symbol_with_name(types_SExpr* expr, slop_string name);
uint8_t parser_is_form(types_SExpr* expr, slop_string keyword);
int64_t parser_sexpr_list_len(types_SExpr* expr);
slop_option_types_SExpr_ptr parser_sexpr_list_get(types_SExpr* expr, int64_t index);
uint8_t parser_sexpr_is_list(types_SExpr* expr);
slop_string parser_sexpr_get_symbol_name(types_SExpr* expr);
slop_string parser_sexpr_symbol_name(types_SExpr* expr);
uint8_t parser_sexpr_is_symbol(types_SExpr* expr);
uint8_t parser_sexpr_is_number(types_SExpr* expr);
uint8_t parser_sexpr_is_string(types_SExpr* expr);
slop_string parser_sexpr_number_string(types_SExpr* expr);
slop_string parser_sexpr_string_value(types_SExpr* expr);
slop_list_types_SExpr_ptr parser_find_holes(slop_arena* arena, types_SExpr* expr);
slop_string parser_pretty_print(slop_arena* arena, types_SExpr* expr);
slop_string parser_json_escape_string(slop_arena* arena, slop_string s);
slop_string parser_json_print_list(slop_arena* arena, slop_list_types_SExpr_ptr items);
slop_string parser_json_print(slop_arena* arena, types_SExpr* expr);

uint8_t parser_string_contains_dot(slop_string s) {
    {
        __auto_type i = 0;
        __auto_type slen = ((int64_t)(s.len));
        __auto_type found = 0;
        while (((i < slen) && !(found))) {
            if ((strlib_char_at(s, ((int64_t)(i))) == ((strlib_AsciiChar)(46)))) {
                found = 1;
            } else {
                i = (i + 1);
            }
        }
        return found;
    }
}

slop_string parser_string_copy(slop_arena* arena, slop_string s) {
    {
        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, (s.len + 1))));
        __auto_type i = 0;
        __auto_type slen = ((int64_t)(s.len));
        while ((i < slen)) {
            buf[i] = s.data[i];
            i = (i + 1);
        }
        buf[slen] = 0;
        return (slop_string){.len = s.len, .data = buf};
    }
}

parser_LexerState parser_lexer_new(slop_string source) {
    return (parser_LexerState){source, 0, 1, 1};
}

uint8_t parser_lexer_at_end(parser_LexerState* state) {
    return ((*state).pos >= ((int64_t)((*state).source.len)));
}

strlib_AsciiChar parser_lexer_peek(parser_LexerState* state) {
    if (parser_lexer_at_end(state)) {
        return ((strlib_AsciiChar)(0));
    } else {
        return strlib_char_at((*state).source, (*state).pos);
    }
}

strlib_AsciiChar parser_lexer_peek_next(parser_LexerState* state) {
    {
        __auto_type next_pos = ((*state).pos + 1);
        if ((next_pos >= ((int64_t)((*state).source.len)))) {
            return ((strlib_AsciiChar)(0));
        } else {
            return strlib_char_at((*state).source, next_pos);
        }
    }
}

void parser_lexer_advance(parser_LexerState* state) {
    SLOP_PRE((!(parser_lexer_at_end(state))), "(not (lexer-at-end state))");
    {
        __auto_type c = parser_lexer_peek(state);
        (*state).pos = ((*state).pos + 1);
        if ((c == 10)) {
            (*state).line = ((*state).line + 1);
            (*state).col = 1;
        } else {
            (*state).col = ((*state).col + 1);
        }
    }
}

void parser_lexer_skip_whitespace(parser_LexerState* state) {
    while ((!(parser_lexer_at_end(state)) && strlib_is_space(parser_lexer_peek(state)))) {
        parser_lexer_advance(state);
    }
}

void parser_lexer_skip_comment(parser_LexerState* state) {
    SLOP_PRE(((parser_lexer_peek(state) == 59)), "(== (lexer-peek state) 59)");
    while ((!(parser_lexer_at_end(state)) && (parser_lexer_peek(state) != 10))) {
        parser_lexer_advance(state);
    }
}

void parser_lexer_skip_whitespace_and_comments(parser_LexerState* state) {
    {
        __auto_type slop_continue = 1;
        while (slop_continue) {
            {
                __auto_type c = parser_lexer_peek(state);
                if (strlib_is_space(c)) {
                    parser_lexer_skip_whitespace(state);
                } else if ((c == 59)) {
                    parser_lexer_skip_comment(state);
                } else {
                    slop_continue = 0;
                }
            }
        }
    }
}

slop_result_parser_Token_parser_ParseError parser_lexer_read_string(slop_arena* arena, parser_LexerState* state) {
    SLOP_PRE(((parser_lexer_peek(state) == 34)), "(== (lexer-peek state) 34)");
    {
        __auto_type start_line = (*state).line;
        __auto_type start_col = (*state).col;
        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, 4096)));
        __auto_type buf_pos = 0;
        parser_lexer_advance(state);
        {
            __auto_type done = 0;
            __auto_type has_error = 0;
            while (((!(done)) && (!(has_error)) && (!(parser_lexer_at_end(state))))) {
                {
                    __auto_type c = parser_lexer_peek(state);
                    if ((c == 34)) {
                        parser_lexer_advance(state);
                        done = 1;
                    } else if ((c == 92)) {
                        parser_lexer_advance(state);
                        if (parser_lexer_at_end(state)) {
                            has_error = 1;
                        } else {
                            {
                                __auto_type next = parser_lexer_peek(state);
                                parser_lexer_advance(state);
                                if ((next == 110)) {
                                    buf[buf_pos] = ((uint8_t)(10));
                                    buf_pos = (buf_pos + 1);
                                } else if ((next == 116)) {
                                    buf[buf_pos] = ((uint8_t)(9));
                                    buf_pos = (buf_pos + 1);
                                } else if ((next == 114)) {
                                    buf[buf_pos] = ((uint8_t)(13));
                                    buf_pos = (buf_pos + 1);
                                } else if ((next == 34)) {
                                    buf[buf_pos] = ((uint8_t)(34));
                                    buf_pos = (buf_pos + 1);
                                } else if ((next == 92)) {
                                    buf[buf_pos] = ((uint8_t)(92));
                                    buf_pos = (buf_pos + 1);
                                } else {
                                    buf[buf_pos] = ((uint8_t)(92));
                                    buf_pos = (buf_pos + 1);
                                    buf[buf_pos] = ((uint8_t)(next));
                                    buf_pos = (buf_pos + 1);
                                }
                            }
                        }
                    } else {
                        buf[buf_pos] = ((uint8_t)(c));
                        buf_pos = (buf_pos + 1);
                        parser_lexer_advance(state);
                    }
                }
            }
            if ((!(done) && !(has_error))) {
                return ((slop_result_parser_Token_parser_ParseError){ .is_ok = false, .data.err = (parser_ParseError){SLOP_STR("Unterminated string"), start_line, start_col} });
            } else {
                if (has_error) {
                    return ((slop_result_parser_Token_parser_ParseError){ .is_ok = false, .data.err = (parser_ParseError){SLOP_STR("Invalid escape sequence"), start_line, start_col} });
                } else {
                    return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_string, (slop_string){.len = ((uint64_t)(buf_pos)), .data = buf}, start_line, start_col} });
                }
            }
        }
    }
}

slop_result_parser_Token_parser_ParseError parser_lexer_read_number(slop_arena* arena, parser_LexerState* state) {
    SLOP_PRE(((strlib_is_digit(parser_lexer_peek(state)) || ((parser_lexer_peek(state) == 45) && strlib_is_digit(parser_lexer_peek_next(state))))), "(or (is-digit (lexer-peek state)) (and (== (lexer-peek state) 45) (is-digit (lexer-peek-next state))))");
    {
        __auto_type start_line = (*state).line;
        __auto_type start_col = (*state).col;
        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, 64)));
        __auto_type buf_pos = 0;
        if ((parser_lexer_peek(state) == 45)) {
            buf[buf_pos] = ((uint8_t)(45));
            buf_pos = (buf_pos + 1);
            parser_lexer_advance(state);
        }
        while ((!(parser_lexer_at_end(state)) && strlib_is_digit(parser_lexer_peek(state)))) {
            buf[buf_pos] = ((uint8_t)(parser_lexer_peek(state)));
            buf_pos = (buf_pos + 1);
            parser_lexer_advance(state);
        }
        if (((!(parser_lexer_at_end(state))) && ((parser_lexer_peek(state) == 46)) && (strlib_is_digit(parser_lexer_peek_next(state))))) {
            buf[buf_pos] = ((uint8_t)(46));
            buf_pos = (buf_pos + 1);
            parser_lexer_advance(state);
            while ((!(parser_lexer_at_end(state)) && strlib_is_digit(parser_lexer_peek(state)))) {
                buf[buf_pos] = ((uint8_t)(parser_lexer_peek(state)));
                buf_pos = (buf_pos + 1);
                parser_lexer_advance(state);
            }
        }
        return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_number, (slop_string){.len = ((uint64_t)(buf_pos)), .data = buf}, start_line, start_col} });
    }
}

parser_Token parser_lexer_read_symbol(slop_arena* arena, parser_LexerState* state) {
    SLOP_PRE((strlib_char_is_symbol_start(parser_lexer_peek(state))), "(char-is-symbol-start (lexer-peek state))");
    {
        __auto_type start_line = (*state).line;
        __auto_type start_col = (*state).col;
        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, 256)));
        __auto_type buf_pos = 0;
        while ((!(parser_lexer_at_end(state)) && strlib_char_is_symbol_char(parser_lexer_peek(state)))) {
            buf[buf_pos] = ((uint8_t)(parser_lexer_peek(state)));
            buf_pos = (buf_pos + 1);
            parser_lexer_advance(state);
        }
        return (parser_Token){parser_TokenType_tok_symbol, (slop_string){.len = ((uint64_t)(buf_pos)), .data = buf}, start_line, start_col};
    }
}

parser_Token parser_lexer_read_operator(slop_arena* arena, parser_LexerState* state) {
    SLOP_PRE((strlib_char_is_operator(parser_lexer_peek(state))), "(char-is-operator (lexer-peek state))");
    {
        __auto_type start_line = (*state).line;
        __auto_type start_col = (*state).col;
        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, 16)));
        __auto_type buf_pos = 0;
        while ((!(parser_lexer_at_end(state)) && strlib_char_is_operator(parser_lexer_peek(state)))) {
            buf[buf_pos] = ((uint8_t)(parser_lexer_peek(state)));
            buf_pos = (buf_pos + 1);
            parser_lexer_advance(state);
        }
        return (parser_Token){parser_TokenType_tok_operator, (slop_string){.len = ((uint64_t)(buf_pos)), .data = buf}, start_line, start_col};
    }
}

slop_result_parser_Token_parser_ParseError parser_lexer_next_token(slop_arena* arena, parser_LexerState* state) {
    parser_lexer_skip_whitespace_and_comments(state);
    {
        __auto_type line = (*state).line;
        __auto_type col = (*state).col;
        __auto_type c = parser_lexer_peek(state);
        if ((c == 0)) {
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_eof, SLOP_STR(""), line, col} });
        } else if ((c == 40)) {
            parser_lexer_advance(state);
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_lparen, SLOP_STR("("), line, col} });
        } else if ((c == 41)) {
            parser_lexer_advance(state);
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_rparen, SLOP_STR(")"), line, col} });
        } else if ((c == 123)) {
            parser_lexer_advance(state);
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_lbrace, SLOP_STR("{"), line, col} });
        } else if ((c == 125)) {
            parser_lexer_advance(state);
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_rbrace, SLOP_STR("}"), line, col} });
        } else if ((c == 39)) {
            parser_lexer_advance(state);
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_quote, SLOP_STR("'"), line, col} });
        } else if ((c == 58)) {
            parser_lexer_advance(state);
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_colon, SLOP_STR(":"), line, col} });
        } else if ((c == 34)) {
            return parser_lexer_read_string(arena, state);
        } else if ((strlib_is_digit(c) || ((c == 45) && strlib_is_digit(parser_lexer_peek_next(state))))) {
            return parser_lexer_read_number(arena, state);
        } else if (strlib_char_is_symbol_start(c)) {
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = parser_lexer_read_symbol(arena, state) });
        } else if ((c == 46)) {
            if ((parser_lexer_peek_next(state) == 46)) {
                parser_lexer_advance(state);
                parser_lexer_advance(state);
                return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = (parser_Token){parser_TokenType_tok_range, SLOP_STR(".."), line, col} });
            } else {
                return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = parser_lexer_read_operator(arena, state) });
            }
        } else if (strlib_char_is_operator(c)) {
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = parser_lexer_read_operator(arena, state) });
        } else {
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = false, .data.err = (parser_ParseError){SLOP_STR("Unexpected character"), line, col} });
        }
    }
}

slop_result_list_parser_Token_parser_ParseError parser_tokenize(slop_arena* arena, slop_string source) {
    {
        __auto_type state = parser_lexer_new(source);
        __auto_type tokens = ((slop_list_parser_Token){ .data = (parser_Token*)slop_arena_alloc(arena, 16 * sizeof(parser_Token)), .len = 0, .cap = 16 });
        __auto_type done = 0;
        __auto_type has_error = 0;
        __auto_type error_val = (parser_ParseError){SLOP_STR(""), 0, 0};
        while ((!(done) && !(has_error))) {
            __auto_type _mv_644 = parser_lexer_next_token(arena, (&state));
            if (_mv_644.is_ok) {
                __auto_type tok = _mv_644.data.ok;
                ({ __auto_type _lst_p = &(tokens); __auto_type _item = (tok); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                if ((tok.kind == parser_TokenType_tok_eof)) {
                    done = 1;
                }
            } else if (!_mv_644.is_ok) {
                __auto_type e = _mv_644.data.err;
                has_error = 1;
                error_val = e;
            }
        }
        if (has_error) {
            return ((slop_result_list_parser_Token_parser_ParseError){ .is_ok = false, .data.err = error_val });
        } else {
            return ((slop_result_list_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = tokens });
        }
    }
}

parser_ParserState parser_parser_new(slop_list_parser_Token tokens) {
    return (parser_ParserState){tokens, 0, 0};
}

uint8_t parser_parser_at_end(parser_ParserState* state) {
    return ((*state).pos >= ((int64_t)(((*state).tokens).len)));
}

parser_Token parser_parser_peek(parser_ParserState* state) {
    __auto_type _mv_645 = ({ __auto_type _lst = (*state).tokens; size_t _idx = (size_t)(*state).pos; slop_option_parser_Token _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_645.has_value) {
        __auto_type tok = _mv_645.value;
        return tok;
    } else if (!_mv_645.has_value) {
        return (parser_Token){parser_TokenType_tok_eof, SLOP_STR(""), 1, 1};
    }
}

void parser_parser_advance(parser_ParserState* state) {
    SLOP_PRE((!(parser_parser_at_end(state))), "(not (parser-at-end state))");
    (*state).pos = ((*state).pos + 1);
}

slop_result_parser_Token_parser_ParseError parser_parser_expect(parser_ParserState* state, parser_TokenType expected) {
    {
        __auto_type tok = parser_parser_peek(state);
        if ((tok.kind == expected)) {
            parser_parser_advance(state);
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = true, .data.ok = tok });
        } else {
            return ((slop_result_parser_Token_parser_ParseError){ .is_ok = false, .data.err = (parser_ParseError){SLOP_STR("Unexpected token"), tok.line, tok.col} });
        }
    }
}

slop_result_types_SExpr_ptr_parser_ParseError parser_parse_expr(slop_arena* arena, parser_ParserState* state) {
    {
        __auto_type tok = parser_parser_peek(state);
        if ((tok.kind == parser_TokenType_tok_lparen)) {
            return parser_parse_list(arena, state);
        } else if ((tok.kind == parser_TokenType_tok_lbrace)) {
            return parser_parse_infix(arena, state);
        } else if ((tok.kind == parser_TokenType_tok_number)) {
            parser_parser_advance(state);
            {
                __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                __auto_type is_float = parser_string_contains_dot(tok.value);
                if (is_float) {
                    (*node) = ((types_SExpr){ .tag = types_SExpr_num, .data.num = (types_SExprNumber){0, strtod(((char*)(tok.value.data)), ((char**)(0))), 1, tok.value, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                } else {
                    (*node) = ((types_SExpr){ .tag = types_SExpr_num, .data.num = (types_SExprNumber){strtoll(((char*)(tok.value.data)), ((char**)(0)), 10), 0.0, 0, tok.value, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                }
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
            }
        } else if ((tok.kind == parser_TokenType_tok_string)) {
            parser_parser_advance(state);
            {
                __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                (*node) = ((types_SExpr){ .tag = types_SExpr_str, .data.str = (types_SExprString){tok.value, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
            }
        } else if ((tok.kind == parser_TokenType_tok_quote)) {
            parser_parser_advance(state);
            __auto_type _mv_646 = parser_parse_expr(arena, state);
            if (_mv_646.is_ok) {
                __auto_type quoted_expr = _mv_646.data.ok;
                {
                    __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                    __auto_type quote_sym = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                    __auto_type items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                    (*quote_sym) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){SLOP_STR("quote"), tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                    ({ __auto_type _lst_p = &(items); __auto_type _item = (quote_sym); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(items); __auto_type _item = (quoted_expr); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    (*node) = ((types_SExpr){ .tag = types_SExpr_lst, .data.lst = (types_SExprList){items, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                    return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
                }
            } else if (!_mv_646.is_ok) {
                __auto_type e = _mv_646.data.err;
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = e });
            }
        } else if ((tok.kind == parser_TokenType_tok_symbol)) {
            parser_parser_advance(state);
            {
                __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                (*node) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){tok.value, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
            }
        } else if ((tok.kind == parser_TokenType_tok_operator)) {
            parser_parser_advance(state);
            {
                __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                (*node) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){tok.value, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
            }
        } else if ((tok.kind == parser_TokenType_tok_colon)) {
            parser_parser_advance(state);
            {
                __auto_type next_tok = parser_parser_peek(state);
                if ((next_tok.kind == parser_TokenType_tok_symbol)) {
                    parser_parser_advance(state);
                    {
                        __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                        __auto_type kw_buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, 256)));
                        kw_buf[0] = ((uint8_t)(58));
                        {
                            __auto_type i = 0;
                            __auto_type slen = ((int64_t)(next_tok.value.len));
                            while ((i < slen)) {
                                kw_buf[(i + 1)] = next_tok.value.data[i];
                                i = (i + 1);
                            }
                            (*node) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){(slop_string){.len = ((uint64_t)((slen + 1))), .data = kw_buf}, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                            return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
                        }
                    }
                } else {
                    return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = (parser_ParseError){SLOP_STR("Expected symbol after :"), tok.line, tok.col} });
                }
            }
        } else if ((tok.kind == parser_TokenType_tok_range)) {
            parser_parser_advance(state);
            {
                __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                (*node) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){SLOP_STR(".."), tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
            }
        } else {
            return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = (parser_ParseError){SLOP_STR("Unexpected token"), tok.line, tok.col} });
        }
    }
}

slop_result_types_SExpr_ptr_parser_ParseError parser_parse_list(slop_arena* arena, parser_ParserState* state) {
    SLOP_PRE(((parser_parser_peek(state).kind == parser_TokenType_tok_lparen)), "(== (. (parser-peek state) kind) (quote tok-lparen))");
    {
        __auto_type start_tok = parser_parser_peek(state);
        parser_parser_advance(state);
        {
            __auto_type items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
            __auto_type done = 0;
            __auto_type has_error = 0;
            __auto_type error_val = (parser_ParseError){SLOP_STR(""), 0, 0};
            while ((!(done) && !(has_error))) {
                {
                    __auto_type tok = parser_parser_peek(state);
                    if ((tok.kind == parser_TokenType_tok_rparen)) {
                        parser_parser_advance(state);
                        done = 1;
                    } else if ((tok.kind == parser_TokenType_tok_eof)) {
                        has_error = 1;
                        error_val = (parser_ParseError){SLOP_STR("Unterminated list"), start_tok.line, start_tok.col};
                    } else {
                        __auto_type _mv_647 = parser_parse_expr(arena, state);
                        if (_mv_647.is_ok) {
                            __auto_type expr = _mv_647.data.ok;
                            ({ __auto_type _lst_p = &(items); __auto_type _item = (expr); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        } else if (!_mv_647.is_ok) {
                            __auto_type e = _mv_647.data.err;
                            has_error = 1;
                            error_val = e;
                        }
                    }
                }
            }
            if (has_error) {
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = error_val });
            } else {
                {
                    __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                    (*node) = ((types_SExpr){ .tag = types_SExpr_lst, .data.lst = (types_SExprList){items, start_tok.line, start_tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                    return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
                }
            }
        }
    }
}

int64_t parser_get_precedence(slop_string op) {
    if (string_eq(op, SLOP_STR("or"))) {
        return parser_PREC_OR;
    } else if (string_eq(op, SLOP_STR("and"))) {
        return parser_PREC_AND;
    } else if (string_eq(op, SLOP_STR("=="))) {
        return parser_PREC_COMPARE;
    } else if (string_eq(op, SLOP_STR("!="))) {
        return parser_PREC_COMPARE;
    } else if (string_eq(op, SLOP_STR("<"))) {
        return parser_PREC_COMPARE;
    } else if (string_eq(op, SLOP_STR(">"))) {
        return parser_PREC_COMPARE;
    } else if (string_eq(op, SLOP_STR("<="))) {
        return parser_PREC_COMPARE;
    } else if (string_eq(op, SLOP_STR(">="))) {
        return parser_PREC_COMPARE;
    } else if (string_eq(op, SLOP_STR("+"))) {
        return parser_PREC_ADD;
    } else if (string_eq(op, SLOP_STR("-"))) {
        return parser_PREC_ADD;
    } else if (string_eq(op, SLOP_STR("*"))) {
        return parser_PREC_MUL;
    } else if (string_eq(op, SLOP_STR("/"))) {
        return parser_PREC_MUL;
    } else if (string_eq(op, SLOP_STR("%"))) {
        return parser_PREC_MUL;
    } else {
        return 0;
    }
}

slop_result_types_SExpr_ptr_parser_ParseError parser_parse_infix_primary(slop_arena* arena, parser_ParserState* state) {
    {
        __auto_type tok = parser_parser_peek(state);
        if ((tok.kind == parser_TokenType_tok_number)) {
            parser_parser_advance(state);
            {
                __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                if (parser_string_contains_dot(tok.value)) {
                    (*node) = ((types_SExpr){ .tag = types_SExpr_num, .data.num = (types_SExprNumber){0, strtod(((char*)(tok.value.data)), ((char**)(0))), 1, tok.value, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                } else {
                    (*node) = ((types_SExpr){ .tag = types_SExpr_num, .data.num = (types_SExprNumber){strtoll(((char*)(tok.value.data)), ((char**)(0)), 10), 0.0, 0, tok.value, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                }
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
            }
        } else if ((tok.kind == parser_TokenType_tok_symbol)) {
            if (string_eq(tok.value, SLOP_STR("not"))) {
                parser_parser_advance(state);
                __auto_type _mv_648 = parser_parse_infix_primary(arena, state);
                if (!_mv_648.is_ok) {
                    __auto_type e = _mv_648.data.err;
                    return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = e });
                } else if (_mv_648.is_ok) {
                    __auto_type operand = _mv_648.data.ok;
                    {
                        __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                        __auto_type not_sym = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                        __auto_type items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                        (*not_sym) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){SLOP_STR("not"), tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                        ({ __auto_type _lst_p = &(items); __auto_type _item = (not_sym); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(items); __auto_type _item = (operand); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        (*node) = ((types_SExpr){ .tag = types_SExpr_lst, .data.lst = (types_SExprList){items, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                        return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
                    }
                }
            } else {
                parser_parser_advance(state);
                {
                    __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                    (*node) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){tok.value, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                    return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
                }
            }
        } else if (((tok.kind == parser_TokenType_tok_operator) && string_eq(tok.value, SLOP_STR("-")))) {
            parser_parser_advance(state);
            __auto_type _mv_649 = parser_parse_infix_primary(arena, state);
            if (!_mv_649.is_ok) {
                __auto_type e = _mv_649.data.err;
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = e });
            } else if (_mv_649.is_ok) {
                __auto_type operand = _mv_649.data.ok;
                {
                    __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                    __auto_type minus_sym = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                    __auto_type zero_node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                    __auto_type items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                    (*minus_sym) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){SLOP_STR("-"), tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                    (*zero_node) = ((types_SExpr){ .tag = types_SExpr_num, .data.num = (types_SExprNumber){0, 0.0, 0, SLOP_STR("0"), tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                    ({ __auto_type _lst_p = &(items); __auto_type _item = (minus_sym); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(items); __auto_type _item = (zero_node); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(items); __auto_type _item = (operand); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    (*node) = ((types_SExpr){ .tag = types_SExpr_lst, .data.lst = (types_SExprList){items, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                    return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
                }
            }
        } else if ((tok.kind == parser_TokenType_tok_operator)) {
            return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = (parser_ParseError){SLOP_STR("Unexpected operator in expression"), tok.line, tok.col} });
        } else if ((tok.kind == parser_TokenType_tok_lparen)) {
            return parser_parse_list(arena, state);
        } else if ((tok.kind == parser_TokenType_tok_quote)) {
            parser_parser_advance(state);
            __auto_type _mv_650 = parser_parse_infix_primary(arena, state);
            if (!_mv_650.is_ok) {
                __auto_type e = _mv_650.data.err;
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = e });
            } else if (_mv_650.is_ok) {
                __auto_type quoted_expr = _mv_650.data.ok;
                {
                    __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                    __auto_type quote_sym = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                    __auto_type items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                    (*quote_sym) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){SLOP_STR("quote"), tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                    ({ __auto_type _lst_p = &(items); __auto_type _item = (quote_sym); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(items); __auto_type _item = (quoted_expr); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    (*node) = ((types_SExpr){ .tag = types_SExpr_lst, .data.lst = (types_SExprList){items, tok.line, tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                    return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = node });
                }
            }
        } else {
            return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = (parser_ParseError){SLOP_STR("Expected expression in infix"), tok.line, tok.col} });
        }
    }
}

slop_result_types_SExpr_ptr_parser_ParseError parser_parse_infix_prec(slop_arena* arena, parser_ParserState* state, int64_t min_prec) {
    __auto_type _mv_651 = parser_parse_infix_primary(arena, state);
    if (!_mv_651.is_ok) {
        __auto_type e = _mv_651.data.err;
        return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = e });
    } else if (_mv_651.is_ok) {
        __auto_type left = _mv_651.data.ok;
        {
            __auto_type result = left;
            __auto_type done = 0;
            __auto_type has_error = 0;
            __auto_type error_val = (parser_ParseError){SLOP_STR(""), 0, 0};
            while ((!(done) && !(has_error))) {
                {
                    __auto_type tok = parser_parser_peek(state);
                    if (((tok.kind == parser_TokenType_tok_operator) || ((tok.kind == parser_TokenType_tok_symbol) && (string_eq(tok.value, SLOP_STR("and")) || string_eq(tok.value, SLOP_STR("or")))))) {
                        {
                            __auto_type op_prec = parser_get_precedence(tok.value);
                            if ((op_prec < min_prec)) {
                                done = 1;
                            } else {
                                {
                                    __auto_type op_tok = tok;
                                    parser_parser_advance(state);
                                    __auto_type _mv_652 = parser_parse_infix_prec(arena, state, (op_prec + 1));
                                    if (!_mv_652.is_ok) {
                                        __auto_type e = _mv_652.data.err;
                                        has_error = 1;
                                        error_val = e;
                                    } else if (_mv_652.is_ok) {
                                        __auto_type right = _mv_652.data.ok;
                                        {
                                            __auto_type node = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                                            __auto_type op_sym = ((types_SExpr*)((uint8_t*)slop_arena_alloc(arena, 128)));
                                            __auto_type items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                                            (*op_sym) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){op_tok.value, op_tok.line, op_tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                                            ({ __auto_type _lst_p = &(items); __auto_type _item = (op_sym); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                            ({ __auto_type _lst_p = &(items); __auto_type _item = (result); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                            ({ __auto_type _lst_p = &(items); __auto_type _item = (right); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                            (*node) = ((types_SExpr){ .tag = types_SExpr_lst, .data.lst = (types_SExprList){items, op_tok.line, op_tok.col, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                                            result = node;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        done = 1;
                    }
                }
            }
            if (has_error) {
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = error_val });
            } else {
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = result });
            }
        }
    }
}

slop_result_types_SExpr_ptr_parser_ParseError parser_parse_infix(slop_arena* arena, parser_ParserState* state) {
    SLOP_PRE(((parser_parser_peek(state).kind == parser_TokenType_tok_lbrace)), "(== (. (parser-peek state) kind) (quote tok-lbrace))");
    {
        __auto_type start_tok = parser_parser_peek(state);
        parser_parser_advance(state);
        (*state).in_infix = 1;
        {
            __auto_type result = parser_parse_infix_prec(arena, state, 0);
            (*state).in_infix = 0;
            __auto_type _mv_653 = result;
            if (!_mv_653.is_ok) {
                __auto_type e = _mv_653.data.err;
                return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = e });
            } else if (_mv_653.is_ok) {
                __auto_type expr = _mv_653.data.ok;
                {
                    __auto_type tok = parser_parser_peek(state);
                    if ((tok.kind == parser_TokenType_tok_rbrace)) {
                        parser_parser_advance(state);
                        return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = expr });
                    } else {
                        return ((slop_result_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = (parser_ParseError){SLOP_STR("Expected '}' to close infix expression"), tok.line, tok.col} });
                    }
                }
            }
        }
    }
}

slop_result_list_types_SExpr_ptr_parser_ParseError parser_parse(slop_arena* arena, slop_string source) {
    __auto_type _mv_654 = parser_tokenize(arena, source);
    if (_mv_654.is_ok) {
        __auto_type tokens = _mv_654.data.ok;
        {
            __auto_type state = parser_parser_new(tokens);
            __auto_type result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
            __auto_type done = 0;
            __auto_type has_error = 0;
            __auto_type error_val = (parser_ParseError){SLOP_STR(""), 0, 0};
            while ((!(done) && !(has_error))) {
                {
                    __auto_type tok = parser_parser_peek((&state));
                    if ((tok.kind == parser_TokenType_tok_eof)) {
                        done = 1;
                    } else {
                        __auto_type _mv_655 = parser_parse_expr(arena, (&state));
                        if (_mv_655.is_ok) {
                            __auto_type expr = _mv_655.data.ok;
                            ({ __auto_type _lst_p = &(result); __auto_type _item = (expr); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        } else if (!_mv_655.is_ok) {
                            __auto_type e = _mv_655.data.err;
                            has_error = 1;
                            error_val = e;
                        }
                    }
                }
            }
            if (has_error) {
                return ((slop_result_list_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = error_val });
            } else {
                return ((slop_result_list_types_SExpr_ptr_parser_ParseError){ .is_ok = true, .data.ok = result });
            }
        }
    } else if (!_mv_654.is_ok) {
        __auto_type e = _mv_654.data.err;
        return ((slop_result_list_types_SExpr_ptr_parser_ParseError){ .is_ok = false, .data.err = e });
    }
}

int64_t parser_sexpr_line(types_SExpr* expr) {
    __auto_type _mv_656 = (*expr);
    switch (_mv_656.tag) {
        case types_SExpr_sym:
        {
            __auto_type s = _mv_656.data.sym;
            return s.line;
        }
        case types_SExpr_str:
        {
            __auto_type s = _mv_656.data.str;
            return s.line;
        }
        case types_SExpr_num:
        {
            __auto_type n = _mv_656.data.num;
            return n.line;
        }
        case types_SExpr_lst:
        {
            __auto_type l = _mv_656.data.lst;
            return l.line;
        }
    }
}

int64_t parser_sexpr_col(types_SExpr* expr) {
    __auto_type _mv_657 = (*expr);
    switch (_mv_657.tag) {
        case types_SExpr_sym:
        {
            __auto_type s = _mv_657.data.sym;
            return s.col;
        }
        case types_SExpr_str:
        {
            __auto_type s = _mv_657.data.str;
            return s.col;
        }
        case types_SExpr_num:
        {
            __auto_type n = _mv_657.data.num;
            return n.col;
        }
        case types_SExpr_lst:
        {
            __auto_type l = _mv_657.data.lst;
            return l.col;
        }
    }
}

uint8_t parser_sexpr_is_symbol_with_name(types_SExpr* expr, slop_string name) {
    __auto_type _mv_658 = (*expr);
    switch (_mv_658.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_658.data.sym;
            return string_eq(sym.name, name);
        }
        default: {
            return 0;
        }
    }
}

uint8_t parser_is_form(types_SExpr* expr, slop_string keyword) {
    __auto_type _mv_659 = (*expr);
    switch (_mv_659.tag) {
        case types_SExpr_lst:
        {
            __auto_type l = _mv_659.data.lst;
            if ((((int64_t)((l.items).len)) == 0)) {
                return 0;
            } else {
                __auto_type _mv_660 = ({ __auto_type _lst = l.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_660.has_value) {
                    __auto_type first = _mv_660.value;
                    return parser_sexpr_is_symbol_with_name(first, keyword);
                } else if (!_mv_660.has_value) {
                    return 0;
                }
            }
        }
        default: {
            return 0;
        }
    }
}

int64_t parser_sexpr_list_len(types_SExpr* expr) {
    __auto_type _mv_661 = (*expr);
    switch (_mv_661.tag) {
        case types_SExpr_lst:
        {
            __auto_type l = _mv_661.data.lst;
            return ((int64_t)((l.items).len));
        }
        default: {
            return 0;
        }
    }
}

slop_option_types_SExpr_ptr parser_sexpr_list_get(types_SExpr* expr, int64_t index) {
    __auto_type _mv_662 = (*expr);
    switch (_mv_662.tag) {
        case types_SExpr_lst:
        {
            __auto_type l = _mv_662.data.lst;
            return ({ __auto_type _lst = l.items; size_t _idx = (size_t)index; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        }
        default: {
            return (slop_option_types_SExpr_ptr){.has_value = false};
        }
    }
}

uint8_t parser_sexpr_is_list(types_SExpr* expr) {
    __auto_type _mv_663 = (*expr);
    switch (_mv_663.tag) {
        case types_SExpr_lst:
        {
            __auto_type l = _mv_663.data.lst;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

slop_string parser_sexpr_get_symbol_name(types_SExpr* expr) {
    __auto_type _mv_664 = (*expr);
    switch (_mv_664.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_664.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_string parser_sexpr_symbol_name(types_SExpr* expr) {
    return parser_sexpr_get_symbol_name(expr);
}

uint8_t parser_sexpr_is_symbol(types_SExpr* expr) {
    __auto_type _mv_665 = (*expr);
    switch (_mv_665.tag) {
        case types_SExpr_sym:
        {
            __auto_type s = _mv_665.data.sym;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

uint8_t parser_sexpr_is_number(types_SExpr* expr) {
    __auto_type _mv_666 = (*expr);
    switch (_mv_666.tag) {
        case types_SExpr_num:
        {
            __auto_type n = _mv_666.data.num;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

uint8_t parser_sexpr_is_string(types_SExpr* expr) {
    __auto_type _mv_667 = (*expr);
    switch (_mv_667.tag) {
        case types_SExpr_str:
        {
            __auto_type s = _mv_667.data.str;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

slop_string parser_sexpr_number_string(types_SExpr* expr) {
    __auto_type _mv_668 = (*expr);
    switch (_mv_668.tag) {
        case types_SExpr_num:
        {
            __auto_type n = _mv_668.data.num;
            return n.raw;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_string parser_sexpr_string_value(types_SExpr* expr) {
    __auto_type _mv_669 = (*expr);
    switch (_mv_669.tag) {
        case types_SExpr_str:
        {
            __auto_type s = _mv_669.data.str;
            return s.value;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_list_types_SExpr_ptr parser_find_holes(slop_arena* arena, types_SExpr* expr) {
    {
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
        if (parser_is_form(expr, SLOP_STR("hole"))) {
            ({ __auto_type _lst_p = &(result); __auto_type _item = (expr); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        }
        __auto_type _mv_670 = (*expr);
        switch (_mv_670.tag) {
            case types_SExpr_lst:
            {
                __auto_type l = _mv_670.data.lst;
                {
                    __auto_type items = l.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type i = 0;
                    while ((i < len)) {
                        __auto_type _mv_671 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_671.has_value) {
                            __auto_type child = _mv_671.value;
                            {
                                __auto_type child_holes = parser_find_holes(arena, child);
                                __auto_type child_len = ((int64_t)((child_holes).len));
                                __auto_type j = 0;
                                while ((j < child_len)) {
                                    __auto_type _mv_672 = ({ __auto_type _lst = child_holes; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_672.has_value) {
                                        __auto_type h = _mv_672.value;
                                        ({ __auto_type _lst_p = &(result); __auto_type _item = (h); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    } else if (!_mv_672.has_value) {
                                    }
                                    j = (j + 1);
                                }
                            }
                        } else if (!_mv_671.has_value) {
                        }
                        i = (i + 1);
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
        return result;
    }
}

slop_string parser_pretty_print(slop_arena* arena, types_SExpr* expr) {
    __auto_type _mv_673 = (*expr);
    switch (_mv_673.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_673.data.sym;
            return parser_string_copy(arena, sym.name);
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_673.data.str;
            {
                __auto_type val = str.value;
                __auto_type slen = ((int64_t)(val.len));
                __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, ((slen * 2) + 3))));
                __auto_type i = 0;
                __auto_type out = 1;
                buf[0] = 34;
                while ((i < slen)) {
                    {
                        __auto_type c = val.data[i];
                        if ((c == 10)) {
                            buf[out] = 92;
                            buf[(out + 1)] = 110;
                            out = (out + 2);
                        } else if ((c == 9)) {
                            buf[out] = 92;
                            buf[(out + 1)] = 116;
                            out = (out + 2);
                        } else if ((c == 34)) {
                            buf[out] = 92;
                            buf[(out + 1)] = 34;
                            out = (out + 2);
                        } else if ((c == 92)) {
                            buf[out] = 92;
                            buf[(out + 1)] = 92;
                            out = (out + 2);
                        } else {
                            buf[out] = c;
                            out = (out + 1);
                        }
                    }
                    i = (i + 1);
                }
                buf[out] = 34;
                buf[(out + 1)] = 0;
                return (slop_string){.len = ((uint64_t)((out + 1))), .data = buf};
            }
        }
        case types_SExpr_num:
        {
            __auto_type num = _mv_673.data.num;
            if (num.is_float) {
                return parser_string_copy(arena, SLOP_STR("<float>"));
            } else {
                return int_to_string(arena, num.int_value);
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_673.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len == 0)) {
                    return parser_string_copy(arena, SLOP_STR("()"));
                } else {
                    {
                        __auto_type result = parser_string_copy(arena, SLOP_STR("("));
                        __auto_type i = 0;
                        while ((i < len)) {
                            __auto_type _mv_674 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_674.has_value) {
                                __auto_type child = _mv_674.value;
                                {
                                    __auto_type child_str = parser_pretty_print(arena, child);
                                    if ((i > 0)) {
                                        result = string_concat(arena, result, SLOP_STR(" "));
                                    }
                                    result = string_concat(arena, result, child_str);
                                }
                            } else if (!_mv_674.has_value) {
                            }
                            i = (i + 1);
                        }
                        return string_concat(arena, result, SLOP_STR(")"));
                    }
                }
            }
        }
    }
}

slop_string parser_json_escape_string(slop_arena* arena, slop_string s) {
    {
        __auto_type slen = ((int64_t)(s.len));
        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, ((slen * 2) + 3))));
        __auto_type i = 0;
        __auto_type out = 1;
        buf[0] = 34;
        while ((i < slen)) {
            {
                __auto_type c = s.data[i];
                if ((c == 34)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 34;
                    out = (out + 2);
                } else if ((c == 92)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 92;
                    out = (out + 2);
                } else if ((c == 10)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 110;
                    out = (out + 2);
                } else if ((c == 13)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 114;
                    out = (out + 2);
                } else if ((c == 9)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 116;
                    out = (out + 2);
                } else {
                    buf[out] = c;
                    out = (out + 1);
                }
            }
            i = (i + 1);
        }
        buf[out] = 34;
        return (slop_string){.len = ((uint64_t)((out + 1))), .data = buf};
    }
}

slop_string parser_json_print_list(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len == 0)) {
            return parser_string_copy(arena, SLOP_STR("[]"));
        } else {
            {
                __auto_type result = parser_string_copy(arena, SLOP_STR("["));
                __auto_type i = 0;
                while ((i < len)) {
                    __auto_type _mv_675 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_675.has_value) {
                        __auto_type child = _mv_675.value;
                        {
                            __auto_type child_json = parser_json_print(arena, child);
                            if ((i > 0)) {
                                result = string_concat(arena, result, SLOP_STR(","));
                            }
                            result = string_concat(arena, result, child_json);
                        }
                    } else if (!_mv_675.has_value) {
                    }
                    i = (i + 1);
                }
                return string_concat(arena, result, SLOP_STR("]"));
            }
        }
    }
}

slop_string parser_json_print(slop_arena* arena, types_SExpr* expr) {
    __auto_type _mv_676 = (*expr);
    switch (_mv_676.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_676.data.sym;
            {
                __auto_type escaped = parser_json_escape_string(arena, sym.name);
                __auto_type line_str = int_to_string(arena, sym.line);
                __auto_type col_str = int_to_string(arena, sym.col);
                return string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, SLOP_STR("{\"type\":\"Symbol\",\"name\":"), escaped), SLOP_STR(",\"line\":")), line_str), SLOP_STR(",\"col\":")), col_str), SLOP_STR("}"));
            }
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_676.data.str;
            {
                __auto_type escaped = parser_json_escape_string(arena, str.value);
                __auto_type line_str = int_to_string(arena, str.line);
                __auto_type col_str = int_to_string(arena, str.col);
                return string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, SLOP_STR("{\"type\":\"String\",\"value\":"), escaped), SLOP_STR(",\"line\":")), line_str), SLOP_STR(",\"col\":")), col_str), SLOP_STR("}"));
            }
        }
        case types_SExpr_num:
        {
            __auto_type num = _mv_676.data.num;
            {
                __auto_type line_str = int_to_string(arena, num.line);
                __auto_type col_str = int_to_string(arena, num.col);
                if (num.is_float) {
                    {
                        __auto_type val_str = strlib_float_to_string(arena, num.float_value, 15);
                        return string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, SLOP_STR("{\"type\":\"Number\",\"value\":"), val_str), SLOP_STR(",\"is_float\":true,\"line\":")), line_str), SLOP_STR(",\"col\":")), col_str), SLOP_STR("}"));
                    }
                } else {
                    {
                        __auto_type val_str = int_to_string(arena, num.int_value);
                        return string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, SLOP_STR("{\"type\":\"Number\",\"value\":"), val_str), SLOP_STR(",\"is_float\":false,\"line\":")), line_str), SLOP_STR(",\"col\":")), col_str), SLOP_STR("}"));
                    }
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_676.data.lst;
            {
                __auto_type items_json = parser_json_print_list(arena, lst.items);
                __auto_type line_str = int_to_string(arena, lst.line);
                __auto_type col_str = int_to_string(arena, lst.col);
                return string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, SLOP_STR("{\"type\":\"List\",\"items\":"), items_json), SLOP_STR(",\"line\":")), line_str), SLOP_STR(",\"col\":")), col_str), SLOP_STR("}"));
            }
        }
    }
}

