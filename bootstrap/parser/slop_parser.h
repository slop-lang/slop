#ifndef SLOP_parser_H
#define SLOP_parser_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_strlib.h"
#include <stdlib.h>

typedef struct parser_Token parser_Token;
typedef struct parser_ParseError parser_ParseError;
typedef struct parser_LexerState parser_LexerState;
typedef struct parser_ParserState parser_ParserState;

typedef enum {
    parser_TokenType_tok_lparen,
    parser_TokenType_tok_rparen,
    parser_TokenType_tok_lbrace,
    parser_TokenType_tok_rbrace,
    parser_TokenType_tok_quote,
    parser_TokenType_tok_colon,
    parser_TokenType_tok_range,
    parser_TokenType_tok_number,
    parser_TokenType_tok_string,
    parser_TokenType_tok_symbol,
    parser_TokenType_tok_operator,
    parser_TokenType_tok_eof
} parser_TokenType;

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

struct parser_Token {
    parser_TokenType kind;
    slop_string value;
    int64_t line;
    int64_t col;
};
typedef struct parser_Token parser_Token;

#ifndef SLOP_OPTION_PARSER_TOKEN_DEFINED
#define SLOP_OPTION_PARSER_TOKEN_DEFINED
SLOP_OPTION_DEFINE(parser_Token, slop_option_parser_Token)
#endif

#ifndef SLOP_LIST_PARSER_TOKEN_DEFINED
#define SLOP_LIST_PARSER_TOKEN_DEFINED
SLOP_LIST_DEFINE(parser_Token, slop_list_parser_Token)
#endif

struct parser_ParseError {
    slop_string message;
    int64_t line;
    int64_t col;
};
typedef struct parser_ParseError parser_ParseError;

#ifndef SLOP_OPTION_PARSER_PARSEERROR_DEFINED
#define SLOP_OPTION_PARSER_PARSEERROR_DEFINED
SLOP_OPTION_DEFINE(parser_ParseError, slop_option_parser_ParseError)
#endif

struct parser_LexerState {
    slop_string source;
    int64_t pos;
    int64_t line;
    int64_t col;
};
typedef struct parser_LexerState parser_LexerState;

#ifndef SLOP_OPTION_PARSER_LEXERSTATE_DEFINED
#define SLOP_OPTION_PARSER_LEXERSTATE_DEFINED
SLOP_OPTION_DEFINE(parser_LexerState, slop_option_parser_LexerState)
#endif

struct parser_ParserState {
    slop_list_parser_Token tokens;
    int64_t pos;
    uint8_t in_infix;
};
typedef struct parser_ParserState parser_ParserState;

#ifndef SLOP_OPTION_PARSER_PARSERSTATE_DEFINED
#define SLOP_OPTION_PARSER_PARSERSTATE_DEFINED
SLOP_OPTION_DEFINE(parser_ParserState, slop_option_parser_ParserState)
#endif

#ifndef SLOP_RESULT_LIST_TYPES_SEXPR_PTR_PARSER_PARSEERROR_DEFINED
#define SLOP_RESULT_LIST_TYPES_SEXPR_PTR_PARSER_PARSEERROR_DEFINED
typedef struct { bool is_ok; union { slop_list_types_SExpr_ptr ok; parser_ParseError err; } data; } slop_result_list_types_SExpr_ptr_parser_ParseError;
#endif

#ifndef SLOP_RESULT_PARSER_TOKEN_PARSER_PARSEERROR_DEFINED
#define SLOP_RESULT_PARSER_TOKEN_PARSER_PARSEERROR_DEFINED
typedef struct { bool is_ok; union { parser_Token ok; parser_ParseError err; } data; } slop_result_parser_Token_parser_ParseError;
#endif

#ifndef SLOP_RESULT_LIST_PARSER_TOKEN_PARSER_PARSEERROR_DEFINED
#define SLOP_RESULT_LIST_PARSER_TOKEN_PARSER_PARSEERROR_DEFINED
typedef struct { bool is_ok; union { slop_list_parser_Token ok; parser_ParseError err; } data; } slop_result_list_parser_Token_parser_ParseError;
#endif

#ifndef SLOP_RESULT_TYPES_SEXPR_PTR_PARSER_PARSEERROR_DEFINED
#define SLOP_RESULT_TYPES_SEXPR_PTR_PARSER_PARSEERROR_DEFINED
typedef struct { bool is_ok; union { types_SExpr* ok; parser_ParseError err; } data; } slop_result_types_SExpr_ptr_parser_ParseError;
#endif

typedef slop_result_list_types_SExpr_ptr_parser_ParseError parser_ParseResult;

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

#ifndef SLOP_OPTION_PARSER_TOKEN_DEFINED
#define SLOP_OPTION_PARSER_TOKEN_DEFINED
SLOP_OPTION_DEFINE(parser_Token, slop_option_parser_Token)
#endif

#ifndef SLOP_OPTION_PARSER_PARSEERROR_DEFINED
#define SLOP_OPTION_PARSER_PARSEERROR_DEFINED
SLOP_OPTION_DEFINE(parser_ParseError, slop_option_parser_ParseError)
#endif

#ifndef SLOP_OPTION_PARSER_LEXERSTATE_DEFINED
#define SLOP_OPTION_PARSER_LEXERSTATE_DEFINED
SLOP_OPTION_DEFINE(parser_LexerState, slop_option_parser_LexerState)
#endif

#ifndef SLOP_OPTION_PARSER_PARSERSTATE_DEFINED
#define SLOP_OPTION_PARSER_PARSERSTATE_DEFINED
SLOP_OPTION_DEFINE(parser_ParserState, slop_option_parser_ParserState)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif


#endif
