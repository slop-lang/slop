#include <tree_sitter/parser.h>

#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"
#endif

#define LANGUAGE_VERSION 14
#define STATE_COUNT 32
#define LARGE_STATE_COUNT 4
#define SYMBOL_COUNT 43
#define ALIAS_COUNT 0
#define TOKEN_COUNT 31
#define EXTERNAL_TOKEN_COUNT 0
#define FIELD_COUNT 0
#define MAX_ALIAS_SEQUENCE_LENGTH 4
#define PRODUCTION_ID_COUNT 1

enum {
  anon_sym_LPAREN = 1,
  anon_sym_RPAREN = 2,
  anon_sym_LBRACE = 3,
  anon_sym_RBRACE = 4,
  anon_sym_or = 5,
  anon_sym_and = 6,
  anon_sym_EQ_EQ = 7,
  anon_sym_BANG_EQ = 8,
  anon_sym_LT = 9,
  anon_sym_LT_EQ = 10,
  anon_sym_GT = 11,
  anon_sym_GT_EQ = 12,
  anon_sym_PLUS = 13,
  anon_sym_DASH = 14,
  anon_sym_STAR = 15,
  anon_sym_SLASH = 16,
  anon_sym_PERCENT = 17,
  anon_sym_not = 18,
  sym_comment = 19,
  sym_number = 20,
  sym_string = 21,
  sym_quoted_symbol = 22,
  anon_sym_true = 23,
  anon_sym_false = 24,
  sym_nil = 25,
  sym_annotation = 26,
  sym_keyword = 27,
  sym_type_name = 28,
  sym_identifier = 29,
  sym_range_dots = 30,
  sym_source_file = 31,
  sym__form = 32,
  sym_list = 33,
  sym_infix_expr = 34,
  sym__infix_expr = 35,
  sym_infix_binary = 36,
  sym_infix_unary = 37,
  sym_infix_group = 38,
  sym__infix_atom = 39,
  sym__atom = 40,
  sym_boolean = 41,
  aux_sym_source_file_repeat1 = 42,
};

static const char * const ts_symbol_names[] = {
  [ts_builtin_sym_end] = "end",
  [anon_sym_LPAREN] = "(",
  [anon_sym_RPAREN] = ")",
  [anon_sym_LBRACE] = "{",
  [anon_sym_RBRACE] = "}",
  [anon_sym_or] = "or",
  [anon_sym_and] = "and",
  [anon_sym_EQ_EQ] = "==",
  [anon_sym_BANG_EQ] = "!=",
  [anon_sym_LT] = "<",
  [anon_sym_LT_EQ] = "<=",
  [anon_sym_GT] = ">",
  [anon_sym_GT_EQ] = ">=",
  [anon_sym_PLUS] = "+",
  [anon_sym_DASH] = "-",
  [anon_sym_STAR] = "*",
  [anon_sym_SLASH] = "/",
  [anon_sym_PERCENT] = "%",
  [anon_sym_not] = "not",
  [sym_comment] = "comment",
  [sym_number] = "number",
  [sym_string] = "string",
  [sym_quoted_symbol] = "quoted_symbol",
  [anon_sym_true] = "true",
  [anon_sym_false] = "false",
  [sym_nil] = "nil",
  [sym_annotation] = "annotation",
  [sym_keyword] = "keyword",
  [sym_type_name] = "type_name",
  [sym_identifier] = "identifier",
  [sym_range_dots] = "range_dots",
  [sym_source_file] = "source_file",
  [sym__form] = "_form",
  [sym_list] = "list",
  [sym_infix_expr] = "infix_expr",
  [sym__infix_expr] = "_infix_expr",
  [sym_infix_binary] = "infix_binary",
  [sym_infix_unary] = "infix_unary",
  [sym_infix_group] = "infix_group",
  [sym__infix_atom] = "_infix_atom",
  [sym__atom] = "_atom",
  [sym_boolean] = "boolean",
  [aux_sym_source_file_repeat1] = "source_file_repeat1",
};

static const TSSymbol ts_symbol_map[] = {
  [ts_builtin_sym_end] = ts_builtin_sym_end,
  [anon_sym_LPAREN] = anon_sym_LPAREN,
  [anon_sym_RPAREN] = anon_sym_RPAREN,
  [anon_sym_LBRACE] = anon_sym_LBRACE,
  [anon_sym_RBRACE] = anon_sym_RBRACE,
  [anon_sym_or] = anon_sym_or,
  [anon_sym_and] = anon_sym_and,
  [anon_sym_EQ_EQ] = anon_sym_EQ_EQ,
  [anon_sym_BANG_EQ] = anon_sym_BANG_EQ,
  [anon_sym_LT] = anon_sym_LT,
  [anon_sym_LT_EQ] = anon_sym_LT_EQ,
  [anon_sym_GT] = anon_sym_GT,
  [anon_sym_GT_EQ] = anon_sym_GT_EQ,
  [anon_sym_PLUS] = anon_sym_PLUS,
  [anon_sym_DASH] = anon_sym_DASH,
  [anon_sym_STAR] = anon_sym_STAR,
  [anon_sym_SLASH] = anon_sym_SLASH,
  [anon_sym_PERCENT] = anon_sym_PERCENT,
  [anon_sym_not] = anon_sym_not,
  [sym_comment] = sym_comment,
  [sym_number] = sym_number,
  [sym_string] = sym_string,
  [sym_quoted_symbol] = sym_quoted_symbol,
  [anon_sym_true] = anon_sym_true,
  [anon_sym_false] = anon_sym_false,
  [sym_nil] = sym_nil,
  [sym_annotation] = sym_annotation,
  [sym_keyword] = sym_keyword,
  [sym_type_name] = sym_type_name,
  [sym_identifier] = sym_identifier,
  [sym_range_dots] = sym_range_dots,
  [sym_source_file] = sym_source_file,
  [sym__form] = sym__form,
  [sym_list] = sym_list,
  [sym_infix_expr] = sym_infix_expr,
  [sym__infix_expr] = sym__infix_expr,
  [sym_infix_binary] = sym_infix_binary,
  [sym_infix_unary] = sym_infix_unary,
  [sym_infix_group] = sym_infix_group,
  [sym__infix_atom] = sym__infix_atom,
  [sym__atom] = sym__atom,
  [sym_boolean] = sym_boolean,
  [aux_sym_source_file_repeat1] = aux_sym_source_file_repeat1,
};

static const TSSymbolMetadata ts_symbol_metadata[] = {
  [ts_builtin_sym_end] = {
    .visible = false,
    .named = true,
  },
  [anon_sym_LPAREN] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_RPAREN] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_LBRACE] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_RBRACE] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_or] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_and] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_EQ_EQ] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_BANG_EQ] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_LT] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_LT_EQ] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_GT] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_GT_EQ] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_PLUS] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_DASH] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_STAR] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_SLASH] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_PERCENT] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_not] = {
    .visible = true,
    .named = false,
  },
  [sym_comment] = {
    .visible = true,
    .named = true,
  },
  [sym_number] = {
    .visible = true,
    .named = true,
  },
  [sym_string] = {
    .visible = true,
    .named = true,
  },
  [sym_quoted_symbol] = {
    .visible = true,
    .named = true,
  },
  [anon_sym_true] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_false] = {
    .visible = true,
    .named = false,
  },
  [sym_nil] = {
    .visible = true,
    .named = true,
  },
  [sym_annotation] = {
    .visible = true,
    .named = true,
  },
  [sym_keyword] = {
    .visible = true,
    .named = true,
  },
  [sym_type_name] = {
    .visible = true,
    .named = true,
  },
  [sym_identifier] = {
    .visible = true,
    .named = true,
  },
  [sym_range_dots] = {
    .visible = true,
    .named = true,
  },
  [sym_source_file] = {
    .visible = true,
    .named = true,
  },
  [sym__form] = {
    .visible = false,
    .named = true,
  },
  [sym_list] = {
    .visible = true,
    .named = true,
  },
  [sym_infix_expr] = {
    .visible = true,
    .named = true,
  },
  [sym__infix_expr] = {
    .visible = false,
    .named = true,
  },
  [sym_infix_binary] = {
    .visible = true,
    .named = true,
  },
  [sym_infix_unary] = {
    .visible = true,
    .named = true,
  },
  [sym_infix_group] = {
    .visible = true,
    .named = true,
  },
  [sym__infix_atom] = {
    .visible = false,
    .named = true,
  },
  [sym__atom] = {
    .visible = false,
    .named = true,
  },
  [sym_boolean] = {
    .visible = true,
    .named = true,
  },
  [aux_sym_source_file_repeat1] = {
    .visible = false,
    .named = false,
  },
};

static const TSSymbol ts_alias_sequences[PRODUCTION_ID_COUNT][MAX_ALIAS_SEQUENCE_LENGTH] = {
  [0] = {0},
};

static const uint16_t ts_non_terminal_alias_map[] = {
  0,
};

static const TSStateId ts_primary_state_ids[STATE_COUNT] = {
  [0] = 0,
  [1] = 1,
  [2] = 2,
  [3] = 3,
  [4] = 4,
  [5] = 5,
  [6] = 6,
  [7] = 7,
  [8] = 8,
  [9] = 9,
  [10] = 10,
  [11] = 11,
  [12] = 12,
  [13] = 13,
  [14] = 14,
  [15] = 15,
  [16] = 16,
  [17] = 17,
  [18] = 18,
  [19] = 19,
  [20] = 20,
  [21] = 21,
  [22] = 22,
  [23] = 23,
  [24] = 24,
  [25] = 25,
  [26] = 26,
  [27] = 27,
  [28] = 18,
  [29] = 29,
  [30] = 30,
  [31] = 31,
};

static bool ts_lex(TSLexer *lexer, TSStateId state) {
  START_LEXER();
  eof = lexer->eof(lexer);
  switch (state) {
    case 0:
      if (eof) ADVANCE(16);
      if (lookahead == '!') ADVANCE(64);
      if (lookahead == '"') ADVANCE(4);
      if (lookahead == '%') ADVANCE(46);
      if (lookahead == '\'') ADVANCE(12);
      if (lookahead == '(') ADVANCE(17);
      if (lookahead == ')') ADVANCE(18);
      if (lookahead == '*') ADVANCE(42);
      if (lookahead == '+') ADVANCE(38);
      if (lookahead == '-') ADVANCE(40);
      if (lookahead == '.') ADVANCE(63);
      if (lookahead == '/') ADVANCE(44);
      if (lookahead == '0') ADVANCE(49);
      if (lookahead == ':') ADVANCE(13);
      if (lookahead == ';') ADVANCE(48);
      if (lookahead == '<') ADVANCE(29);
      if (lookahead == '=') ADVANCE(65);
      if (lookahead == '>') ADVANCE(33);
      if (lookahead == '@') ADVANCE(82);
      if (lookahead == 'a') ADVANCE(74);
      if (lookahead == 'f') ADVANCE(66);
      if (lookahead == 'n') ADVANCE(70);
      if (lookahead == 'o') ADVANCE(75);
      if (lookahead == 't') ADVANCE(76);
      if (lookahead == '{') ADVANCE(19);
      if (lookahead == '}') ADVANCE(20);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\r' ||
          lookahead == ' ') SKIP(0)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(50);
      if (lookahead == '&' ||
          lookahead == '?' ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('b' <= lookahead && lookahead <= '|')) ADVANCE(83);
      if (('A' <= lookahead && lookahead <= 'Z')) ADVANCE(62);
      END_STATE();
    case 1:
      if (lookahead == '!') ADVANCE(64);
      if (lookahead == '"') ADVANCE(4);
      if (lookahead == '%') ADVANCE(46);
      if (lookahead == '\'') ADVANCE(12);
      if (lookahead == '(') ADVANCE(17);
      if (lookahead == ')') ADVANCE(18);
      if (lookahead == '*') ADVANCE(42);
      if (lookahead == '+') ADVANCE(38);
      if (lookahead == '-') ADVANCE(40);
      if (lookahead == '.') ADVANCE(63);
      if (lookahead == '/') ADVANCE(44);
      if (lookahead == '0') ADVANCE(49);
      if (lookahead == ':') ADVANCE(13);
      if (lookahead == ';') ADVANCE(48);
      if (lookahead == '<') ADVANCE(29);
      if (lookahead == '=') ADVANCE(65);
      if (lookahead == '>') ADVANCE(33);
      if (lookahead == '@') ADVANCE(82);
      if (lookahead == 'a') ADVANCE(74);
      if (lookahead == 'f') ADVANCE(66);
      if (lookahead == 'n') ADVANCE(71);
      if (lookahead == 'o') ADVANCE(75);
      if (lookahead == 't') ADVANCE(76);
      if (lookahead == '{') ADVANCE(19);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\r' ||
          lookahead == ' ') SKIP(1)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(50);
      if (lookahead == '&' ||
          lookahead == '?' ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('b' <= lookahead && lookahead <= '|')) ADVANCE(83);
      if (('A' <= lookahead && lookahead <= 'Z')) ADVANCE(62);
      END_STATE();
    case 2:
      if (lookahead == '!') ADVANCE(5);
      if (lookahead == '%') ADVANCE(45);
      if (lookahead == ')') ADVANCE(18);
      if (lookahead == '*') ADVANCE(41);
      if (lookahead == '+') ADVANCE(37);
      if (lookahead == '-') ADVANCE(39);
      if (lookahead == '/') ADVANCE(43);
      if (lookahead == ';') ADVANCE(48);
      if (lookahead == '<') ADVANCE(30);
      if (lookahead == '=') ADVANCE(6);
      if (lookahead == '>') ADVANCE(34);
      if (lookahead == 'a') ADVANCE(8);
      if (lookahead == 'o') ADVANCE(9);
      if (lookahead == '}') ADVANCE(20);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\r' ||
          lookahead == ' ') SKIP(2)
      END_STATE();
    case 3:
      if (lookahead == '"') ADVANCE(4);
      if (lookahead == '\'') ADVANCE(12);
      if (lookahead == '(') ADVANCE(17);
      if (lookahead == '-') ADVANCE(40);
      if (lookahead == '0') ADVANCE(49);
      if (lookahead == ';') ADVANCE(48);
      if (lookahead == 'f') ADVANCE(66);
      if (lookahead == 'n') ADVANCE(70);
      if (lookahead == 't') ADVANCE(76);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\r' ||
          lookahead == ' ') SKIP(3)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(50);
      if (('A' <= lookahead && lookahead <= 'Z')) ADVANCE(62);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          lookahead == '.' ||
          lookahead == '/' ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 4:
      if (lookahead == '"') ADVANCE(55);
      if (lookahead == '\\') ADVANCE(14);
      if (lookahead != 0) ADVANCE(4);
      END_STATE();
    case 5:
      if (lookahead == '=') ADVANCE(27);
      END_STATE();
    case 6:
      if (lookahead == '=') ADVANCE(25);
      END_STATE();
    case 7:
      if (lookahead == 'd') ADVANCE(23);
      END_STATE();
    case 8:
      if (lookahead == 'n') ADVANCE(7);
      END_STATE();
    case 9:
      if (lookahead == 'r') ADVANCE(21);
      END_STATE();
    case 10:
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(52);
      END_STATE();
    case 11:
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(54);
      END_STATE();
    case 12:
      if (('a' <= lookahead && lookahead <= 'z')) ADVANCE(56);
      END_STATE();
    case 13:
      if (('a' <= lookahead && lookahead <= 'z')) ADVANCE(61);
      END_STATE();
    case 14:
      if (lookahead != 0 &&
          lookahead != '\n') ADVANCE(4);
      END_STATE();
    case 15:
      if (eof) ADVANCE(16);
      if (lookahead == '"') ADVANCE(4);
      if (lookahead == '\'') ADVANCE(12);
      if (lookahead == '(') ADVANCE(17);
      if (lookahead == ')') ADVANCE(18);
      if (lookahead == '-') ADVANCE(80);
      if (lookahead == '.') ADVANCE(63);
      if (lookahead == '0') ADVANCE(49);
      if (lookahead == ':') ADVANCE(13);
      if (lookahead == ';') ADVANCE(48);
      if (lookahead == '@') ADVANCE(82);
      if (lookahead == 'f') ADVANCE(66);
      if (lookahead == 'n') ADVANCE(71);
      if (lookahead == 't') ADVANCE(76);
      if (lookahead == '{') ADVANCE(19);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\r' ||
          lookahead == ' ') SKIP(15)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(50);
      if (('A' <= lookahead && lookahead <= 'Z')) ADVANCE(62);
      if (lookahead == '!' ||
          ('%' <= lookahead && lookahead <= '+') ||
          ('/' <= lookahead && lookahead <= '?') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= '|')) ADVANCE(83);
      END_STATE();
    case 16:
      ACCEPT_TOKEN(ts_builtin_sym_end);
      END_STATE();
    case 17:
      ACCEPT_TOKEN(anon_sym_LPAREN);
      END_STATE();
    case 18:
      ACCEPT_TOKEN(anon_sym_RPAREN);
      END_STATE();
    case 19:
      ACCEPT_TOKEN(anon_sym_LBRACE);
      END_STATE();
    case 20:
      ACCEPT_TOKEN(anon_sym_RBRACE);
      END_STATE();
    case 21:
      ACCEPT_TOKEN(anon_sym_or);
      END_STATE();
    case 22:
      ACCEPT_TOKEN(anon_sym_or);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 23:
      ACCEPT_TOKEN(anon_sym_and);
      END_STATE();
    case 24:
      ACCEPT_TOKEN(anon_sym_and);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 25:
      ACCEPT_TOKEN(anon_sym_EQ_EQ);
      END_STATE();
    case 26:
      ACCEPT_TOKEN(anon_sym_EQ_EQ);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 27:
      ACCEPT_TOKEN(anon_sym_BANG_EQ);
      END_STATE();
    case 28:
      ACCEPT_TOKEN(anon_sym_BANG_EQ);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 29:
      ACCEPT_TOKEN(anon_sym_LT);
      if (lookahead == '=') ADVANCE(32);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 30:
      ACCEPT_TOKEN(anon_sym_LT);
      if (lookahead == '=') ADVANCE(31);
      END_STATE();
    case 31:
      ACCEPT_TOKEN(anon_sym_LT_EQ);
      END_STATE();
    case 32:
      ACCEPT_TOKEN(anon_sym_LT_EQ);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 33:
      ACCEPT_TOKEN(anon_sym_GT);
      if (lookahead == '=') ADVANCE(36);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 34:
      ACCEPT_TOKEN(anon_sym_GT);
      if (lookahead == '=') ADVANCE(35);
      END_STATE();
    case 35:
      ACCEPT_TOKEN(anon_sym_GT_EQ);
      END_STATE();
    case 36:
      ACCEPT_TOKEN(anon_sym_GT_EQ);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 37:
      ACCEPT_TOKEN(anon_sym_PLUS);
      END_STATE();
    case 38:
      ACCEPT_TOKEN(anon_sym_PLUS);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 39:
      ACCEPT_TOKEN(anon_sym_DASH);
      END_STATE();
    case 40:
      ACCEPT_TOKEN(anon_sym_DASH);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(51);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '/') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 41:
      ACCEPT_TOKEN(anon_sym_STAR);
      END_STATE();
    case 42:
      ACCEPT_TOKEN(anon_sym_STAR);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 43:
      ACCEPT_TOKEN(anon_sym_SLASH);
      END_STATE();
    case 44:
      ACCEPT_TOKEN(anon_sym_SLASH);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 45:
      ACCEPT_TOKEN(anon_sym_PERCENT);
      END_STATE();
    case 46:
      ACCEPT_TOKEN(anon_sym_PERCENT);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 47:
      ACCEPT_TOKEN(anon_sym_not);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 48:
      ACCEPT_TOKEN(sym_comment);
      if (lookahead != 0 &&
          lookahead != '\n') ADVANCE(48);
      END_STATE();
    case 49:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(10);
      if (lookahead == 'x') ADVANCE(11);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(50);
      END_STATE();
    case 50:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(10);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(50);
      END_STATE();
    case 51:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(81);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(51);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '/') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 52:
      ACCEPT_TOKEN(sym_number);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(52);
      END_STATE();
    case 53:
      ACCEPT_TOKEN(sym_number);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(53);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '/') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 54:
      ACCEPT_TOKEN(sym_number);
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(54);
      END_STATE();
    case 55:
      ACCEPT_TOKEN(sym_string);
      END_STATE();
    case 56:
      ACCEPT_TOKEN(sym_quoted_symbol);
      if (lookahead == '-' ||
          ('0' <= lookahead && lookahead <= '9') ||
          ('a' <= lookahead && lookahead <= 'z')) ADVANCE(56);
      END_STATE();
    case 57:
      ACCEPT_TOKEN(anon_sym_true);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 58:
      ACCEPT_TOKEN(anon_sym_false);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 59:
      ACCEPT_TOKEN(sym_nil);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 60:
      ACCEPT_TOKEN(sym_annotation);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('.' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          lookahead == '|') ADVANCE(83);
      if (lookahead == '-' ||
          ('a' <= lookahead && lookahead <= 'z')) ADVANCE(60);
      END_STATE();
    case 61:
      ACCEPT_TOKEN(sym_keyword);
      if (lookahead == '-' ||
          ('0' <= lookahead && lookahead <= '9') ||
          ('a' <= lookahead && lookahead <= 'z')) ADVANCE(61);
      END_STATE();
    case 62:
      ACCEPT_TOKEN(sym_type_name);
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'Z') ||
          ('a' <= lookahead && lookahead <= 'z')) ADVANCE(62);
      END_STATE();
    case 63:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == '.') ADVANCE(84);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 64:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == '=') ADVANCE(28);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 65:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == '=') ADVANCE(26);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 66:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'a') ADVANCE(72);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('b' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 67:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'd') ADVANCE(24);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 68:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'e') ADVANCE(57);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 69:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'e') ADVANCE(58);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 70:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'i') ADVANCE(73);
      if (lookahead == 'o') ADVANCE(78);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 71:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'i') ADVANCE(73);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 72:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'l') ADVANCE(77);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 73:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'l') ADVANCE(59);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 74:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'n') ADVANCE(67);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 75:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'r') ADVANCE(22);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 76:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'r') ADVANCE(79);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 77:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 's') ADVANCE(69);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 78:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 't') ADVANCE(47);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 79:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == 'u') ADVANCE(68);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 80:
      ACCEPT_TOKEN(sym_identifier);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(51);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '/') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 81:
      ACCEPT_TOKEN(sym_identifier);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(53);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '/') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 82:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          lookahead == '|') ADVANCE(83);
      if (('a' <= lookahead && lookahead <= 'z')) ADVANCE(60);
      END_STATE();
    case 83:
      ACCEPT_TOKEN(sym_identifier);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    case 84:
      ACCEPT_TOKEN(sym_range_dots);
      if (lookahead == '!' ||
          lookahead == '%' ||
          lookahead == '&' ||
          lookahead == '*' ||
          lookahead == '+' ||
          ('-' <= lookahead && lookahead <= '9') ||
          ('<' <= lookahead && lookahead <= '@') ||
          lookahead == '^' ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'z') ||
          lookahead == '|') ADVANCE(83);
      END_STATE();
    default:
      return false;
  }
}

static const TSLexMode ts_lex_modes[STATE_COUNT] = {
  [0] = {.lex_state = 0},
  [1] = {.lex_state = 15},
  [2] = {.lex_state = 1},
  [3] = {.lex_state = 15},
  [4] = {.lex_state = 15},
  [5] = {.lex_state = 15},
  [6] = {.lex_state = 15},
  [7] = {.lex_state = 15},
  [8] = {.lex_state = 3},
  [9] = {.lex_state = 3},
  [10] = {.lex_state = 3},
  [11] = {.lex_state = 3},
  [12] = {.lex_state = 3},
  [13] = {.lex_state = 3},
  [14] = {.lex_state = 3},
  [15] = {.lex_state = 3},
  [16] = {.lex_state = 2},
  [17] = {.lex_state = 15},
  [18] = {.lex_state = 15},
  [19] = {.lex_state = 15},
  [20] = {.lex_state = 15},
  [21] = {.lex_state = 2},
  [22] = {.lex_state = 2},
  [23] = {.lex_state = 2},
  [24] = {.lex_state = 2},
  [25] = {.lex_state = 2},
  [26] = {.lex_state = 2},
  [27] = {.lex_state = 2},
  [28] = {.lex_state = 2},
  [29] = {.lex_state = 2},
  [30] = {.lex_state = 2},
  [31] = {.lex_state = 0},
};

static const uint16_t ts_parse_table[LARGE_STATE_COUNT][SYMBOL_COUNT] = {
  [0] = {
    [ts_builtin_sym_end] = ACTIONS(1),
    [anon_sym_LPAREN] = ACTIONS(1),
    [anon_sym_RPAREN] = ACTIONS(1),
    [anon_sym_LBRACE] = ACTIONS(1),
    [anon_sym_RBRACE] = ACTIONS(1),
    [anon_sym_or] = ACTIONS(1),
    [anon_sym_and] = ACTIONS(1),
    [anon_sym_EQ_EQ] = ACTIONS(1),
    [anon_sym_BANG_EQ] = ACTIONS(1),
    [anon_sym_LT] = ACTIONS(1),
    [anon_sym_LT_EQ] = ACTIONS(1),
    [anon_sym_GT] = ACTIONS(1),
    [anon_sym_GT_EQ] = ACTIONS(1),
    [anon_sym_PLUS] = ACTIONS(1),
    [anon_sym_DASH] = ACTIONS(1),
    [anon_sym_STAR] = ACTIONS(1),
    [anon_sym_SLASH] = ACTIONS(1),
    [anon_sym_PERCENT] = ACTIONS(1),
    [anon_sym_not] = ACTIONS(1),
    [sym_comment] = ACTIONS(3),
    [sym_number] = ACTIONS(1),
    [sym_string] = ACTIONS(1),
    [sym_quoted_symbol] = ACTIONS(1),
    [anon_sym_true] = ACTIONS(1),
    [anon_sym_false] = ACTIONS(1),
    [sym_nil] = ACTIONS(1),
    [sym_annotation] = ACTIONS(1),
    [sym_keyword] = ACTIONS(1),
    [sym_type_name] = ACTIONS(1),
    [sym_identifier] = ACTIONS(1),
    [sym_range_dots] = ACTIONS(1),
  },
  [1] = {
    [sym_source_file] = STATE(31),
    [sym__form] = STATE(6),
    [sym_list] = STATE(6),
    [sym_infix_expr] = STATE(6),
    [sym__atom] = STATE(6),
    [sym_boolean] = STATE(6),
    [aux_sym_source_file_repeat1] = STATE(6),
    [ts_builtin_sym_end] = ACTIONS(5),
    [anon_sym_LPAREN] = ACTIONS(7),
    [anon_sym_LBRACE] = ACTIONS(9),
    [sym_comment] = ACTIONS(3),
    [sym_number] = ACTIONS(11),
    [sym_string] = ACTIONS(13),
    [sym_quoted_symbol] = ACTIONS(13),
    [anon_sym_true] = ACTIONS(15),
    [anon_sym_false] = ACTIONS(15),
    [sym_nil] = ACTIONS(11),
    [sym_annotation] = ACTIONS(11),
    [sym_keyword] = ACTIONS(13),
    [sym_type_name] = ACTIONS(13),
    [sym_identifier] = ACTIONS(11),
    [sym_range_dots] = ACTIONS(11),
  },
  [2] = {
    [sym__form] = STATE(5),
    [sym_list] = STATE(5),
    [sym_infix_expr] = STATE(5),
    [sym__atom] = STATE(5),
    [sym_boolean] = STATE(5),
    [aux_sym_source_file_repeat1] = STATE(5),
    [anon_sym_LPAREN] = ACTIONS(7),
    [anon_sym_RPAREN] = ACTIONS(17),
    [anon_sym_LBRACE] = ACTIONS(9),
    [anon_sym_or] = ACTIONS(19),
    [anon_sym_and] = ACTIONS(19),
    [anon_sym_EQ_EQ] = ACTIONS(19),
    [anon_sym_BANG_EQ] = ACTIONS(19),
    [anon_sym_LT] = ACTIONS(19),
    [anon_sym_LT_EQ] = ACTIONS(19),
    [anon_sym_GT] = ACTIONS(19),
    [anon_sym_GT_EQ] = ACTIONS(19),
    [anon_sym_PLUS] = ACTIONS(19),
    [anon_sym_DASH] = ACTIONS(19),
    [anon_sym_STAR] = ACTIONS(19),
    [anon_sym_SLASH] = ACTIONS(19),
    [anon_sym_PERCENT] = ACTIONS(19),
    [sym_comment] = ACTIONS(3),
    [sym_number] = ACTIONS(21),
    [sym_string] = ACTIONS(23),
    [sym_quoted_symbol] = ACTIONS(23),
    [anon_sym_true] = ACTIONS(15),
    [anon_sym_false] = ACTIONS(15),
    [sym_nil] = ACTIONS(21),
    [sym_annotation] = ACTIONS(21),
    [sym_keyword] = ACTIONS(23),
    [sym_type_name] = ACTIONS(23),
    [sym_identifier] = ACTIONS(21),
    [sym_range_dots] = ACTIONS(21),
  },
  [3] = {
    [sym__form] = STATE(3),
    [sym_list] = STATE(3),
    [sym_infix_expr] = STATE(3),
    [sym__atom] = STATE(3),
    [sym_boolean] = STATE(3),
    [aux_sym_source_file_repeat1] = STATE(3),
    [ts_builtin_sym_end] = ACTIONS(25),
    [anon_sym_LPAREN] = ACTIONS(27),
    [anon_sym_RPAREN] = ACTIONS(25),
    [anon_sym_LBRACE] = ACTIONS(30),
    [sym_comment] = ACTIONS(3),
    [sym_number] = ACTIONS(33),
    [sym_string] = ACTIONS(36),
    [sym_quoted_symbol] = ACTIONS(36),
    [anon_sym_true] = ACTIONS(39),
    [anon_sym_false] = ACTIONS(39),
    [sym_nil] = ACTIONS(33),
    [sym_annotation] = ACTIONS(33),
    [sym_keyword] = ACTIONS(36),
    [sym_type_name] = ACTIONS(36),
    [sym_identifier] = ACTIONS(33),
    [sym_range_dots] = ACTIONS(33),
  },
};

static const uint16_t ts_small_parse_table[] = {
  [0] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(7), 1,
      anon_sym_LPAREN,
    ACTIONS(9), 1,
      anon_sym_LBRACE,
    ACTIONS(42), 1,
      anon_sym_RPAREN,
    ACTIONS(15), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(46), 4,
      sym_string,
      sym_quoted_symbol,
      sym_keyword,
      sym_type_name,
    ACTIONS(44), 5,
      sym_number,
      sym_nil,
      sym_annotation,
      sym_identifier,
      sym_range_dots,
    STATE(7), 6,
      sym__form,
      sym_list,
      sym_infix_expr,
      sym__atom,
      sym_boolean,
      aux_sym_source_file_repeat1,
  [38] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(7), 1,
      anon_sym_LPAREN,
    ACTIONS(9), 1,
      anon_sym_LBRACE,
    ACTIONS(48), 1,
      anon_sym_RPAREN,
    ACTIONS(15), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(52), 4,
      sym_string,
      sym_quoted_symbol,
      sym_keyword,
      sym_type_name,
    ACTIONS(50), 5,
      sym_number,
      sym_nil,
      sym_annotation,
      sym_identifier,
      sym_range_dots,
    STATE(3), 6,
      sym__form,
      sym_list,
      sym_infix_expr,
      sym__atom,
      sym_boolean,
      aux_sym_source_file_repeat1,
  [76] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(7), 1,
      anon_sym_LPAREN,
    ACTIONS(9), 1,
      anon_sym_LBRACE,
    ACTIONS(54), 1,
      ts_builtin_sym_end,
    ACTIONS(15), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(52), 4,
      sym_string,
      sym_quoted_symbol,
      sym_keyword,
      sym_type_name,
    ACTIONS(50), 5,
      sym_number,
      sym_nil,
      sym_annotation,
      sym_identifier,
      sym_range_dots,
    STATE(3), 6,
      sym__form,
      sym_list,
      sym_infix_expr,
      sym__atom,
      sym_boolean,
      aux_sym_source_file_repeat1,
  [114] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(7), 1,
      anon_sym_LPAREN,
    ACTIONS(9), 1,
      anon_sym_LBRACE,
    ACTIONS(56), 1,
      anon_sym_RPAREN,
    ACTIONS(15), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(52), 4,
      sym_string,
      sym_quoted_symbol,
      sym_keyword,
      sym_type_name,
    ACTIONS(50), 5,
      sym_number,
      sym_nil,
      sym_annotation,
      sym_identifier,
      sym_range_dots,
    STATE(3), 6,
      sym__form,
      sym_list,
      sym_infix_expr,
      sym__atom,
      sym_boolean,
      aux_sym_source_file_repeat1,
  [152] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(58), 1,
      anon_sym_LPAREN,
    ACTIONS(60), 2,
      anon_sym_DASH,
      anon_sym_not,
    ACTIONS(66), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(62), 3,
      sym_number,
      sym_nil,
      sym_identifier,
    ACTIONS(64), 3,
      sym_string,
      sym_quoted_symbol,
      sym_type_name,
    STATE(22), 6,
      sym__infix_expr,
      sym_infix_binary,
      sym_infix_unary,
      sym_infix_group,
      sym__infix_atom,
      sym_boolean,
  [185] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(58), 1,
      anon_sym_LPAREN,
    ACTIONS(60), 2,
      anon_sym_DASH,
      anon_sym_not,
    ACTIONS(66), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(68), 3,
      sym_number,
      sym_nil,
      sym_identifier,
    ACTIONS(70), 3,
      sym_string,
      sym_quoted_symbol,
      sym_type_name,
    STATE(30), 6,
      sym__infix_expr,
      sym_infix_binary,
      sym_infix_unary,
      sym_infix_group,
      sym__infix_atom,
      sym_boolean,
  [218] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(58), 1,
      anon_sym_LPAREN,
    ACTIONS(60), 2,
      anon_sym_DASH,
      anon_sym_not,
    ACTIONS(66), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(72), 3,
      sym_number,
      sym_nil,
      sym_identifier,
    ACTIONS(74), 3,
      sym_string,
      sym_quoted_symbol,
      sym_type_name,
    STATE(26), 6,
      sym__infix_expr,
      sym_infix_binary,
      sym_infix_unary,
      sym_infix_group,
      sym__infix_atom,
      sym_boolean,
  [251] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(58), 1,
      anon_sym_LPAREN,
    ACTIONS(60), 2,
      anon_sym_DASH,
      anon_sym_not,
    ACTIONS(66), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(76), 3,
      sym_number,
      sym_nil,
      sym_identifier,
    ACTIONS(78), 3,
      sym_string,
      sym_quoted_symbol,
      sym_type_name,
    STATE(25), 6,
      sym__infix_expr,
      sym_infix_binary,
      sym_infix_unary,
      sym_infix_group,
      sym__infix_atom,
      sym_boolean,
  [284] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(58), 1,
      anon_sym_LPAREN,
    ACTIONS(84), 1,
      sym_identifier,
    ACTIONS(60), 2,
      anon_sym_DASH,
      anon_sym_not,
    ACTIONS(66), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(80), 2,
      sym_number,
      sym_nil,
    ACTIONS(82), 3,
      sym_string,
      sym_quoted_symbol,
      sym_type_name,
    STATE(29), 6,
      sym__infix_expr,
      sym_infix_binary,
      sym_infix_unary,
      sym_infix_group,
      sym__infix_atom,
      sym_boolean,
  [319] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(58), 1,
      anon_sym_LPAREN,
    ACTIONS(60), 2,
      anon_sym_DASH,
      anon_sym_not,
    ACTIONS(66), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(86), 3,
      sym_number,
      sym_nil,
      sym_identifier,
    ACTIONS(88), 3,
      sym_string,
      sym_quoted_symbol,
      sym_type_name,
    STATE(16), 6,
      sym__infix_expr,
      sym_infix_binary,
      sym_infix_unary,
      sym_infix_group,
      sym__infix_atom,
      sym_boolean,
  [352] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(58), 1,
      anon_sym_LPAREN,
    ACTIONS(60), 2,
      anon_sym_DASH,
      anon_sym_not,
    ACTIONS(66), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(90), 3,
      sym_number,
      sym_nil,
      sym_identifier,
    ACTIONS(92), 3,
      sym_string,
      sym_quoted_symbol,
      sym_type_name,
    STATE(24), 6,
      sym__infix_expr,
      sym_infix_binary,
      sym_infix_unary,
      sym_infix_group,
      sym__infix_atom,
      sym_boolean,
  [385] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(58), 1,
      anon_sym_LPAREN,
    ACTIONS(60), 2,
      anon_sym_DASH,
      anon_sym_not,
    ACTIONS(66), 2,
      anon_sym_true,
      anon_sym_false,
    ACTIONS(94), 3,
      sym_number,
      sym_nil,
      sym_identifier,
    ACTIONS(96), 3,
      sym_string,
      sym_quoted_symbol,
      sym_type_name,
    STATE(23), 6,
      sym__infix_expr,
      sym_infix_binary,
      sym_infix_unary,
      sym_infix_group,
      sym__infix_atom,
      sym_boolean,
  [418] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(100), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(98), 13,
      anon_sym_RPAREN,
      anon_sym_RBRACE,
      anon_sym_or,
      anon_sym_and,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
  [441] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(104), 7,
      sym_number,
      anon_sym_true,
      anon_sym_false,
      sym_nil,
      sym_annotation,
      sym_identifier,
      sym_range_dots,
    ACTIONS(102), 8,
      ts_builtin_sym_end,
      anon_sym_LPAREN,
      anon_sym_RPAREN,
      anon_sym_LBRACE,
      sym_string,
      sym_quoted_symbol,
      sym_keyword,
      sym_type_name,
  [464] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(108), 7,
      sym_number,
      anon_sym_true,
      anon_sym_false,
      sym_nil,
      sym_annotation,
      sym_identifier,
      sym_range_dots,
    ACTIONS(106), 8,
      ts_builtin_sym_end,
      anon_sym_LPAREN,
      anon_sym_RPAREN,
      anon_sym_LBRACE,
      sym_string,
      sym_quoted_symbol,
      sym_keyword,
      sym_type_name,
  [487] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(112), 7,
      sym_number,
      anon_sym_true,
      anon_sym_false,
      sym_nil,
      sym_annotation,
      sym_identifier,
      sym_range_dots,
    ACTIONS(110), 8,
      ts_builtin_sym_end,
      anon_sym_LPAREN,
      anon_sym_RPAREN,
      anon_sym_LBRACE,
      sym_string,
      sym_quoted_symbol,
      sym_keyword,
      sym_type_name,
  [510] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(116), 7,
      sym_number,
      anon_sym_true,
      anon_sym_false,
      sym_nil,
      sym_annotation,
      sym_identifier,
      sym_range_dots,
    ACTIONS(114), 8,
      ts_builtin_sym_end,
      anon_sym_LPAREN,
      anon_sym_RPAREN,
      anon_sym_LBRACE,
      sym_string,
      sym_quoted_symbol,
      sym_keyword,
      sym_type_name,
  [533] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(120), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(118), 13,
      anon_sym_RPAREN,
      anon_sym_RBRACE,
      anon_sym_or,
      anon_sym_and,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
  [556] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(124), 1,
      anon_sym_and,
    ACTIONS(128), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(130), 2,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(122), 3,
      anon_sym_RPAREN,
      anon_sym_RBRACE,
      anon_sym_or,
    ACTIONS(132), 3,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
    ACTIONS(126), 4,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
  [587] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(128), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(130), 2,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(132), 3,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
    ACTIONS(122), 4,
      anon_sym_RPAREN,
      anon_sym_RBRACE,
      anon_sym_or,
      anon_sym_and,
    ACTIONS(126), 4,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
  [616] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(130), 2,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(134), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(132), 3,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
    ACTIONS(122), 8,
      anon_sym_RPAREN,
      anon_sym_RBRACE,
      anon_sym_or,
      anon_sym_and,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
  [643] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(134), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(132), 3,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
    ACTIONS(122), 10,
      anon_sym_RPAREN,
      anon_sym_RBRACE,
      anon_sym_or,
      anon_sym_and,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [668] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(134), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(122), 13,
      anon_sym_RPAREN,
      anon_sym_RBRACE,
      anon_sym_or,
      anon_sym_and,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
  [691] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(138), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(136), 13,
      anon_sym_RPAREN,
      anon_sym_RBRACE,
      anon_sym_or,
      anon_sym_and,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
  [714] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(108), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(106), 13,
      anon_sym_RPAREN,
      anon_sym_RBRACE,
      anon_sym_or,
      anon_sym_and,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
  [737] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(124), 1,
      anon_sym_and,
    ACTIONS(140), 1,
      anon_sym_RPAREN,
    ACTIONS(142), 1,
      anon_sym_or,
    ACTIONS(128), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(130), 2,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(132), 3,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
    ACTIONS(126), 4,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
  [769] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(124), 1,
      anon_sym_and,
    ACTIONS(142), 1,
      anon_sym_or,
    ACTIONS(144), 1,
      anon_sym_RBRACE,
    ACTIONS(128), 2,
      anon_sym_LT,
      anon_sym_GT,
    ACTIONS(130), 2,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(132), 3,
      anon_sym_STAR,
      anon_sym_SLASH,
      anon_sym_PERCENT,
    ACTIONS(126), 4,
      anon_sym_EQ_EQ,
      anon_sym_BANG_EQ,
      anon_sym_LT_EQ,
      anon_sym_GT_EQ,
  [801] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(146), 1,
      ts_builtin_sym_end,
};

static const uint32_t ts_small_parse_table_map[] = {
  [SMALL_STATE(4)] = 0,
  [SMALL_STATE(5)] = 38,
  [SMALL_STATE(6)] = 76,
  [SMALL_STATE(7)] = 114,
  [SMALL_STATE(8)] = 152,
  [SMALL_STATE(9)] = 185,
  [SMALL_STATE(10)] = 218,
  [SMALL_STATE(11)] = 251,
  [SMALL_STATE(12)] = 284,
  [SMALL_STATE(13)] = 319,
  [SMALL_STATE(14)] = 352,
  [SMALL_STATE(15)] = 385,
  [SMALL_STATE(16)] = 418,
  [SMALL_STATE(17)] = 441,
  [SMALL_STATE(18)] = 464,
  [SMALL_STATE(19)] = 487,
  [SMALL_STATE(20)] = 510,
  [SMALL_STATE(21)] = 533,
  [SMALL_STATE(22)] = 556,
  [SMALL_STATE(23)] = 587,
  [SMALL_STATE(24)] = 616,
  [SMALL_STATE(25)] = 643,
  [SMALL_STATE(26)] = 668,
  [SMALL_STATE(27)] = 691,
  [SMALL_STATE(28)] = 714,
  [SMALL_STATE(29)] = 737,
  [SMALL_STATE(30)] = 769,
  [SMALL_STATE(31)] = 801,
};

static const TSParseActionEntry ts_parse_actions[] = {
  [0] = {.entry = {.count = 0, .reusable = false}},
  [1] = {.entry = {.count = 1, .reusable = false}}, RECOVER(),
  [3] = {.entry = {.count = 1, .reusable = true}}, SHIFT_EXTRA(),
  [5] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_source_file, 0),
  [7] = {.entry = {.count = 1, .reusable = true}}, SHIFT(4),
  [9] = {.entry = {.count = 1, .reusable = true}}, SHIFT(9),
  [11] = {.entry = {.count = 1, .reusable = false}}, SHIFT(6),
  [13] = {.entry = {.count = 1, .reusable = true}}, SHIFT(6),
  [15] = {.entry = {.count = 1, .reusable = false}}, SHIFT(18),
  [17] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__infix_atom, 1),
  [19] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym__infix_atom, 1),
  [21] = {.entry = {.count = 1, .reusable = false}}, SHIFT(5),
  [23] = {.entry = {.count = 1, .reusable = true}}, SHIFT(5),
  [25] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2),
  [27] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(4),
  [30] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(9),
  [33] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(3),
  [36] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(3),
  [39] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(18),
  [42] = {.entry = {.count = 1, .reusable = true}}, SHIFT(20),
  [44] = {.entry = {.count = 1, .reusable = false}}, SHIFT(7),
  [46] = {.entry = {.count = 1, .reusable = true}}, SHIFT(7),
  [48] = {.entry = {.count = 1, .reusable = true}}, SHIFT(27),
  [50] = {.entry = {.count = 1, .reusable = false}}, SHIFT(3),
  [52] = {.entry = {.count = 1, .reusable = true}}, SHIFT(3),
  [54] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_source_file, 1),
  [56] = {.entry = {.count = 1, .reusable = true}}, SHIFT(19),
  [58] = {.entry = {.count = 1, .reusable = true}}, SHIFT(12),
  [60] = {.entry = {.count = 1, .reusable = false}}, SHIFT(13),
  [62] = {.entry = {.count = 1, .reusable = false}}, SHIFT(22),
  [64] = {.entry = {.count = 1, .reusable = true}}, SHIFT(22),
  [66] = {.entry = {.count = 1, .reusable = false}}, SHIFT(28),
  [68] = {.entry = {.count = 1, .reusable = false}}, SHIFT(30),
  [70] = {.entry = {.count = 1, .reusable = true}}, SHIFT(30),
  [72] = {.entry = {.count = 1, .reusable = false}}, SHIFT(26),
  [74] = {.entry = {.count = 1, .reusable = true}}, SHIFT(26),
  [76] = {.entry = {.count = 1, .reusable = false}}, SHIFT(25),
  [78] = {.entry = {.count = 1, .reusable = true}}, SHIFT(25),
  [80] = {.entry = {.count = 1, .reusable = false}}, SHIFT(29),
  [82] = {.entry = {.count = 1, .reusable = true}}, SHIFT(29),
  [84] = {.entry = {.count = 1, .reusable = false}}, SHIFT(2),
  [86] = {.entry = {.count = 1, .reusable = false}}, SHIFT(16),
  [88] = {.entry = {.count = 1, .reusable = true}}, SHIFT(16),
  [90] = {.entry = {.count = 1, .reusable = false}}, SHIFT(24),
  [92] = {.entry = {.count = 1, .reusable = true}}, SHIFT(24),
  [94] = {.entry = {.count = 1, .reusable = false}}, SHIFT(23),
  [96] = {.entry = {.count = 1, .reusable = true}}, SHIFT(23),
  [98] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_infix_unary, 2),
  [100] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_infix_unary, 2),
  [102] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_infix_expr, 3),
  [104] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_infix_expr, 3),
  [106] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_boolean, 1),
  [108] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_boolean, 1),
  [110] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_list, 3),
  [112] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_list, 3),
  [114] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_list, 2),
  [116] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_list, 2),
  [118] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_infix_group, 3),
  [120] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_infix_group, 3),
  [122] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_infix_binary, 3),
  [124] = {.entry = {.count = 1, .reusable = true}}, SHIFT(15),
  [126] = {.entry = {.count = 1, .reusable = true}}, SHIFT(14),
  [128] = {.entry = {.count = 1, .reusable = false}}, SHIFT(14),
  [130] = {.entry = {.count = 1, .reusable = true}}, SHIFT(11),
  [132] = {.entry = {.count = 1, .reusable = true}}, SHIFT(10),
  [134] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_infix_binary, 3),
  [136] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_infix_group, 4),
  [138] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_infix_group, 4),
  [140] = {.entry = {.count = 1, .reusable = true}}, SHIFT(21),
  [142] = {.entry = {.count = 1, .reusable = true}}, SHIFT(8),
  [144] = {.entry = {.count = 1, .reusable = true}}, SHIFT(17),
  [146] = {.entry = {.count = 1, .reusable = true}},  ACCEPT_INPUT(),
};

#ifdef __cplusplus
extern "C" {
#endif
#ifdef _WIN32
#define extern __declspec(dllexport)
#endif

extern const TSLanguage *tree_sitter_slop(void) {
  static const TSLanguage language = {
    .version = LANGUAGE_VERSION,
    .symbol_count = SYMBOL_COUNT,
    .alias_count = ALIAS_COUNT,
    .token_count = TOKEN_COUNT,
    .external_token_count = EXTERNAL_TOKEN_COUNT,
    .state_count = STATE_COUNT,
    .large_state_count = LARGE_STATE_COUNT,
    .production_id_count = PRODUCTION_ID_COUNT,
    .field_count = FIELD_COUNT,
    .max_alias_sequence_length = MAX_ALIAS_SEQUENCE_LENGTH,
    .parse_table = &ts_parse_table[0][0],
    .small_parse_table = ts_small_parse_table,
    .small_parse_table_map = ts_small_parse_table_map,
    .parse_actions = ts_parse_actions,
    .symbol_names = ts_symbol_names,
    .symbol_metadata = ts_symbol_metadata,
    .public_symbol_map = ts_symbol_map,
    .alias_map = ts_non_terminal_alias_map,
    .alias_sequences = &ts_alias_sequences[0][0],
    .lex_modes = ts_lex_modes,
    .lex_fn = ts_lex,
    .primary_state_ids = ts_primary_state_ids,
  };
  return &language;
}
#ifdef __cplusplus
}
#endif
