/**
 * Tree-sitter grammar for SLOP (Symbolic LLM-Optimized Programming)
 *
 * SLOP uses S-expression syntax with:
 * - Modules, functions, and type definitions
 * - Contract annotations (@intent, @spec, @pre, @post)
 * - Range types (Int 0 .. 100)
 * - Holes for LLM generation
 */

module.exports = grammar({
  name: 'slop',

  extras: $ => [
    /\s/,
    $.comment,
  ],

  rules: {
    source_file: $ => repeat($._form),

    _form: $ => choice(
      $.list,
      $._atom
    ),

    // S-expression list
    list: $ => seq(
      '(',
      repeat($._form),
      ')'
    ),

    // Atoms
    _atom: $ => choice(
      $.number,
      $.string,
      $.quoted_symbol,
      $.boolean,
      $.nil,
      $.annotation,
      $.keyword,
      $.type_name,
      $.identifier,
      $.range_dots
    ),

    // Comments
    comment: $ => token(seq(';', /.*/)),

    // Literals
    number: $ => token(choice(
      // Integer
      /-?[0-9]+/,
      // Float
      /-?[0-9]+\.[0-9]+/,
      // Hex
      /0x[0-9a-fA-F]+/
    )),

    string: $ => token(seq(
      '"',
      repeat(choice(
        /[^"\\]/,
        /\\./
      )),
      '"'
    )),

    // Quoted symbol (enum value)
    quoted_symbol: $ => token(seq(
      "'",
      /[a-z][a-z0-9-]*/
    )),

    // Boolean and nil
    boolean: $ => choice('true', 'false'),
    nil: $ => 'nil',

    // Contract and metadata annotations (@intent, @spec, etc.)
    annotation: $ => token(seq(
      '@',
      /[a-z][a-z-]*/
    )),

    // Keywords (:keyword style, used in hole attributes)
    keyword: $ => token(seq(
      ':',
      /[a-z][a-z0-9-]*/
    )),

    // Type names (PascalCase)
    type_name: $ => /[A-Z][a-zA-Z0-9]*/,

    // Identifiers (kebab-case, includes special forms and operators)
    identifier: $ => /[a-z_+\-*\/%<>=!&|^.@?][a-z0-9_+\-*\/%<>=!&|^.@?]*/,

    // Range dots for type bounds
    range_dots: $ => '..',
  }
});
