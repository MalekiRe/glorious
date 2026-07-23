/**
 * @file Tree-sitter grammar for the Grandiose programming language.
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

const commaSep = rule => optional(seq(rule, repeat(seq(',', rule)), optional(',')));
const path = $ => seq($.identifier, repeat(seq('::', $.identifier)));

module.exports = grammar({
  name: 'grandiose',

  extras: $ => [/[\s\uFEFF\u2060\u200B]/, $.line_comment, $.block_comment],
  word: $ => $.identifier,

  supertypes: $ => [$._declaration, $._expression, $._type, $._pattern],
  conflicts: $ => [
    [$.block, $.struct_expression],
    [$.block, $.closure_expression],
    [$.effect_row, $.block],
    [$._type, $._expression],
    [$._pattern, $._expression],
    [$._pattern, $.type_identifier],
    [$.generic_arguments, $.binary_expression],
  ],

  rules: {
    source_file: $ => repeat($._declaration),

    _declaration: $ => choice(
      $.module_declaration,
      $.use_declaration,
      $.type_alias_declaration,
      $.effect_row_alias_declaration,
      $.fixity_declaration,
      $.global_binding_declaration,
      $.struct_declaration,
      $.enum_declaration,
      $.trait_declaration,
      $.impl_declaration,
      $.effect_declaration,
      $.function_declaration,
      $.empty_statement,
    ),

    visibility_modifier: _ => 'pub',
    field_visibility_modifier: _ => 'private',

    module_declaration: $ => seq(optional($.visibility_modifier), 'mod', field('name', $.identifier), choice(';', seq('{', repeat($._declaration), '}'))),
    use_declaration: $ => seq(optional($.visibility_modifier), 'use', $.import_tree, ';'),
    import_tree: $ => prec.right(choice(
      seq('{', commaSep($.import_tree), '}'),
      '*',
      seq(choice($.identifier, 'self'), optional(seq('::', $.import_tree)), optional(seq('as', $.identifier))),
    )),

    type_alias_declaration: $ => seq(optional($.visibility_modifier), 'type', field('name', $.type_identifier), optional($.generic_parameters), '=', field('value', $._type), ';'),
    effect_row_alias_declaration: $ => seq(optional($.visibility_modifier), 'cases', field('name', $.type_identifier), optional($.generic_parameters), '=', $.effect_row, ';'),
    global_binding_declaration: $ => seq(optional($.visibility_modifier), 'let', field('name', $.path_expression), optional(seq(':', $._type)), '=', field('value', $._expression), ';'),

    fixity_declaration: $ => seq(
      optional($.visibility_modifier),
      field('associativity', choice('infixl', 'infixr', 'infix', 'prefix')),
      field('precedence', $.integer_literal),
      field('operator', choice($.operator_sequence, $.identifier, $.word_operator)),
      ';',
    ),

    struct_declaration: $ => seq(optional($.visibility_modifier), 'struct', field('name', $.type_identifier), optional($.generic_parameters), '{', repeat($.field_declaration), '}'),
    field_declaration: $ => seq(optional($.field_visibility_modifier), field('name', $.identifier), ':', field('type', $._type), optional(choice(',', ';'))),

    enum_declaration: $ => seq(optional($.visibility_modifier), 'enum', field('name', $.type_identifier), optional($.generic_parameters), '{', repeat($.enum_variant), '}'),
    enum_variant: $ => seq(field('name', $.variant_identifier), optional(seq('(', commaSep($._type), ')')), optional(choice(',', ';'))),

    trait_declaration: $ => seq(optional($.visibility_modifier), 'trait', field('name', $.type_identifier), optional($.generic_parameters), optional(seq(':', sep1($.trait_reference, '+'))), '{', repeat(choice($.associated_type_declaration, $.function_signature)), '}'),
    associated_type_declaration: $ => seq('type', field('name', $.type_identifier), optional($.generic_parameters), optional(seq(':', 'EffectRow')), ';'),
    impl_declaration: $ => seq(optional($.visibility_modifier), 'impl', optional($.generic_parameters), optional('!'), $.trait_reference, 'for', $._type, optional($.where_clause), '{', repeat(choice($.associated_type_definition, $.function_declaration)), '}'),
    associated_type_definition: $ => seq('type', field('name', $.type_identifier), optional($.generic_parameters), '=', choice($._type, $.effect_row), ';'),

    effect_declaration: $ => seq(optional($.visibility_modifier), 'effect', field('name', $.effect_identifier), optional($.generic_parameters), '{', repeat($.effect_operation), '}'),
    effect_operation: $ => prec.right(seq(optional($.quantity), field('name', $.effect_operation_identifier), $.parameters, '->', optional($._type), optional(';'))),
    quantity: $ => seq('[', $.integer_literal, ',', choice($.integer_literal, 'infinity', '*'), ']'),

    function_declaration: $ => seq(optional($.visibility_modifier), field('name', $.identifier), optional($.generic_parameters), $.parameters, '->', optional($._type), optional(seq('/', $.effect_row)), optional($.where_clause), field('body', $.block)),
    function_signature: $ => seq(field('name', $.identifier), optional($.generic_parameters), $.parameters, '->', optional($._type), optional(seq('/', $.effect_row)), optional($.where_clause), ';'),
    parameters: $ => seq('(', commaSep($.parameter), ')'),
    parameter: $ => seq(field('name', $.identifier), ':', field('type', $._type)),

    generic_parameters: $ => seq('<', commaSep($.generic_parameter), '>'),
    generic_parameter: $ => choice(
      $.lifetime,
      seq('const', $.identifier, ':', choice('Quantity', 'u32'), optional(seq('=', $._expression))),
      seq($.identifier, optional(seq(':', 'EffectRow'))),
    ),
    generic_arguments: $ => prec(1, seq('<', commaSep($.generic_argument), '>')),
    generic_argument: $ => choice(seq($.identifier, '=', choice($._type, $.effect_row, $.quantity, $.literal)), $.lifetime, $._type, $.quantity, $.literal),
    where_clause: $ => seq('where', commaSep($.where_predicate)),
    where_predicate: $ => choice(
      seq(optional(seq('for', $.generic_parameters)), $.lifetime, ':', $.lifetime),
      seq(optional(seq('for', $.generic_parameters)), $._type, ':', sep1($.trait_reference, '+')),
    ),
    trait_reference: $ => seq($.type_path, optional($.generic_arguments)),
    effect_row: $ => seq('{', commaSep($._type), optional(seq('|', $.identifier)), '}'),

    _type: $ => choice(
      $.type_path,
      $.reference_type,
      $.tuple_type,
      $.array_type,
      $.function_type,
      $.never_type,
      $.inferred_type,
    ),
    type_path: $ => prec.right(seq(optional(seq('<', $._type, 'as', $.trait_reference, '>', '::')), field('name', $.type_identifier), repeat(seq('::', field('name', $.type_identifier))), optional($.generic_arguments))),
    reference_type: $ => seq('&', optional($.lifetime), optional('mut'), $._type),
    tuple_type: $ => seq('(', commaSep($._type), ')'),
    array_type: $ => seq('[', $._type, optional(seq(';', $._expression)), ']'),
    function_type: $ => prec.right(seq('fn', optional($.generic_parameters), '(', commaSep($._type), ')', '->', optional($._type), optional(seq('/', $.effect_row)))),
    never_type: _ => '!',
    inferred_type: _ => '_',

    block: $ => seq('{', repeat($.statement), optional($._expression), '}'),
    statement: $ => choice(
      $.let_statement,
      $.assignment_statement,
      $.expression_statement,
      $.empty_statement,
    ),
    let_statement: $ => prec.right(seq('let', choice($.identifier, $.deconstruction_pattern), optional(seq(':', $._type)), '=', $._expression, optional(';'))),
    assignment_statement: $ => seq(field('left', $._expression), '=', field('right', $._expression), ';'),
    expression_statement: $ => seq($._expression, ';'),
    empty_statement: _ => ';',

    _expression: $ => choice(
      $.literal,
      $.path_expression,
      $.unit_expression,
      $.parenthesized_expression,
      $.tuple_expression,
      $.list_expression,
      $.block,
      $.closure_expression,
      $.typed_closure_expression,
      $.struct_expression,
      $.control_application,
      $.context_application,
      $.call_expression,
      $.field_expression,
      $.unary_expression,
      $.binary_expression,
      $.pattern_test_expression,
      $.match_expression,
      $.handle_expression,
      $.perform_expression,
      $.resumption_expression,
      $.label_expression,
      $.leave_expression,
    ),
    path_expression: $ => prec(1, path($)),
    unit_expression: _ => seq('(', ')'),
    parenthesized_expression: $ => seq('(', $._expression, ')'),
    tuple_expression: $ => seq('(', $._expression, ',', commaSep($._expression), ')'),
    list_expression: $ => seq('[', commaSep($._expression), ']'),
    closure_expression: $ => choice(
      prec(30, seq('{', '(', commaSep($.identifier), ')', '=>', $._expression, '}')),
      prec.dynamic(2, seq('{', commaSep($.identifier), '=>', $._expression, '}')),
    ),
    typed_closure_expression: $ => seq($.parameters, '->', optional($._type), optional(seq('/', $.effect_row)), $.block),
    struct_expression: $ => prec(20, seq(field('type', $.identifier), '{', commaSep($.field_initializer), '}')),
    field_initializer: $ => seq(field('name', $.identifier), ':', field('value', $._expression)),
    call_expression: $ => prec.left(12, seq(field('function', $._expression), field('arguments', $.arguments))),
    control_application: $ => prec.left(10, seq(
      field('function', alias(choice('loop', 'while', 'until'), $.identifier)),
      repeat1(field('context', $._context_argument)),
    )),
    context_application: $ => prec.left(10, seq(
      field('function', $.call_expression),
      repeat1(field('context', $._context_argument)),
    )),
    _context_argument: $ => choice($.block, $.closure_expression, $.label_expression),
    arguments: $ => seq('(', commaSep($._expression), ')'),
    field_expression: $ => prec.left(13, seq(field('value', $._expression), '.', field('field', choice($.identifier, $.integer_literal)))),
    unary_expression: $ => prec(11, seq(field('operator', choice('-', '&', seq('&', 'mut'), '*', 'move', $.operator, $.word_operator)), field('operand', $._expression))),
    binary_expression: $ => prec.left(5, seq(field('left', $._expression), field('operator', choice($.operator_sequence, $.word_operator)), field('right', $._expression))),
    pattern_test_expression: $ => prec.left(3, seq(field('value', $._expression), 'is', field('pattern', $._pattern))),
    match_expression: $ => prec(14, seq('match', '(', field('value', $._expression), ')', '{', repeat1($.match_arm), '}')),
    match_arm: $ => seq(field('pattern', $._pattern), '=>', field('body', $._expression), optional(choice(',', ';'))),
    handle_expression: $ => prec.right(seq('handle', field('computation', $._expression), '{', repeat(choice($.handler_clause, $.elided_handler_clause)), '}')),
    effect_reference: $ => seq($.effect_identifier, optional($.generic_arguments)),
    handler_clause: $ => prec.dynamic(2, seq(field('effect', $.effect_reference), '::', field('operation', $.effect_operation_identifier), '(', commaSep($._pattern), ')', optional(seq('with', field('resumption', $.identifier))), '=>', field('body', $._expression), optional(choice(',', ';')))),
    elided_handler_clause: $ => prec.dynamic(1, seq(field('pattern', $._elided_handler_pattern), '=>', field('body', $._expression), optional(choice(',', ';')))),
    perform_expression: $ => seq('perform', field('effect', $.effect_reference), '::', field('operation', $.effect_operation_identifier), $.arguments),
    resumption_expression: $ => seq(choice('resume', 'cancel', 'tail'), $.arguments),
    label_expression: $ => choice(seq('label', $.label), seq($.label, ':', $.block)),
    leave_expression: $ => prec.right(seq('leave', optional($.label), optional($._expression))),

    _pattern: $ => choice($.path_pattern, $.identifier, $.literal_pattern, $.tuple_pattern, $.variant_pattern, $.struct_pattern),
    _elided_handler_pattern: $ => choice($.identifier, $.literal_pattern, $.tuple_pattern, $.elided_variant_pattern, $.struct_pattern),
    elided_variant_pattern: $ => prec(11, seq(
      field('type', choice('Result', 'Option')),
      '::',
      field('variant', $.identifier),
      '(',
      commaSep($._pattern),
      ')',
    )),
    path_pattern: $ => prec(9, seq($.identifier, '::', $.identifier, repeat(seq('::', $.identifier)))),
    literal_pattern: $ => $.literal,
    tuple_pattern: $ => seq('(', commaSep($._pattern), ')'),
    variant_pattern: $ => prec(10, seq(
      field('type', $.identifier),
      repeat(seq('::', $.identifier)),
      '::',
      field('variant', $.variant_identifier),
      '(',
      commaSep($._pattern),
      ')',
    )),
    struct_pattern: $ => prec(20, seq($.identifier, '{', commaSep(choice('..', seq($.identifier, optional(seq(':', $._pattern))))), '}')),
    deconstruction_pattern: $ => choice($.tuple_pattern, $.struct_pattern),

    literal: $ => choice($.integer_literal, $.float_literal, $.string_literal, $.char_literal, $.byte_literal, $.byte_string_literal, $.boolean_literal),
    boolean_literal: _ => choice('true', 'false'),
    integer_literal: _ => token(choice(/0[bB]_?[01](?:_?[01])*/, /0[oO]_?[0-7](?:_?[0-7])*/, /0[xX]_?[0-9a-fA-F](?:_?[0-9a-fA-F])*/, /[0-9](?:_?[0-9])*/)),
    float_literal: _ => token(/[0-9](?:_?[0-9])*\.[0-9](?:_?[0-9])*(?:[eE][+-]?[0-9](?:_?[0-9])*)?|[0-9](?:_?[0-9])*[eE][+-]?[0-9](?:_?[0-9])*/),
    string_literal: _ => token(seq('"', repeat(choice(/[^"\\\n]/, /\\(?:[nrt0"'\\]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]+\})/)), '"')),
    char_literal: _ => token(seq("'", choice(/[^'\\\n]/, /\\(?:[nrt0"'\\]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]+\})/), "'")),
    byte_literal: _ => token(seq("b'", choice(/[^'\\\n]/, /\\(?:[nrt0'\\]|x[0-9a-fA-F]{2})/), "'")),
    byte_string_literal: _ => token(seq('b"', repeat(choice(/[^"\\\n]/, /\\(?:[nrt0"\\]|x[0-9a-fA-F]{2})/)), '"')),
    lifetime: _ => token(seq("'", /[A-Za-z_][A-Za-z0-9_]*/)),
    label: _ => token(seq('@', /[A-Za-z_][A-Za-z0-9_]*/)),
    identifier: _ => /[A-Za-z_][A-Za-z0-9_]*/,
    type_identifier: $ => alias($.identifier, $.type_identifier),
    variant_identifier: $ => alias($.identifier, $.variant_identifier),
    effect_identifier: $ => alias($.identifier, $.effect_identifier),
    effect_operation_identifier: $ => alias($.identifier, $.effect_operation_identifier),
    // Word operators are contextual in the compiler. Tree-sitter cannot alter
    // its lexer from a file-local fixity table, so this names the operators in
    // the distributed library while symbolic operators remain fully open.
    word_operator: _ => choice('and', 'or', 'else', 'not', 'represents'),
    builtin_operator: _ => choice('==', '!=', '<=', '>=', '..', '+', '-', '*', '/', '%', '<', '>', '&', '|'),
    operator_sequence: $ => prec.right(repeat1(choice($.builtin_operator, $.operator))),
    operator: _ => token(prec(-1, /[!#$%&*+\-.\/<=>?^|~]+/)),
    line_comment: _ => token(seq('//', /[^\n]*/)),
    block_comment: _ => token(seq('/*', repeat(choice(/[^*/]+/, /\*+[^*/]/, /\/+[^*/]/)), '*/')),
  },
});

function sep1(rule, separator) {
  return seq(rule, repeat(seq(separator, rule)));
}
