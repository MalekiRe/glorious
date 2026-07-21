[(line_comment) (block_comment)] @comment

[(string_literal) (char_literal) (byte_literal) (byte_string_literal)] @string
[(integer_literal) (float_literal)] @number
(boolean_literal) @boolean
(lifetime) @variable.special
(label) @label

(type_identifier) @type
(struct_declaration name: (type_identifier) @type)
(enum_declaration name: (type_identifier) @type)
(trait_declaration name: (type_identifier) @type)
(effect_declaration name: (type_identifier) @type)

(enum_variant name: (variant_identifier) @constructor)
(struct_expression type: (identifier) @type)
(effect_reference (identifier) @type)

(function_declaration name: (identifier) @function)
(function_signature name: (identifier) @function)
(effect_operation name: (identifier) @function)
(call_expression
  function: (path_expression . (identifier) @function.call .))
(call_expression
  function: (path_expression
    (identifier) @function.method .
    (#match? @function.method "^[a-z_]")))
(path_expression
  (identifier) @type
  (identifier) @constructor .
  (#match? @constructor "^[A-Z]"))
(field_expression field: (identifier) @property)
(field_declaration name: (identifier) @property)
(field_initializer name: (identifier) @property)

(parameter name: (identifier) @variable.parameter)
(generic_parameter (identifier) @variable.parameter)
(let_statement (identifier) @variable)

(handler_clause operation: (identifier) @function.method)
(perform_expression operation: (identifier) @function.method)

[
 "mod" "use" "as" "self" "type" "cases" "let"
 "struct" "enum" "trait" "impl" "effect" "where" "for" "const"
 "handle" "perform" "resume" "cancel" "tail" "label" "leave" "is"
 "with" "move" "mut"
] @keyword

[(word_operator) (builtin_operator) (operator)] @operator
[(visibility_modifier) (field_visibility_modifier)] @keyword.modifier
[("(" ")" "[" "]" "{" "}")] @punctuation.bracket
[("," ";" ":" "::" ".")] @punctuation.delimiter
