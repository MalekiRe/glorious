[(line_comment) (block_comment)] @comment

[(string_literal) (char_literal) (byte_literal) (byte_string_literal)] @string
[(integer_literal) (float_literal)] @number
(boolean_literal) @boolean
(lifetime) @variable.special
(label) @label

[(type_identifier) (type_path name: (type_identifier))] @type
[(struct_declaration name: (type_identifier))
 (enum_declaration name: (type_identifier))
 (trait_declaration name: (type_identifier))
 (effect_declaration name: (type_identifier))] @type

[(function_declaration name: (identifier))
 (function_signature name: (identifier))
 (effect_operation name: (identifier))] @function
(call_expression function: (path_expression (identifier) @function.call))
(field_expression field: (identifier) @property)
(field_declaration name: (identifier) @property)
(field_initializer name: (identifier) @property)

[(parameter name: (identifier))
 (generic_parameter (identifier))] @variable.parameter

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
