[(line_comment) (block_comment)] @comment
[(string_literal) (char_literal) (byte_literal) (byte_string_literal)] @string
[(integer_literal) (float_literal)] @number
(boolean_literal) @boolean
(lifetime) @variable.special
(label) @label
(type_identifier) @type
[(function_declaration name: (identifier))
 (function_signature name: (identifier))
 (effect_operation name: (identifier))] @function
[(word_operator) (builtin_operator) (operator)] @operator
[
 "mod" "use" "as" "self" "type" "cases" "let"
 "struct" "enum" "trait" "impl" "effect" "where" "for" "const"
 "handle" "perform" "resume" "cancel" "tail" "label" "leave" "is"
 "with" "move" "mut"
] @keyword
