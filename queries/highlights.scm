[(line_comment) (block_comment)] @comment
[(string_literal) (char_literal) (byte_literal) (byte_string_literal)] @string
[(integer_literal) (float_literal)] @number
(boolean_literal) @boolean
(lifetime) @variable.special
(label) @label
[(type_identifier)
 (struct_expression type: (identifier))
 (effect_reference (identifier))] @type

(struct_declaration name: (type_identifier) @type)
(enum_declaration name: (type_identifier) @type)
(trait_declaration name: (type_identifier) @type)
(effect_declaration name: (type_identifier) @type)

(enum_variant name: (variant_identifier) @constructor)

(field_declaration name: (identifier) @property)
(field_initializer name: (identifier) @property)
(field_expression field: (identifier) @property)

(parameter name: (identifier) @variable.parameter)
(generic_parameter (identifier) @variable.parameter)

(let_statement (identifier) @variable)

(function_declaration name: (identifier) @function)
(function_signature name: (identifier) @function)
(effect_operation name: (identifier) @function)

(call_expression
  function: (path_expression . (identifier) @function.call .))
(call_expression
  function: (path_expression
    (identifier) @function.method .
    (#match? @function.method "^[a-z_]")))

(handler_clause operation: (identifier) @function.method)
(perform_expression operation: (identifier) @function.method)

; Qualified uppercase values such as `Result::Ok` and
; `Instruction::MoveRight` are enum constructors. A qualified call is instead
; captured as a function by the call-expression rule above.
(path_expression
  (identifier) @type
  (identifier) @constructor .
  (#match? @constructor "^[A-Z]"))
[(word_operator) (builtin_operator) (operator)] @operator
[
 "mod" "use" "as" "self" "type" "cases" "let"
 "struct" "enum" "trait" "impl" "effect" "where" "for" "const"
 "handle" "perform" "resume" "cancel" "tail" "label" "leave" "is"
 "with" "move" "mut"
] @keyword
