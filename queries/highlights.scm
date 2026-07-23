[(line_comment) (block_comment)] @comment
[(string_literal) (char_literal) (byte_literal) (byte_string_literal)] @string
[(integer_literal) (float_literal)] @number
(boolean_literal) @boolean
(lifetime) @variable.special
(label) @label
(type_identifier) @type
(struct_expression type: (identifier) @type)
(struct_pattern (identifier) @type . "{")

(struct_declaration name: (type_identifier) @type)
(trait_declaration name: (type_identifier) @type)
(enum_declaration name: (type_identifier) @type @enum)

; Effects and their operations are distinct semantic namespaces.  Giving either
; one an overlapping type/function capture makes clients such as Zed choose the
; ordinary declaration colour and obscures handlers at a glance.
(effect_identifier) @tag
(effect_operation_identifier) @variant

(enum_variant name: (variant_identifier) @constructor)
(variant_pattern
  type: (identifier) @type
  variant: (variant_identifier) @constructor)
(field_declaration name: (identifier) @property)
(field_initializer name: (identifier) @property)
(field_expression field: (identifier) @property)
(struct_pattern "{" (identifier) @property)

(parameter name: (identifier) @variable.parameter)
(generic_parameter (identifier) @variable.parameter)
(handler_clause (identifier) @variable.parameter)
(legacy_handler_clause continuation: (identifier) @variable.parameter)
; A new-surface operation arm and a qualified completion pattern are
; syntactically identical. The compiler resolves them from effect declarations;
; Tree-sitter uses the lowercase operation convention for highlighting.
(handler_completion_arm
  pattern: (variant_pattern
    type: (identifier) @tag
    variant: (variant_identifier) @variant
    (#match? @variant "^[a-z_]")))

(let_statement (identifier) @variable)

(function_declaration name: (identifier) @function)
(function_signature name: (identifier) @function)

(call_expression
  function: (path_expression . (identifier) @function.call .))
(call_expression
  function: (path_expression
    (identifier) @function.method .
    (#match? @function.method "^[a-z_]")))


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
 "handle" "perform" "resume" "cancel" "tail" "label" "leave" "is" "match"
 "with" "move" "mut"
] @keyword
