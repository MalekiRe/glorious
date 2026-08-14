//! Demand-driven, body-local syntax parsing.
//!
//! The parser receives a declaration body range from structural scanning and
//! releases its arena after elaboration. It intentionally preserves flat
//! operator chains and contextual blocks; fixity and expected-type decisions
//! belong to later semantic queries, not parser heuristics.

use crate::{
    header::{EffectRowHeader, HeaderGenericArgument, HeaderType},
    quantity::Quantity,
    scanner::TokenRange,
    source::{LexedFile, Span, TokenKind},
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExprId(pub u32);

/// Body-local identity for a structural G1 pattern.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PatternId(pub u32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternKind {
    Wildcard,
    Binding(String),
    Literal(String),
    Tuple(Vec<PatternId>),
    Record {
        path: Vec<String>,
        fields: Vec<(String, PatternId)>,
    },
    Enum {
        path: Vec<String>,
        fields: Vec<PatternId>,
    },
    Recovered,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

/// One source-order handler arm. Effect and operation paths remain syntactic
/// until Typed Core resolves them against frozen interfaces.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HandlerClause {
    /// The structural pattern spelling of this arm. An operation-shaped arm
    /// keeps this too: Core classifies it only after effect-name resolution.
    pub completion: Option<PatternId>,
    /// True when the source had `Path::operation(patterns)` form. This is a
    /// syntax candidate, not an arm kind: an equally shaped enum constructor
    /// is a normal-completion pattern unless it resolves as an operation.
    pub operation_candidate: bool,
    pub path: Vec<String>,
    /// Type arguments on the protocol portion of `Protocol<Args>::operation`.
    /// Protocol arguments establish the nominal effect-instance identity.
    pub effect_arguments: Vec<HeaderType>,
    /// Type arguments applied to the operation itself, after its final path
    /// segment: `Effect::operation<T>(...)`. These are distinct from the
    /// protocol arguments above, since only protocol arguments contribute to
    /// the nominal runtime effect-instance identity.
    pub operation_arguments: Vec<HeaderType>,
    pub patterns: Vec<PatternId>,
    pub resumption: Option<String>,
    /// The final unified arm pattern was `_`, spelling a discarded
    /// continuation rather than a tail-resume result.
    pub discard_resumption: bool,
    pub body: ExprId,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExprKind {
    Literal(String),
    Path(Vec<String>),
    /// A path with explicit source type arguments. Namespace resolution owns
    /// whether it denotes an effect protocol, nominal constructor, or another
    /// generic entity; the parser must not guess from its spelling.
    GenericPath {
        path: Vec<String>,
        /// Type arguments applied to the leading protocol or trait path,
        /// before `::`: `Effect<T>::operation`.
        effect_arguments: Vec<HeaderType>,
        /// Type arguments applied to the final operation or method path,
        /// after `::`: `Effect::operation<T>`.
        operation_arguments: Vec<HeaderType>,
    },
    Tuple(Vec<ExprId>),
    /// Finite machine-array construction. Its element type is inferred by
    /// Typed Core; the parser deliberately stores no type-directed facts.
    Array(Vec<ExprId>),
    /// Named record construction. The path remains syntactic until Typed Core
    /// resolves it in the type namespace against a frozen nominal layout.
    Record {
        path: Vec<String>,
        fields: Vec<(String, ExprId)>,
    },
    Block(Vec<ExprId>),
    ContextualBlock(Vec<ExprId>),
    /// Compact, inferred callable syntax: `{x, y => expression}`.
    Closure {
        parameters: Vec<String>,
        body: ExprId,
    },
    /// Explicit callable syntax: `(x: T, y: U) -> R / {E | e} { body }`.
    /// Header terms remain syntactic here; signature/type elaboration owns
    /// their semantic meaning and any contextual callable selection.
    TypedClosure {
        parameters: Vec<ClosureParameter>,
        result: Option<HeaderType>,
        effects: EffectRowHeader,
        body: ExprId,
    },
    Let {
        name: String,
        value: ExprId,
    },
    Call {
        callee: ExprId,
        arguments: Vec<ExprId>,
    },
    Field {
        base: ExprId,
        name: String,
    },
    Move(ExprId),
    Prefix {
        operator: String,
        value: ExprId,
    },
    Borrow {
        unique: bool,
        value: ExprId,
    },
    Assign {
        place: ExprId,
        value: ExprId,
    },
    /// The sole compiler-level structural test. It becomes a Test/Bindings
    /// result during semantic elaboration, not compiler-known control flow.
    Is {
        subject: ExprId,
        pattern: PatternId,
    },
    /// Structural handler syntax. Core owns operation selection and control
    /// semantics after all declaration interfaces are available.
    Handle {
        computation: ExprId,
        clauses: Vec<HandlerClause>,
    },
    OperatorChain {
        operands: Vec<ExprId>,
        operators: Vec<String>,
    },
    Recovered,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosureParameter {
    pub name: String,
    pub ty: Option<HeaderType>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BodyDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: &'static str,
}

#[derive(Clone, Debug)]
pub struct BodySyntax {
    pub expressions: Vec<Expr>,
    pub patterns: Vec<Pattern>,
    pub root: ExprId,
    pub diagnostics: Vec<BodyDiagnostic>,
    pub recovered: bool,
}

impl BodySyntax {
    pub fn parse(lexed: &LexedFile, source: &str, range: TokenRange) -> Self {
        Self::parse_with(lexed, source, range, |parser| parser.parse_block(false))
    }

    /// Parse a body-shaped expression that is not enclosed in declaration
    /// braces. Constant initializers use this path while retaining the same
    /// demand-driven AST, diagnostics, and fixity-later operator chains.
    pub fn parse_expression(lexed: &LexedFile, source: &str, range: TokenRange) -> Self {
        Self::parse_with(lexed, source, range, |parser| parser.parse_expression())
    }

    fn parse_with(
        lexed: &LexedFile,
        source: &str,
        range: TokenRange,
        parse: impl FnOnce(&mut Parser<'_>) -> Option<ExprId>,
    ) -> Self {
        let tokens = lexed.tokens[range.start..range.end]
            .iter()
            .enumerate()
            .filter_map(|(offset, token)| (!is_trivia(&token.kind)).then_some(range.start + offset))
            .collect::<Vec<_>>();
        let mut parser = Parser {
            lexed,
            source,
            tokens,
            position: 0,
            expressions: vec![],
            patterns: vec![],
            diagnostics: vec![],
            recovered: false,
            handler_computation: false,
        };
        let root = parse(&mut parser).unwrap_or_else(|| parser.recover_root());
        if parser.current().is_some() {
            parser.error_current("G4010", "unexpected trailing token after expression");
        }
        parser
            .diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        Self {
            expressions: parser.expressions,
            patterns: parser.patterns,
            root,
            diagnostics: parser.diagnostics,
            recovered: parser.recovered,
        }
    }

    pub fn expression(&self, id: ExprId) -> &Expr {
        &self.expressions[id.0 as usize]
    }
    pub fn pattern(&self, id: PatternId) -> &Pattern {
        &self.patterns[id.0 as usize]
    }
}

struct Parser<'a> {
    lexed: &'a LexedFile,
    source: &'a str,
    tokens: Vec<usize>,
    position: usize,
    expressions: Vec<Expr>,
    patterns: Vec<Pattern>,
    diagnostics: Vec<BodyDiagnostic>,
    recovered: bool,
    handler_computation: bool,
}

impl Parser<'_> {
    fn parse_block(&mut self, contextual: bool) -> Option<ExprId> {
        let open = self.expect_punctuation('{')?;
        let mut expressions = vec![];
        while !self.at_punctuation('}') && self.current().is_some() {
            let expression = self
                .parse_statement()
                .unwrap_or_else(|| self.recover_expression());
            let assignment = matches!(self.expression(expression).kind, ExprKind::Assign { .. });
            expressions.push(expression);
            if self.at_punctuation(';') {
                self.position += 1;
            } else if assignment {
                self.error_current("G4015", "assignment statements require a trailing `;`");
                self.synchronize();
            } else if !self.at_punctuation('}') && self.current().is_some() {
                self.error_current("G4001", "expected `;` or `}` after expression");
                self.synchronize();
            }
        }
        let close = self.expect_punctuation('}').unwrap_or(open);
        let span = Span {
            file: self.lexed.file,
            start: self.lexed.tokens[open].span.start,
            end: self.lexed.tokens[close].span.end,
        };
        Some(self.alloc(
            if contextual {
                ExprKind::ContextualBlock(expressions)
            } else {
                ExprKind::Block(expressions)
            },
            span,
        ))
    }

    fn parse_expression(&mut self) -> Option<ExprId> {
        if self.word() == Some("let") {
            return self.parse_let();
        }
        let expression = self.parse_prefix()?;
        self.finish_expression(expression)
    }

    /// Assignment belongs only to the statement grammar.  Keeping it out of
    /// the expression parser rejects both chained assignments and accidental
    /// operand-position writes before Typed Core is built.
    fn parse_statement(&mut self) -> Option<ExprId> {
        if self.word() == Some("let") {
            return self.parse_let();
        }
        let expression = self.parse_prefix()?;
        if self.at_operator("=") {
            self.position += 1;
            let value = self
                .parse_expression()
                .unwrap_or_else(|| self.recover_expression());
            let span = join(
                self.expression(expression).span,
                self.expression(value).span,
            );
            return Some(self.alloc(
                ExprKind::Assign {
                    place: expression,
                    value,
                },
                span,
            ));
        }
        self.finish_expression(expression)
    }

    fn finish_expression(&mut self, mut expression: ExprId) -> Option<ExprId> {
        while self.word() == Some("else") {
            let else_token = self.advance()?;
            let negative = if self.at_punctuation('{') {
                self.parse_block(true)?
            } else {
                self.parse_prefix()
                    .unwrap_or_else(|| self.recover_expression())
            };
            let callee = self.alloc(
                ExprKind::Path(vec!["else".into()]),
                self.lexed.tokens[else_token].span,
            );
            let span = join(
                self.expression(expression).span,
                self.expression(negative).span,
            );
            expression = self.alloc(
                ExprKind::Call {
                    callee,
                    arguments: vec![expression, negative],
                },
                span,
            );
        }
        if self.word() == Some("is") {
            let is_token = self.advance()?;
            let mut binders = std::collections::BTreeSet::new();
            let pattern = self
                .parse_pattern(&mut binders)
                .unwrap_or_else(|| self.recover_pattern());
            let span = join(self.expression(expression).span, self.pattern(pattern).span);
            expression = self.alloc(
                ExprKind::Is {
                    subject: expression,
                    pattern,
                },
                join(self.lexed.tokens[is_token].span, span),
            );
        }
        let mut operands = vec![expression];
        let mut operators = vec![];
        while let Some(operator) = self.infix_operator().map(str::to_owned) {
            self.position += 1;
            let rhs = self
                .parse_prefix()
                .unwrap_or_else(|| self.recover_expression());
            operators.push(operator);
            operands.push(rhs);
        }
        (operators.is_empty()).then_some(operands[0]).or_else(|| {
            let span = join(
                self.expression(operands[0]).span,
                self.expression(*operands.last().unwrap()).span,
            );
            Some(self.alloc(
                ExprKind::OperatorChain {
                    operands,
                    operators,
                },
                span,
            ))
        })
    }

    fn parse_prefix(&mut self) -> Option<ExprId> {
        if self.word() == Some("handle") {
            return self.parse_handle();
        }
        // `perform` is legacy spelling around the canonical effect operation
        // application. Its semantic identity is still established from the
        // following `Protocol::operation(...)` path in Typed Core.
        if self.word() == Some("perform") {
            self.advance()?;
            return self.parse_prefix();
        }
        if self.word() == Some("move") {
            let start = self.advance()?;
            let value = self
                .parse_prefix()
                .unwrap_or_else(|| self.recover_expression());
            return Some(self.alloc(
                ExprKind::Move(value),
                join(self.lexed.tokens[start].span, self.expression(value).span),
            ));
        }
        if self.at_operator("&") {
            let start = self.advance()?;
            let unique = if self.at_operator("mut") || self.word() == Some("mut") {
                self.position += 1;
                true
            } else {
                false
            };
            let value = self
                .parse_prefix()
                .unwrap_or_else(|| self.recover_expression());
            return Some(self.alloc(
                ExprKind::Borrow { unique, value },
                join(self.lexed.tokens[start].span, self.expression(value).span),
            ));
        }
        if let Some(operator) = self.operator().map(str::to_owned)
            && matches!(operator.as_str(), "+" | "-" | "!")
        {
            let start = self.advance()?;
            let value = self
                .parse_prefix()
                .unwrap_or_else(|| self.recover_expression());
            return Some(self.alloc(
                ExprKind::Prefix { operator, value },
                join(self.lexed.tokens[start].span, self.expression(value).span),
            ));
        }
        let mut value = self.parse_atom()?;
        loop {
            if self.at_punctuation('(') {
                value = self.parse_call(value)?;
            } else if self.at_punctuation('.') {
                let start = self.expression(value).span;
                self.position += 1;
                let name = self.expect_identifier()?;
                let span = join(
                    start,
                    self.lexed.tokens[self.tokens[self.position - 1]].span,
                );
                value = self.alloc(ExprKind::Field { base: value, name }, span);
            } else if self.at_punctuation('{')
                && matches!(self.expression(value).kind, ExprKind::Path(_))
                && self.record_literal_ahead()
            {
                let ExprKind::Path(path) = self.expression(value).kind.clone() else {
                    unreachable!("record lookahead follows only a parsed atom")
                };
                value = self.parse_record(path, self.expression(value).span)?;
            } else if self.at_punctuation('{') && !self.handler_computation {
                let block = self.parse_block(true)?;
                let span = join(self.expression(value).span, self.expression(block).span);
                value = self.alloc(
                    ExprKind::Call {
                        callee: value,
                        arguments: vec![block],
                    },
                    span,
                );
            } else {
                break;
            }
        }
        Some(value)
    }

    fn parse_handle(&mut self) -> Option<ExprId> {
        let start = self.advance()?;
        let computation = if self.at_punctuation('{') {
            self.parse_block(false)?
        } else {
            let previous = self.handler_computation;
            self.handler_computation = true;
            let computation = self.parse_prefix();
            self.handler_computation = previous;
            computation?
        };
        if !self.at_punctuation('{') {
            self.error_current("G4022", "expected `{` and handler clauses");
            return None;
        }
        self.position += 1;
        let mut clauses = vec![];
        while self.current().is_some() && !self.at_punctuation('}') {
            let clause_start = self.current()?;
            // An arm that cannot start an effect-qualified path is necessarily
            // a normal-completion pattern. A bare identifier immediately
            // followed by `=>` is also unambiguous. Qualified constructor
            // forms are preserved as candidates and classified by Core after
            // effect-name resolution.
            let completion_ahead = self.current().is_some_and(|token| {
                !matches!(self.lexed.tokens[token].kind, TokenKind::Identifier)
                    || self.tokens.get(self.position + 1).is_some_and(|next| {
                        self.lexed.tokens[*next].kind == TokenKind::Operator
                            && self.text(*next) == "=>"
                    })
            });
            if completion_ahead {
                clauses.push(self.parse_completion_clause(clause_start)?);
                continue;
            }
            let clause_position = self.position;
            let (path, effect_arguments, operation_arguments) = self.parse_effect_path()?;
            // `Type::Variant` and `Type { field: ... }` are completion
            // patterns, not malformed operation arms. Rewind and parse the
            // structural pattern so its nominal type can be resolved later.
            if !self.at_punctuation('(') {
                self.position = clause_position;
                clauses.push(self.parse_completion_clause(clause_start)?);
                continue;
            }
            if self.expect_punctuation('(').is_none() {
                self.error_current("G4023", "expected `(` after handler operation path");
                return None;
            }
            let mut patterns = vec![];
            let mut binders = std::collections::BTreeSet::new();
            while !self.at_punctuation(')') && self.current().is_some() {
                patterns.push(
                    self.parse_pattern(&mut binders)
                        .unwrap_or_else(|| self.recover_pattern()),
                );
                if !self.at_punctuation(',') {
                    break;
                }
                self.position += 1;
            }
            self.expect_punctuation(')')?;
            let completion = self.alloc_pattern(
                PatternKind::Enum {
                    path: path.clone(),
                    fields: patterns.clone(),
                },
                join(
                    self.lexed.tokens[clause_start].span,
                    self.lexed.tokens[self.tokens[self.position - 1]].span,
                ),
            );
            let (resumption, discard_resumption) = if self.word() == Some("with") {
                self.position += 1;
                let continuation = self.current()?;
                let name = self.expect_identifier()?;
                // `_` is the explicit full-control spelling for abandoning a
                // continuation.  It is not a source-level callable named
                // `_`: preserving that distinction lets Core enforce the
                // operation's quantitative cancellation contract.
                if name == "_" {
                    (None, true)
                } else {
                    // Payload patterns and the explicit continuation inhabit
                    // one handler-clause scope.  Do not silently shadow a
                    // payload binder with the generated callable identity.
                    if !binders.insert(name.clone()) {
                        self.error_at(
                            self.lexed.tokens[continuation].span,
                            "G4017",
                            "duplicate binder in one handler clause",
                        );
                    }
                    (Some(name), false)
                }
            } else {
                (None, false)
            };
            if !self.at_operator("=>") {
                self.error_current("G4024", "expected `=>` before handler clause body");
                return None;
            }
            self.position += 1;
            let body = self
                .parse_expression()
                .unwrap_or_else(|| self.recover_expression());
            let span = join(
                self.lexed.tokens[clause_start].span,
                self.expression(body).span,
            );
            clauses.push(HandlerClause {
                completion: Some(completion),
                operation_candidate: true,
                path,
                effect_arguments,
                operation_arguments,
                patterns,
                resumption,
                discard_resumption,
                body,
                span,
            });
            if self.at_punctuation(',') || self.at_punctuation(';') {
                self.position += 1;
            } else if !self.at_punctuation('}') {
                self.error_current("G4025", "expected `,` or `}` after handler clause");
                return None;
            }
        }
        let close = self.expect_punctuation('}')?;
        Some(self.alloc(
            ExprKind::Handle {
                computation,
                clauses,
            },
            join(self.lexed.tokens[start].span, self.lexed.tokens[close].span),
        ))
    }

    fn parse_completion_clause(&mut self, clause_start: usize) -> Option<HandlerClause> {
        let mut binders = std::collections::BTreeSet::new();
        let pattern = self.parse_pattern(&mut binders)?;
        if !self.at_operator("=>") {
            self.error_current("G4024", "expected `=>` before handler clause body");
            return None;
        }
        self.position += 1;
        let body = self
            .parse_expression()
            .unwrap_or_else(|| self.recover_expression());
        let span = join(
            self.lexed.tokens[clause_start].span,
            self.expression(body).span,
        );
        if self.at_punctuation(',') || self.at_punctuation(';') {
            self.position += 1;
        }
        Some(HandlerClause {
            completion: Some(pattern),
            operation_candidate: false,
            path: vec![],
            effect_arguments: vec![],
            operation_arguments: vec![],
            patterns: vec![],
            resumption: None,
            discard_resumption: false,
            body,
            span,
        })
    }

    fn parse_effect_path(&mut self) -> Option<(Vec<String>, Vec<HeaderType>, Vec<HeaderType>)> {
        let first = self.expect_identifier()?;
        let mut effect_arguments = vec![];
        if self.generic_path_ahead() {
            self.position += 1;
            while !self.at_operator(">") && self.current().is_some() {
                effect_arguments.push(self.closure_type()?);
                if !self.at_punctuation(',') {
                    break;
                }
                self.position += 1;
            }
            if !self.at_operator(">") {
                self.error_current("G4026", "expected `>` in handler effect application");
                return None;
            }
            self.position += 1;
        }
        let mut path = vec![first];
        while self.at_punctuation(':') && self.peek_punctuation(1, ':') {
            self.position += 2;
            path.push(self.expect_identifier()?);
        }
        let operation_arguments = if path.len() > 1 && self.operation_generic_ahead() {
            self.parse_type_arguments("G4026", "expected `>` in handler operation application")?
        } else {
            vec![]
        };
        Some((path, effect_arguments, operation_arguments))
    }

    fn record_literal_ahead(&self) -> bool {
        let Some(name) = self.tokens.get(self.position + 1).copied() else {
            return false;
        };
        let Some(colon) = self.tokens.get(self.position + 2).copied() else {
            return false;
        };
        self.lexed.tokens[name].kind == TokenKind::Identifier
            && self.lexed.tokens[colon].kind == TokenKind::Punctuation(':')
            // A qualified handler arm begins `Type::Variant`; its first
            // colon must never be mistaken for a record-field separator while
            // parsing the `handle` scrutinee.
            && !self.peek_punctuation(3, ':')
    }

    /// `<` is also an ordinary infix comparison operator.  Treat it as a
    /// source type application only when its balanced closing `>` is followed
    /// by `::`, which is the unambiguous generic-path form admitted by this
    /// body grammar (`Protocol<T>::operation`).
    fn generic_path_ahead(&self) -> bool {
        if !self.at_operator("<") {
            return false;
        }
        let mut depth = 0u32;
        for position in self.position..self.tokens.len() {
            let token = self.tokens[position];
            if self.lexed.tokens[token].kind == TokenKind::Operator {
                match self.text(token) {
                    "<" => depth += 1,
                    ">" => {
                        if depth == 0 {
                            return false;
                        }
                        depth -= 1;
                        if depth == 0 {
                            return matches!(
                                (self.tokens.get(position + 1), self.tokens.get(position + 2)),
                                (Some(first), Some(second))
                                    if self.lexed.tokens[*first].kind == TokenKind::Punctuation(':')
                                        && self.lexed.tokens[*second].kind == TokenKind::Punctuation(':')
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        false
    }

    /// Final-segment type arguments are unambiguous only when followed by a
    /// call/pattern argument list. This prevents ordinary `value < other`
    /// comparisons from being parsed as generic applications.
    fn operation_generic_ahead(&self) -> bool {
        if !self.at_operator("<") {
            return false;
        }
        let mut depth = 0u32;
        for position in self.position..self.tokens.len() {
            let token = self.tokens[position];
            if self.lexed.tokens[token].kind != TokenKind::Operator {
                continue;
            }
            match self.text(token) {
                "<" => depth += 1,
                ">" if depth > 0 => {
                    depth -= 1;
                    if depth == 0 {
                        return self.tokens.get(position + 1).is_some_and(|next| {
                            self.lexed.tokens[*next].kind == TokenKind::Punctuation('(')
                        });
                    }
                }
                ">" => return false,
                _ => {}
            }
        }
        false
    }

    fn parse_type_arguments(
        &mut self,
        code: &'static str,
        missing_message: &'static str,
    ) -> Option<Vec<HeaderType>> {
        if !self.at_operator("<") {
            return Some(vec![]);
        }
        self.position += 1;
        let mut arguments = vec![];
        while !self.at_operator(">") && self.current().is_some() {
            arguments.push(self.closure_type()?);
            if !self.at_punctuation(',') {
                break;
            }
            self.position += 1;
        }
        if !self.at_operator(">") {
            self.error_current(code, missing_message);
            return None;
        }
        self.position += 1;
        Some(arguments)
    }

    fn parse_record(&mut self, path: Vec<String>, start: Span) -> Option<ExprId> {
        self.expect_punctuation('{')?;
        let mut fields = vec![];
        while self.current().is_some() && !self.at_punctuation('}') {
            let name = self.expect_identifier()?;
            if self.expect_punctuation(':').is_none() {
                self.error_current("G4013", "expected `:` after record field name");
                return None;
            }
            let value = self
                .parse_expression()
                .unwrap_or_else(|| self.recover_expression());
            fields.push((name, value));
            if !self.at_punctuation(',') {
                break;
            }
            self.position += 1;
        }
        let close = self.expect_punctuation('}')?;
        Some(self.alloc(
            ExprKind::Record { path, fields },
            join(start, self.lexed.tokens[close].span),
        ))
    }

    fn parse_atom(&mut self) -> Option<ExprId> {
        let index = self.current()?;
        let token = &self.lexed.tokens[index];
        match token.kind {
            TokenKind::Integer | TokenKind::Float | TokenKind::String | TokenKind::Character => {
                self.position += 1;
                Some(self.alloc(ExprKind::Literal(self.text(index).to_owned()), token.span))
            }
            TokenKind::Identifier => {
                self.position += 1;
                if matches!(self.text(index), "true" | "false") {
                    return Some(
                        self.alloc(ExprKind::Literal(self.text(index).to_owned()), token.span),
                    );
                }
                let mut path = vec![self.text(index).to_owned()];
                let mut effect_arguments = vec![];
                if self.generic_path_ahead() {
                    effect_arguments =
                        self.parse_type_arguments("G4026", "expected `>` in effect application")?;
                }
                while self.at_punctuation(':') && self.peek_punctuation(1, ':') {
                    self.position += 2;
                    path.push(self.expect_identifier()?);
                }
                let operation_arguments = if path.len() > 1 && self.operation_generic_ahead() {
                    self.parse_type_arguments("G4026", "expected `>` in operation application")?
                } else {
                    vec![]
                };
                let end = self.lexed.tokens[self.tokens[self.position - 1]].span;
                let kind = if effect_arguments.is_empty() && operation_arguments.is_empty() {
                    ExprKind::Path(path)
                } else {
                    ExprKind::GenericPath {
                        path,
                        effect_arguments,
                        operation_arguments,
                    }
                };
                Some(self.alloc(kind, join(token.span, end)))
            }
            TokenKind::Punctuation('{') if self.compact_closure_ahead() => {
                self.parse_compact_closure()
            }
            TokenKind::Punctuation('{') => self.parse_block(false),
            TokenKind::Punctuation('(') if self.typed_closure_ahead() => self.parse_typed_closure(),
            TokenKind::Punctuation('(') => self.parse_group_or_tuple(),
            TokenKind::Punctuation('[') => self.parse_array(),
            _ => {
                self.error_current("G4002", "expected an expression");
                None
            }
        }
    }

    fn parse_group_or_tuple(&mut self) -> Option<ExprId> {
        let open = self.expect_punctuation('(')?;
        if self.at_punctuation(')') {
            let close = self.advance()?;
            return Some(self.alloc(
                ExprKind::Tuple(vec![]),
                join(self.lexed.tokens[open].span, self.lexed.tokens[close].span),
            ));
        }
        let first = self.parse_expression()?;
        if !self.at_punctuation(',') {
            self.expect_punctuation(')')?;
            return Some(first);
        }
        let mut elements = vec![first];
        while self.at_punctuation(',') {
            self.position += 1;
            if self.at_punctuation(')') {
                break;
            }
            elements.push(
                self.parse_expression()
                    .unwrap_or_else(|| self.recover_expression()),
            );
        }
        let close = self.expect_punctuation(')')?;
        Some(self.alloc(
            ExprKind::Tuple(elements),
            join(self.lexed.tokens[open].span, self.lexed.tokens[close].span),
        ))
    }

    fn parse_array(&mut self) -> Option<ExprId> {
        let open = self.expect_punctuation('[')?;
        let mut values = vec![];
        while self.current().is_some() && !self.at_punctuation(']') {
            values.push(
                self.parse_expression()
                    .unwrap_or_else(|| self.recover_expression()),
            );
            if !self.at_punctuation(',') {
                break;
            }
            self.position += 1;
        }
        let close = self.expect_punctuation(']')?;
        Some(self.alloc(
            ExprKind::Array(values),
            join(self.lexed.tokens[open].span, self.lexed.tokens[close].span),
        ))
    }

    fn compact_closure_ahead(&self) -> bool {
        if self.current().is_none() {
            return false;
        }
        let Some(first) = self.tokens.get(self.position + 1).copied() else {
            return false;
        };
        let first = &self.lexed.tokens[first];
        if first.kind == TokenKind::Operator && self.text(self.tokens[self.position + 1]) == "=>" {
            return true;
        }
        if first.kind != TokenKind::Identifier {
            return false;
        }
        let Some(second) = self.tokens.get(self.position + 2).copied() else {
            return false;
        };
        (self.lexed.tokens[second].kind == TokenKind::Operator && self.text(second) == "=>")
            || self.lexed.tokens[second].kind == TokenKind::Punctuation(',')
    }

    fn parse_compact_closure(&mut self) -> Option<ExprId> {
        let open = self.expect_punctuation('{')?;
        let mut parameters = vec![];
        if !self.at_operator("=>") {
            loop {
                parameters.push(self.expect_identifier()?);
                if self.at_operator("=>") {
                    break;
                }
                if !self.at_punctuation(',') {
                    self.error_current("G4006", "expected `,` or `=>` in closure parameters");
                    return None;
                }
                self.position += 1;
            }
        }
        if !self.at_operator("=>") {
            self.error_current("G4006", "expected `=>` after closure parameters");
            return None;
        }
        self.position += 1;
        let body = self
            .parse_expression()
            .unwrap_or_else(|| self.recover_expression());
        let close = self.expect_punctuation('}')?;
        Some(self.alloc(
            ExprKind::Closure { parameters, body },
            join(self.lexed.tokens[open].span, self.lexed.tokens[close].span),
        ))
    }

    fn typed_closure_ahead(&self) -> bool {
        let Some(open) = self.current() else {
            return false;
        };
        let Some(close) = self.lexed.delimiters.matching(open) else {
            return false;
        };
        let Some(position) = self.tokens.iter().position(|token| *token == close) else {
            return false;
        };
        self.tokens
            .get(position + 1)
            .is_some_and(|token| self.lexed.tokens[*token].kind == TokenKind::Operator)
            && self
                .tokens
                .get(position + 1)
                .is_some_and(|token| self.text(*token) == "->")
    }

    fn parse_typed_closure(&mut self) -> Option<ExprId> {
        let open = self.expect_punctuation('(')?;
        let mut parameters = vec![];
        while !self.at_punctuation(')') && self.current().is_some() {
            let start = self.current()?;
            let name = self.expect_identifier()?;
            if !self.at_punctuation(':') {
                self.error_current("G4007", "expected `:` in typed closure parameter");
                return None;
            }
            self.position += 1;
            let ty = self.closure_type()?;
            let end = self
                .position
                .checked_sub(1)
                .and_then(|position| self.tokens.get(position).copied())
                .unwrap_or(start);
            parameters.push(ClosureParameter {
                name,
                ty: Some(ty),
                span: join(self.lexed.tokens[start].span, self.lexed.tokens[end].span),
            });
            if !self.at_punctuation(',') {
                break;
            }
            self.position += 1;
        }
        if self.expect_punctuation(')').is_none() || !self.at_operator("->") {
            self.error_current("G4008", "expected `->` after typed closure parameters");
            return None;
        }
        self.position += 1;
        let result = if !self.at_punctuation('{') && !self.at_operator("/") {
            Some(self.closure_type()?)
        } else {
            None
        };
        let mut effects = EffectRowHeader::default();
        if self.at_operator("/") {
            self.position += 1;
            if self.at_punctuation('{') {
                self.position += 1;
                while !self.at_punctuation('}') && self.current().is_some() {
                    if self.at_operator("|") {
                        self.position += 1;
                        effects.tail = Some(self.expect_identifier()?);
                        break;
                    }
                    effects.effects.push(self.closure_type()?);
                    if self.at_operator("|") {
                        continue;
                    }
                    if !self.at_punctuation(',') {
                        if !self.at_punctuation('}') {
                            self.error_current(
                                "G4017",
                                "expected `,` between typed closure effect-row members",
                            );
                        }
                        break;
                    }
                    self.position += 1;
                }
                self.expect_punctuation('}')?;
            } else {
                effects.effects.push(self.closure_type()?);
            }
        }
        let body = self.parse_block(false)?;
        let span = join(self.lexed.tokens[open].span, self.expression(body).span);
        Some(self.alloc(
            ExprKind::TypedClosure {
                parameters,
                result,
                effects,
                body,
            },
            span,
        ))
    }

    fn closure_type(&mut self) -> Option<HeaderType> {
        if self.at_operator("<") {
            self.position += 1;
            let subject = self.closure_type()?;
            if self.word() != Some("as") {
                self.error_current("G4010", "expected `as` in associated type projection");
                return None;
            }
            self.position += 1;
            let mut trait_path = vec![self.expect_identifier()?];
            while self.at_punctuation(':') && self.peek_punctuation(1, ':') {
                self.position += 2;
                trait_path.push(self.expect_identifier()?);
            }
            let trait_arguments = self.closure_type_arguments()?;
            if !self.at_operator(">") {
                self.error_current("G4011", "expected `>` in associated type projection");
                return None;
            }
            self.position += 1;
            if !self.at_punctuation(':') || !self.peek_punctuation(1, ':') {
                self.error_current("G4012", "expected `::` before associated type name");
                return None;
            }
            self.position += 2;
            let name = self.expect_identifier()?;
            let item_arguments = self.closure_type_arguments()?;
            return Some(HeaderType::Projection {
                subject: Box::new(subject),
                trait_path,
                trait_arguments,
                name,
                item_arguments,
            });
        }
        if self.at_operator("!") {
            self.position += 1;
            return Some(HeaderType::Never);
        }
        if self.at_operator("&") {
            self.position += 1;
            let lifetime = if self
                .current()
                .is_some_and(|token| self.text(token).starts_with('\''))
            {
                Some(self.expect_identifier()?)
            } else {
                None
            };
            let unique = self.word() == Some("mut");
            if unique {
                self.position += 1;
            }
            return Some(HeaderType::Reference {
                unique,
                lifetime,
                referent: Box::new(self.closure_type()?),
            });
        }
        if self.at_punctuation('(') {
            self.position += 1;
            let mut values = vec![];
            while !self.at_punctuation(')') && self.current().is_some() {
                values.push(self.closure_type()?);
                if !self.at_punctuation(',') {
                    break;
                }
                self.position += 1;
            }
            self.expect_punctuation(')')?;
            if self.at_operator("->") {
                self.position += 1;
                return Some(HeaderType::Callable {
                    parameters: values,
                    result: Box::new(self.closure_type()?),
                });
            }
            return Some(HeaderType::Tuple(values));
        }
        let mut path = vec![self.expect_identifier()?];
        while self.at_punctuation(':') && self.peek_punctuation(1, ':') {
            self.position += 2;
            path.push(self.expect_identifier()?);
        }
        let base = HeaderType::Path(path);
        if !self.at_operator("<") {
            return Some(base);
        }
        let arguments = self.closure_type_arguments()?;
        Some(HeaderType::Application(Box::new(base), arguments))
    }

    fn closure_type_arguments(&mut self) -> Option<Vec<HeaderGenericArgument>> {
        if !self.at_operator("<") {
            return Some(vec![]);
        }
        self.position += 1;
        let mut arguments = vec![];
        while !self.at_operator(">") && self.current().is_some() {
            if self.at_punctuation('[') {
                arguments.push(HeaderGenericArgument::Quantity(
                    self.closure_structural_quantity_argument()?,
                ));
            } else if let Some(index) = self.current()
                && self.lexed.tokens[index].kind == TokenKind::Integer
            {
                let text = self.text(index).to_owned();
                self.position += 1;
                match text.parse::<u32>() {
                    Ok(value) => arguments.push(HeaderGenericArgument::U32(value)),
                    Err(_) => {
                        self.error_current(
                            "G4009",
                            "structural u32 generic argument is out of range",
                        );
                        return None;
                    }
                }
            } else {
                arguments.push(HeaderGenericArgument::Type(self.closure_type()?));
            }
            if !self.at_punctuation(',') {
                break;
            }
            self.position += 1;
        }
        if !self.at_operator(">") {
            self.error_current("G4009", "expected `>` in closure type application");
            return None;
        }
        self.position += 1;
        Some(arguments)
    }

    fn closure_structural_quantity_argument(&mut self) -> Option<Quantity> {
        debug_assert!(self.at_punctuation('['));
        self.position += 1;
        let lower = self.closure_u32("expected a non-negative quantity lower bound")?;
        if !self.at_punctuation(',') {
            self.error_current("G4009", "expected `,` in structural quantity argument");
            return None;
        }
        self.position += 1;
        let upper = if self.at_operator("*") {
            self.position += 1;
            None
        } else {
            Some(self.closure_u32("expected a non-negative quantity upper bound")?)
        };
        if !self.at_punctuation(']') {
            self.error_current("G4009", "expected `]` after structural quantity argument");
            return None;
        }
        self.position += 1;
        match Quantity::new(u64::from(lower), upper.map(u64::from)) {
            Ok(value) => Some(value),
            Err(_) => {
                self.error_current("G4009", "quantity upper bound is below its lower bound");
                None
            }
        }
    }

    fn closure_u32(&mut self, message: &'static str) -> Option<u32> {
        let index = self.current()?;
        if self.lexed.tokens[index].kind != TokenKind::Integer {
            self.error_current("G4009", message);
            return None;
        }
        let value = self.text(index).parse().ok();
        self.position += 1;
        value.or_else(|| {
            self.error_current("G4009", message);
            None
        })
    }

    fn parse_call(&mut self, callee: ExprId) -> Option<ExprId> {
        self.expect_punctuation('(')?;
        let mut arguments = vec![];
        while !self.at_punctuation(')') && self.current().is_some() {
            arguments.push(
                self.parse_expression()
                    .unwrap_or_else(|| self.recover_expression()),
            );
            if self.at_punctuation(',') {
                self.position += 1;
            } else {
                break;
            }
        }
        let close = self.expect_punctuation(')')?;
        let span = join(self.expression(callee).span, self.lexed.tokens[close].span);
        Some(self.alloc(ExprKind::Call { callee, arguments }, span))
    }

    fn parse_let(&mut self) -> Option<ExprId> {
        let start = self.advance()?;
        let name = self.expect_identifier()?;
        if !self.at_operator("=") {
            self.error_current("G4003", "expected `=` in let binding");
            return None;
        }
        self.position += 1;
        let value = self
            .parse_expression()
            .unwrap_or_else(|| self.recover_expression());
        Some(self.alloc(
            ExprKind::Let { name, value },
            join(self.lexed.tokens[start].span, self.expression(value).span),
        ))
    }

    fn parse_pattern(
        &mut self,
        binders: &mut std::collections::BTreeSet<String>,
    ) -> Option<PatternId> {
        let start = self.current()?;
        let token = &self.lexed.tokens[start];
        match token.kind {
            TokenKind::Integer | TokenKind::Float | TokenKind::String | TokenKind::Character => {
                self.position += 1;
                Some(self.alloc_pattern(
                    PatternKind::Literal(self.text(start).to_owned()),
                    token.span,
                ))
            }
            TokenKind::Punctuation('(') => {
                self.position += 1;
                let mut values = vec![];
                while !self.at_punctuation(')') && self.current().is_some() {
                    values.push(self.parse_pattern(binders)?);
                    if !self.at_punctuation(',') {
                        break;
                    }
                    self.position += 1;
                }
                let close = self.expect_punctuation(')')?;
                Some(self.alloc_pattern(
                    PatternKind::Tuple(values),
                    join(token.span, self.lexed.tokens[close].span),
                ))
            }
            TokenKind::Identifier => {
                self.position += 1;
                let first = self.text(start).to_owned();
                if first == "_" {
                    return Some(self.alloc_pattern(PatternKind::Wildcard, token.span));
                }
                if matches!(first.as_str(), "true" | "false") {
                    return Some(self.alloc_pattern(PatternKind::Literal(first), token.span));
                }
                let mut path = vec![first];
                while self.at_punctuation(':') && self.peek_punctuation(1, ':') {
                    self.position += 2;
                    path.push(self.expect_identifier()?);
                }
                if self.at_punctuation('{') {
                    self.position += 1;
                    let mut fields = vec![];
                    while !self.at_punctuation('}') && self.current().is_some() {
                        let name = self.expect_identifier()?;
                        if !self.at_punctuation(':') {
                            self.error_current("G4016", "expected `:` in record pattern field");
                            return None;
                        }
                        self.position += 1;
                        fields.push((name, self.parse_pattern(binders)?));
                        if !self.at_punctuation(',') {
                            break;
                        }
                        self.position += 1;
                    }
                    let close = self.expect_punctuation('}')?;
                    return Some(self.alloc_pattern(
                        PatternKind::Record { path, fields },
                        join(token.span, self.lexed.tokens[close].span),
                    ));
                }
                if self.at_punctuation('(') {
                    self.position += 1;
                    let mut fields = vec![];
                    while !self.at_punctuation(')') && self.current().is_some() {
                        fields.push(self.parse_pattern(binders)?);
                        if !self.at_punctuation(',') {
                            break;
                        }
                        self.position += 1;
                    }
                    let close = self.expect_punctuation(')')?;
                    return Some(self.alloc_pattern(
                        PatternKind::Enum { path, fields },
                        join(token.span, self.lexed.tokens[close].span),
                    ));
                }
                if path.len() > 1 {
                    return Some(self.alloc_pattern(
                        PatternKind::Enum {
                            path,
                            fields: vec![],
                        },
                        token.span,
                    ));
                }
                if !binders.insert(path[0].clone()) {
                    self.error_at(token.span, "G4017", "duplicate binder in one pattern");
                }
                Some(self.alloc_pattern(PatternKind::Binding(path.remove(0)), token.span))
            }
            _ => {
                self.error_current("G4018", "expected a structural pattern");
                None
            }
        }
    }

    fn recover_expression(&mut self) -> ExprId {
        self.recovered = true;
        let token = self
            .current()
            .or_else(|| self.tokens.last().copied())
            .expect("body has delimiters");
        self.synchronize();
        self.alloc(ExprKind::Recovered, self.lexed.tokens[token].span)
    }
    fn recover_pattern(&mut self) -> PatternId {
        self.recovered = true;
        let token = self
            .current()
            .or_else(|| self.tokens.last().copied())
            .expect("body has delimiters");
        self.synchronize();
        self.alloc_pattern(PatternKind::Recovered, self.lexed.tokens[token].span)
    }

    fn recover_root(&mut self) -> ExprId {
        self.recovered = true;
        let span = self
            .tokens
            .first()
            .map(|index| self.lexed.tokens[*index].span)
            .unwrap_or(Span {
                file: self.lexed.file,
                start: 0,
                end: 0,
            });
        self.alloc(ExprKind::Recovered, span)
    }

    fn synchronize(&mut self) {
        while let Some(index) = self.current() {
            if matches!(
                self.lexed.tokens[index].kind,
                TokenKind::Punctuation(';' | '}')
            ) {
                return;
            }
            self.position += 1;
        }
    }

    fn alloc(&mut self, kind: ExprKind, span: Span) -> ExprId {
        let id = ExprId(
            u32::try_from(self.expressions.len()).expect("body syntax arena exceeds G1 range"),
        );
        self.expressions.push(Expr { kind, span });
        id
    }
    fn alloc_pattern(&mut self, kind: PatternKind, span: Span) -> PatternId {
        let id = PatternId(
            u32::try_from(self.patterns.len()).expect("body pattern arena exceeds G1 range"),
        );
        self.patterns.push(Pattern { kind, span });
        id
    }

    fn expression(&self, id: ExprId) -> &Expr {
        &self.expressions[id.0 as usize]
    }
    fn pattern(&self, id: PatternId) -> &Pattern {
        &self.patterns[id.0 as usize]
    }
    fn current(&self) -> Option<usize> {
        self.tokens
            .get(self.position)
            .copied()
            .filter(|index| self.lexed.tokens[*index].kind != TokenKind::End)
    }
    fn advance(&mut self) -> Option<usize> {
        let current = self.current()?;
        self.position += 1;
        Some(current)
    }
    fn text(&self, index: usize) -> &str {
        self.lexed.text(self.source, &self.lexed.tokens[index])
    }
    fn word(&self) -> Option<&str> {
        let index = self.current()?;
        (self.lexed.tokens[index].kind == TokenKind::Identifier).then(|| self.text(index))
    }
    fn operator(&self) -> Option<&str> {
        let index = self.current()?;
        (self.lexed.tokens[index].kind == TokenKind::Operator).then(|| self.text(index))
    }
    /// Word-form boolean operators belong to the same flat operator stream as
    /// symbolic operators. Keeping them here, rather than parsing a separate
    /// expression grammar, lets the frozen module fixity table retain the
    /// authority for their precedence and associativity.
    fn infix_operator(&self) -> Option<&str> {
        self.operator().or_else(|| match self.word() {
            Some("and" | "or") => self.word(),
            _ => None,
        })
    }
    fn at_operator(&self, operator: &str) -> bool {
        self.operator() == Some(operator)
    }
    fn at_punctuation(&self, punctuation: char) -> bool {
        self.current().is_some_and(|index| {
            self.lexed.tokens[index].kind == TokenKind::Punctuation(punctuation)
        })
    }
    fn peek_punctuation(&self, offset: usize, punctuation: char) -> bool {
        self.tokens
            .get(self.position + offset)
            .is_some_and(|index| {
                self.lexed.tokens[*index].kind == TokenKind::Punctuation(punctuation)
            })
    }
    fn expect_punctuation(&mut self, punctuation: char) -> Option<usize> {
        if self.at_punctuation(punctuation) {
            self.advance()
        } else {
            self.error_current("G4004", "expected punctuation");
            None
        }
    }
    fn expect_identifier(&mut self) -> Option<String> {
        if self.word().is_some() {
            let index = self.advance()?;
            Some(self.text(index).to_owned())
        } else {
            self.error_current("G4005", "expected identifier");
            None
        }
    }
    fn error_current(&mut self, code: &'static str, message: &'static str) {
        let index = self.current().or_else(|| self.tokens.last().copied());
        if let Some(index) = index {
            self.diagnostics.push(BodyDiagnostic {
                code,
                span: self.lexed.tokens[index].span,
                message,
            });
        }
        self.recovered = true;
    }
    fn error_at(&mut self, span: Span, code: &'static str, message: &'static str) {
        self.diagnostics.push(BodyDiagnostic {
            code,
            span,
            message,
        });
        self.recovered = true;
    }
}

fn join(left: Span, right: Span) -> Span {
    Span {
        file: left.file,
        start: left.start,
        end: right.end,
    }
}
fn is_trivia(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
    )
}
