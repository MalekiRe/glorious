//! Parsed declaration headers shared by interfaces and body elaboration.
//!
//! The scanner owns declaration boundaries; this parser consumes only a
//! shell's header range. Function bodies therefore remain demand-driven while
//! type spelling, generic binders, and callable contracts have one syntax.

use std::collections::BTreeSet;

use crate::{
    quantity::Quantity,
    scanner::{DeclarationKind, DeclarationShell, TokenRange},
    source::{LexedFile, Span, TokenKind},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HeaderType {
    Path(Vec<String>),
    Application(Box<HeaderType>, Vec<HeaderType>),
    /// An associated type selected through an explicit trait relation.  The
    /// angle-bracket form avoids treating a qualified path as either a module
    /// path or an associated item before its receiver has been elaborated.
    ///
    /// Canonical spelling: `<Subject as Trait<Args>>::Item`.
    Projection {
        subject: Box<HeaderType>,
        trait_path: Vec<String>,
        trait_arguments: Vec<HeaderType>,
        name: String,
    },
    Tuple(Vec<HeaderType>),
    Callable {
        parameters: Vec<HeaderType>,
        result: Box<HeaderType>,
    },
    Reference {
        unique: bool,
        referent: Box<HeaderType>,
    },
    Never,
    Recovered,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderParameter {
    pub name: String,
    pub ty: HeaderType,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallableHeader {
    pub generics: Vec<String>,
    pub parameters: Vec<HeaderParameter>,
    pub result: Option<HeaderType>,
    /// A callable's declared outward effect row.  Omission is the canonical
    /// closed empty row; body-local inference never mutates this interface
    /// fact.
    pub effects: EffectRowHeader,
    pub where_bounds: Vec<WhereBoundHeader>,
}

#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct EffectRowHeader {
    pub effects: Vec<HeaderType>,
    /// Row-polymorphic tails require a kinded binder and are retained in
    /// syntax now; signature elaboration rejects one until the generic-kind
    /// interface product is available rather than treating it as a type.
    pub tail: Option<String>,
}

/// A trait reference deliberately uses the header type grammar for arguments.
/// It remains source-shaped until interface elaboration resolves the trait path
/// to its stable declaration identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitRefHeader {
    pub path: Vec<String>,
    pub arguments: Vec<HeaderType>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhereBoundHeader {
    pub subject: HeaderType,
    pub relation: TraitRefHeader,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedTypeHeader {
    pub name: String,
    pub generics: Vec<String>,
    /// `type Output: EffectRow;` declares an associated effect row rather
    /// than an ordinary associated type.
    pub effect_row: bool,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedTypeDefinitionHeader {
    pub name: String,
    pub generics: Vec<String>,
    pub value: HeaderType,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplementationMethodHeader {
    pub name: String,
    pub signature: CallableHeader,
    /// Exact brace-delimited source range of the method body. The
    /// implementation declaration itself remains an interface fact, while
    /// this range lets later body elaboration allocate a distinct callable
    /// product for each method without reparsing or guessing its boundary.
    pub body: Option<TokenRange>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitHeader {
    pub generics: Vec<String>,
    pub supertraits: Vec<TraitRefHeader>,
    pub associated_types: Vec<AssociatedTypeHeader>,
    pub methods: Vec<TraitMethodHeader>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitMethodHeader {
    pub name: String,
    pub signature: CallableHeader,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplementationHeader {
    pub generics: Vec<String>,
    pub negative: bool,
    pub relation: TraitRefHeader,
    pub self_ty: HeaderType,
    pub where_bounds: Vec<WhereBoundHeader>,
    pub associated_types: Vec<AssociatedTypeDefinitionHeader>,
    pub methods: Vec<ImplementationMethodHeader>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectOperationHeader {
    pub name: String,
    pub generics: Vec<String>,
    pub parameters: Vec<HeaderParameter>,
    /// Omitted result syntax is the unit type; terminality is represented
    /// separately so `!` can never be mistaken for a resumptive result.
    pub result: Option<HeaderType>,
    pub terminal: bool,
    pub resumption: Quantity,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectHeader {
    pub generics: Vec<String>,
    pub operations: Vec<EffectOperationHeader>,
}

/// Field declarations are interface facts for records and record-like enum
/// payloads. They use the same type grammar and source spans as callable
/// parameters, but are deliberately separate from body-local expressions.
pub type NominalFieldHeader = HeaderParameter;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EnumVariantPayloadHeader {
    Unit,
    Tuple(Vec<HeaderType>),
    Struct(Vec<NominalFieldHeader>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnumVariantHeader {
    pub name: String,
    pub payload: EnumVariantPayloadHeader,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NominalLayoutHeader {
    Struct(Vec<NominalFieldHeader>),
    Enum(Vec<EnumVariantHeader>),
    /// A body-less nominal is retained for recovery and for future opaque
    /// declarations; no layout-dependent operation may assume fields exist.
    Opaque,
}

/// The spelling of a source-level fixity declaration.  Prefix and infix
/// entries occupy separate lookup spaces, so a language can legitimately
/// declare both for the same operator spelling.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FixityForm {
    Prefix,
    InfixLeft,
    InfixRight,
    InfixNonAssociative,
}

impl FixityForm {
    pub fn is_prefix(self) -> bool {
        self == Self::Prefix
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FixityHeader {
    pub form: FixityForm,
    pub precedence: u8,
    pub operator: String,
}

/// A single explicit import binding.  Imports are declaration-header facts:
/// they are available to all body resolution without loading any body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportHeader {
    pub bindings: Vec<ImportBindingHeader>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportBindingHeader {
    pub path: Vec<String>,
    pub alias: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParsedHeader {
    Function(CallableHeader),
    TypeAlias {
        generics: Vec<String>,
        target: HeaderType,
    },
    Constant {
        ty: Option<HeaderType>,
    },
    Import(ImportHeader),
    Fixity(FixityHeader),
    Trait(TraitHeader),
    Implementation(ImplementationHeader),
    Effect(EffectHeader),
    Nominal {
        generics: Vec<String>,
        layout: NominalLayoutHeader,
    },
    Opaque,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: &'static str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderParse {
    pub header: ParsedHeader,
    pub diagnostics: Vec<HeaderDiagnostic>,
    pub recovered: bool,
}

impl HeaderParse {
    pub fn parse(lexed: &LexedFile, source: &str, shell: &DeclarationShell) -> Self {
        let tokens = significant(lexed, shell.header);
        let mut parser = Parser {
            lexed,
            source,
            tokens,
            position: 0,
            diagnostics: vec![],
            recovered: false,
        };
        if parser.word() == Some("pub") {
            parser.position += 1;
        }
        let keyword = parser.word().map(str::to_owned);
        parser.position += 1; // Scanner already proved the declaration keyword.
        let header = match shell.kind {
            DeclarationKind::Function => ParsedHeader::Function(parser.callable()),
            DeclarationKind::TypeAlias => {
                parser.identifier();
                let generics = parser.generics();
                if !parser.operator("=") {
                    parser.error("G3201", "expected `=` in type alias");
                }
                ParsedHeader::TypeAlias {
                    generics,
                    target: parser.ty(),
                }
            }
            DeclarationKind::Constant => {
                parser.identifier();
                let ty = parser.punctuation(':').then(|| parser.ty());
                if !parser.operator("=") {
                    parser.error("G3219", "expected `=` in constant declaration");
                }
                ParsedHeader::Constant { ty }
            }
            DeclarationKind::Import => ParsedHeader::Import(parser.import()),
            DeclarationKind::Fixity => ParsedHeader::Fixity(parser.fixity(keyword.as_deref())),
            DeclarationKind::Struct | DeclarationKind::Enum => {
                parser.identifier();
                let generics = parser.generics();
                let mut layout_parser = Parser {
                    lexed,
                    source,
                    tokens: shell
                        .body
                        .map(|range| significant(lexed, range))
                        .unwrap_or_default(),
                    position: 0,
                    diagnostics: vec![],
                    recovered: false,
                };
                let layout = layout_parser.nominal_layout(shell.kind);
                parser.diagnostics.extend(layout_parser.diagnostics);
                parser.recovered |= layout_parser.recovered;
                ParsedHeader::Nominal { generics, layout }
            }
            DeclarationKind::Trait => {
                parser.identifier();
                let generics = parser.generics();
                let supertraits = parser.supertraits();
                let lexed = parser.lexed;
                let source = parser.source;
                let mut body_parser = Parser {
                    lexed,
                    source,
                    tokens: shell
                        .body
                        .map(|range| significant(lexed, range))
                        .unwrap_or_default(),
                    position: 0,
                    diagnostics: vec![],
                    recovered: false,
                };
                let value = body_parser.trait_header(generics, supertraits);
                parser.diagnostics.extend(body_parser.diagnostics);
                parser.recovered |= body_parser.recovered;
                ParsedHeader::Trait(value)
            }
            DeclarationKind::Implementation => {
                ParsedHeader::Implementation(parser.implementation(shell.body))
            }
            DeclarationKind::Effect => {
                parser.identifier();
                let generics = parser.generics();
                let lexed = parser.lexed;
                let source = parser.source;
                let mut body_parser = Parser {
                    lexed,
                    source,
                    tokens: shell
                        .body
                        .map(|range| significant(lexed, range))
                        .unwrap_or_default(),
                    position: 0,
                    diagnostics: vec![],
                    recovered: false,
                };
                let value = body_parser.effect_header(generics);
                parser.diagnostics.extend(body_parser.diagnostics);
                parser.recovered |= body_parser.recovered;
                ParsedHeader::Effect(value)
            }
            _ => ParsedHeader::Opaque,
        };
        parser
            .diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        Self {
            header,
            diagnostics: parser.diagnostics,
            recovered: parser.recovered,
        }
    }
}

fn significant(lexed: &LexedFile, range: TokenRange) -> Vec<usize> {
    lexed.tokens[range.start..range.end]
        .iter()
        .enumerate()
        .filter_map(|(offset, token)| {
            (!matches!(
                token.kind,
                TokenKind::Whitespace
                    | TokenKind::LineComment
                    | TokenKind::BlockComment
                    | TokenKind::End
            ))
            .then_some(range.start + offset)
        })
        .collect()
}

struct Parser<'a> {
    lexed: &'a LexedFile,
    source: &'a str,
    tokens: Vec<usize>,
    position: usize,
    diagnostics: Vec<HeaderDiagnostic>,
    recovered: bool,
}
impl Parser<'_> {
    fn trait_header(
        &mut self,
        generics: Vec<String>,
        supertraits: Vec<TraitRefHeader>,
    ) -> TraitHeader {
        let mut associated_types = vec![];
        let mut methods = vec![];
        let mut names = BTreeSet::new();
        if !self.punctuation('{') {
            self.error("G3232", "expected `{` after trait declaration");
            return TraitHeader {
                generics,
                supertraits,
                associated_types,
                methods,
            };
        }
        while self.current().is_some() && !self.at_punctuation('}') {
            let start = self.current().unwrap();
            if self.word() == Some("type") {
                self.position += 1;
                let name = self.identifier().unwrap_or_else(|| {
                    self.error("G3233", "expected associated type name");
                    "<error>".into()
                });
                let item_generics = self.generics();
                let effect_row = if self.punctuation(':') {
                    if self.word() == Some("EffectRow") {
                        self.position += 1;
                        true
                    } else {
                        self.error("G3234", "expected `EffectRow` after associated item `:`");
                        false
                    }
                } else {
                    false
                };
                if self.operator("=") {
                    self.error("G3235", "associated type defaults are not supported");
                    self.skip_to_item_end();
                }
                if !self.punctuation(';') {
                    self.error("G3236", "expected `;` after associated type declaration");
                    self.skip_to_item_end();
                }
                if !names.insert(name.clone()) {
                    self.error("G3237", "duplicate trait item name");
                }
                let end = self.previous().unwrap_or(start);
                associated_types.push(AssociatedTypeHeader {
                    name,
                    generics: item_generics,
                    effect_row,
                    span: self.span(start, end),
                });
                continue;
            }
            if self.word() == Some("fn") {
                self.position += 1;
            }
            let method_start = self.current().unwrap_or(start);
            let name = self.identifier().unwrap_or_else(|| {
                self.error("G3233", "expected trait method name");
                "<error>".into()
            });
            let method_generics = self.generics();
            let parameters = self.callable_parameters();
            let result = self.operator("->").then(|| self.ty());
            let method = CallableHeader {
                generics: method_generics,
                parameters,
                result,
                effects: self.effect_row_annotation(),
                where_bounds: self.where_bounds(),
            };
            if !names.insert(name.clone()) {
                self.error("G3237", "duplicate trait item name");
            }
            if !self.punctuation(';') {
                self.error("G3238", "expected `;` after trait method signature");
                self.skip_to_item_end();
            }
            let method_end = self.previous().unwrap_or(method_start);
            methods.push(TraitMethodHeader {
                name,
                signature: method,
                span: self.span(method_start, method_end),
            });
        }
        if !self.punctuation('}') {
            self.error("G3239", "expected `}` after trait declaration");
        }
        TraitHeader {
            generics,
            supertraits,
            associated_types,
            methods,
        }
    }
    fn implementation(&mut self, body: Option<TokenRange>) -> ImplementationHeader {
        let generics = self.generics();
        let negative = self.operator("!");
        let relation = self.trait_ref();
        if self.word() != Some("for") {
            self.error("G3240", "expected `for` after implementation trait");
        } else {
            self.position += 1;
        }
        let self_ty = self.ty();
        let where_bounds = self.where_bounds();
        if self.current().is_some() {
            self.error("G3241", "unexpected token in implementation header");
        }
        let lexed = self.lexed;
        let source = self.source;
        let mut body_parser = Parser {
            lexed,
            source,
            tokens: body
                .map(|range| significant(lexed, range))
                .unwrap_or_default(),
            position: 0,
            diagnostics: vec![],
            recovered: false,
        };
        let mut associated_types = vec![];
        let mut methods = vec![];
        if body_parser.punctuation('{') {
            let mut names = BTreeSet::new();
            while body_parser.current().is_some() && !body_parser.at_punctuation('}') {
                if body_parser.word() != Some("type") && body_parser.word() != Some("fn") {
                    body_parser.skip_item_body();
                    continue;
                }
                if body_parser.word() == Some("type") {
                    let start = body_parser.current().unwrap();
                    body_parser.position += 1;
                    let name = body_parser.identifier().unwrap_or_else(|| {
                        body_parser.error("G3242", "expected associated type definition name");
                        "<error>".into()
                    });
                    let item_generics = body_parser.generics();
                    if !body_parser.operator("=") {
                        body_parser.error("G3243", "expected `=` in associated type definition");
                    }
                    let value = body_parser.ty();
                    if !body_parser.punctuation(';') {
                        body_parser.error("G3244", "expected `;` after associated type definition");
                        body_parser.skip_to_item_end();
                    }
                    if !names.insert(name.clone()) {
                        body_parser.error("G3245", "duplicate associated type definition");
                    }
                    let end = body_parser.previous().unwrap_or(start);
                    associated_types.push(AssociatedTypeDefinitionHeader {
                        name,
                        generics: item_generics,
                        value,
                        span: body_parser.span(start, end),
                    });
                    continue;
                }
                if body_parser.word() == Some("fn") {
                    let start = body_parser.current().unwrap();
                    body_parser.position += 1;
                    let name = body_parser.identifier().unwrap_or_else(|| {
                        body_parser.error("G3242", "expected implementation method name");
                        "<error>".into()
                    });
                    let generics = body_parser.generics();
                    let parameters = body_parser.callable_parameters();
                    let result = body_parser.operator("->").then(|| body_parser.ty());
                    let signature = CallableHeader {
                        generics,
                        parameters,
                        result,
                        effects: body_parser.effect_row_annotation(),
                        where_bounds: body_parser.where_bounds(),
                    };
                    if !names.insert(name.clone()) {
                        body_parser.error("G3245", "duplicate implementation item name");
                    }
                    let body_start = body_parser.current();
                    let body = if !body_parser.punctuation('{') {
                        body_parser.error("G3244", "expected implementation method body");
                        body_parser.skip_to_item_end();
                        None
                    } else {
                        let mut depth = 1;
                        while body_parser.current().is_some() && depth > 0 {
                            if body_parser.punctuation('{') {
                                depth += 1;
                                continue;
                            }
                            if body_parser.punctuation('}') {
                                depth -= 1;
                                continue;
                            }
                            body_parser.position += 1;
                        }
                        if depth != 0 {
                            body_parser
                                .error("G3246", "expected `}` after implementation method body");
                            None
                        } else {
                            let end = body_parser
                                .previous()
                                .expect("closed implementation method body has closing brace")
                                + 1;
                            Some(TokenRange {
                                start: body_start.expect("method body start exists"),
                                end,
                            })
                        }
                    };
                    let end = body_parser.previous().unwrap_or(start);
                    methods.push(ImplementationMethodHeader {
                        name,
                        signature,
                        body,
                        span: body_parser.span(start, end),
                    });
                    continue;
                }
            }
            if !body_parser.punctuation('}') {
                body_parser.error("G3246", "expected `}` after implementation body");
            }
        } else {
            body_parser.error("G3247", "expected implementation body");
        }
        self.diagnostics.extend(body_parser.diagnostics);
        self.recovered |= body_parser.recovered;
        ImplementationHeader {
            generics,
            negative,
            relation,
            self_ty,
            where_bounds,
            associated_types,
            methods,
        }
    }
    fn effect_header(&mut self, generics: Vec<String>) -> EffectHeader {
        let mut operations = vec![];
        let mut names = BTreeSet::new();
        if !self.punctuation('{') {
            self.error("G3248", "expected `{` after effect declaration");
            return EffectHeader {
                generics,
                operations,
            };
        }
        while self.current().is_some() && !self.at_punctuation('}') {
            let start = self.current().unwrap();
            let resumption = self.quantity().unwrap_or(Quantity::ONCE);
            let has_quantity = self
                .previous()
                .is_some_and(|index| self.lexed.tokens[index].kind == TokenKind::Punctuation(']'));
            let name = self.identifier().unwrap_or_else(|| {
                self.error("G3249", "expected effect operation name");
                "<error>".into()
            });
            let operation_generics = self.generics();
            let parameters = self.callable_parameters();
            let (result, terminal) = if self.operator("->") {
                if self.operator("!") {
                    (None, true)
                } else {
                    (Some(self.ty()), false)
                }
            } else {
                (None, false)
            };
            if terminal && has_quantity {
                self.error(
                    "G3250",
                    "terminal operations may not declare a resumption quantity",
                );
            }
            if !self.punctuation(';') && !self.at_punctuation('}') {
                // Newlines are trivia, so a following identifier begins the
                // next operation.  The source form remains unambiguous here.
                if self.word().is_none() {
                    self.error("G3251", "expected `;` between effect operations");
                    self.skip_to_item_end();
                }
            }
            if !names.insert(name.clone()) {
                self.error("G3252", "duplicate effect operation name");
            }
            let end = self.previous().unwrap_or(start);
            operations.push(EffectOperationHeader {
                name,
                generics: operation_generics,
                parameters,
                result,
                terminal,
                resumption,
                span: self.span(start, end),
            });
        }
        if !self.punctuation('}') {
            self.error("G3253", "expected `}` after effect declaration");
        }
        EffectHeader {
            generics,
            operations,
        }
    }
    fn callable_parameters(&mut self) -> Vec<HeaderParameter> {
        if !self.punctuation('(') {
            self.error("G3202", "expected callable parameter list");
        }
        let mut parameters = vec![];
        while self.current().is_some() && !self.at_punctuation(')') {
            let start = self.current().unwrap();
            let name = self.identifier().unwrap_or_else(|| "<error>".into());
            if !self.punctuation(':') {
                self.error("G3203", "expected `:` after parameter name");
            }
            let ty = self.ty();
            let end = self.previous().unwrap_or(start);
            parameters.push(HeaderParameter {
                name,
                ty,
                span: self.span(start, end),
            });
            if !self.punctuation(',') {
                break;
            }
        }
        if !self.punctuation(')') {
            self.error("G3204", "expected `)` after callable parameters");
        }
        parameters
    }
    fn trait_ref(&mut self) -> TraitRefHeader {
        let start = self
            .current()
            .unwrap_or_else(|| self.previous().unwrap_or(0));
        let path = self.path();
        let mut arguments = vec![];
        if self.operator("<") {
            while self.current().is_some() && !self.at_operator(">") {
                arguments.push(self.ty());
                if !self.punctuation(',') {
                    break;
                }
            }
            if !self.operator(">") {
                self.error("G3254", "expected `>` after trait arguments");
            }
        }
        if path.is_empty() {
            self.error("G3255", "expected trait path");
        }
        let end = self.previous().unwrap_or(start);
        TraitRefHeader {
            path,
            arguments,
            span: self.span(start, end),
        }
    }
    fn where_bounds(&mut self) -> Vec<WhereBoundHeader> {
        if self.word() != Some("where") {
            return vec![];
        }
        self.position += 1;
        let mut bounds = vec![];
        while self.current().is_some() {
            let start = self.current().unwrap();
            let subject = self.ty();
            if !self.punctuation(':') {
                self.error("G3256", "expected `:` in where bound");
                break;
            }
            let relation = self.trait_ref();
            let end = self.previous().unwrap_or(start);
            bounds.push(WhereBoundHeader {
                subject,
                relation,
                span: self.span(start, end),
            });
            if !self.punctuation(',') {
                break;
            }
        }
        bounds
    }
    fn quantity(&mut self) -> Option<Quantity> {
        if !self.punctuation('[') {
            return None;
        }
        let lower = self.integer(
            "G3257",
            "resumption quantity lower bound must be a non-negative integer",
        );
        if !self.punctuation(',') {
            self.error("G3258", "expected `,` between resumption quantity bounds");
        }
        let upper = if self.at_operator("*") || self.word() == Some("infinity") {
            self.position += 1;
            None
        } else {
            Some(self.integer(
                "G3259",
                "resumption quantity upper bound must be a non-negative integer or `*`",
            ))
        };
        if !self.punctuation(']') {
            self.error("G3260", "expected `]` after resumption quantity");
        }
        match Quantity::new(lower, upper) {
            Ok(value) => Some(value),
            Err(_) => {
                self.error(
                    "G3261",
                    "resumption quantity lower bound exceeds upper bound",
                );
                Some(Quantity::ONCE)
            }
        }
    }
    fn integer(&mut self, code: &'static str, message: &'static str) -> u64 {
        match self.current() {
            Some(index) if self.lexed.tokens[index].kind == TokenKind::Integer => {
                self.position += 1;
                self.text(index).parse().unwrap_or_else(|_| {
                    self.error(code, message);
                    0
                })
            }
            _ => {
                self.error(code, message);
                0
            }
        }
    }
    fn supertraits(&mut self) -> Vec<TraitRefHeader> {
        if !self.punctuation(':') {
            return vec![];
        }
        let mut result = vec![];
        loop {
            result.push(self.trait_ref());
            if !self.operator("+") {
                break;
            }
        }
        result
    }
    fn skip_to_item_end(&mut self) {
        while self.current().is_some() && !self.at_punctuation(';') && !self.at_punctuation('}') {
            self.position += 1;
        }
        self.punctuation(';');
    }
    fn skip_item_body(&mut self) {
        if self.word() == Some("fn") {
            self.position += 1;
        }
        self.skip_to_item_end();
        if self.at_punctuation('{') {
            self.position += 1;
            let mut depth = 1;
            while self.current().is_some() && depth > 0 {
                if self.punctuation('{') {
                    depth += 1;
                    continue;
                }
                if self.punctuation('}') {
                    depth -= 1;
                    continue;
                }
                self.position += 1;
            }
        }
    }
    fn span(&self, start: usize, end: usize) -> Span {
        Span {
            file: self.lexed.file,
            start: self.lexed.tokens[start].span.start,
            end: self.lexed.tokens[end].span.end,
        }
    }
    fn nominal_layout(&mut self, kind: DeclarationKind) -> NominalLayoutHeader {
        if self.tokens.is_empty() {
            return NominalLayoutHeader::Opaque;
        }
        if !self.punctuation('{') {
            self.error("G3220", "expected nominal declaration body");
            return NominalLayoutHeader::Opaque;
        }
        let layout = match kind {
            DeclarationKind::Struct => NominalLayoutHeader::Struct(self.nominal_fields('}')),
            DeclarationKind::Enum => NominalLayoutHeader::Enum(self.enum_variants()),
            _ => NominalLayoutHeader::Opaque,
        };
        if !self.punctuation('}') {
            self.error("G3221", "expected `}` after nominal declaration body");
        }
        if self.current().is_some() {
            self.error("G3222", "unexpected trailing token in nominal declaration");
        }
        layout
    }
    fn nominal_fields(&mut self, closing: char) -> Vec<NominalFieldHeader> {
        let mut fields = vec![];
        let mut names = BTreeSet::new();
        while self.current().is_some() && !self.at_punctuation(closing) {
            let start = self.current().unwrap();
            let name = self.identifier().unwrap_or_else(|| {
                self.error("G3223", "expected nominal field name");
                "<error>".into()
            });
            if !self.punctuation(':') {
                self.error("G3224", "expected `:` after nominal field name");
            }
            let ty = self.ty();
            if !names.insert(name.clone()) {
                self.error("G3230", "duplicate nominal field name");
            }
            let end = self.previous().unwrap_or(start);
            fields.push(HeaderParameter {
                name,
                ty,
                span: Span {
                    file: self.lexed.file,
                    start: self.lexed.tokens[start].span.start,
                    end: self.lexed.tokens[end].span.end,
                },
            });
            if !self.punctuation(',') && !self.at_punctuation(closing) {
                self.error("G3225", "expected `,` between nominal fields");
                self.position += 1;
            }
        }
        fields
    }
    fn enum_variants(&mut self) -> Vec<EnumVariantHeader> {
        let mut variants = vec![];
        let mut names = BTreeSet::new();
        while self.current().is_some() && !self.at_punctuation('}') {
            let start = self.current().unwrap();
            let name = self.identifier().unwrap_or_else(|| {
                self.error("G3226", "expected enum variant name");
                "<error>".into()
            });
            let payload = if self.punctuation('(') {
                let mut fields = vec![];
                while self.current().is_some() && !self.at_punctuation(')') {
                    fields.push(self.ty());
                    if !self.punctuation(',') {
                        break;
                    }
                }
                if !self.punctuation(')') {
                    self.error("G3227", "expected `)` after enum tuple payload");
                }
                EnumVariantPayloadHeader::Tuple(fields)
            } else if self.punctuation('{') {
                let fields = self.nominal_fields('}');
                if !self.punctuation('}') {
                    self.error("G3228", "expected `}` after enum record payload");
                }
                EnumVariantPayloadHeader::Struct(fields)
            } else {
                EnumVariantPayloadHeader::Unit
            };
            if !names.insert(name.clone()) {
                self.error("G3231", "duplicate enum variant name");
            }
            let end = self.previous().unwrap_or(start);
            variants.push(EnumVariantHeader {
                name,
                payload,
                span: Span {
                    file: self.lexed.file,
                    start: self.lexed.tokens[start].span.start,
                    end: self.lexed.tokens[end].span.end,
                },
            });
            if !self.punctuation(',') && !self.at_punctuation('}') {
                self.error("G3229", "expected `,` between enum variants");
                self.position += 1;
            }
        }
        variants
    }
    fn callable(&mut self) -> CallableHeader {
        self.identifier();
        let generics = self.generics();
        if !self.punctuation('(') {
            self.error("G3202", "expected callable parameter list");
        }
        let mut parameters = vec![];
        while self.current().is_some() && !self.at_punctuation(')') {
            let start = self.current().unwrap();
            let name = self.identifier().unwrap_or_else(|| "<error>".into());
            if !self.punctuation(':') {
                self.error("G3203", "expected `:` after parameter name");
            }
            let ty = self.ty();
            let end = self.previous().unwrap_or(start);
            parameters.push(HeaderParameter {
                name,
                ty,
                span: Span {
                    file: self.lexed.file,
                    start: self.lexed.tokens[start].span.start,
                    end: self.lexed.tokens[end].span.end,
                },
            });
            if !self.punctuation(',') {
                break;
            }
        }
        if !self.punctuation(')') {
            self.error("G3204", "expected `)` after callable parameters");
        }
        let result = self.operator("->").then(|| self.ty());
        let effects = self.effect_row_annotation();
        let where_bounds = self.where_bounds();
        CallableHeader {
            generics,
            parameters,
            result,
            effects,
            where_bounds,
        }
    }
    fn effect_row_annotation(&mut self) -> EffectRowHeader {
        if !self.operator("/") {
            return EffectRowHeader::default();
        }
        if !self.punctuation('{') {
            return EffectRowHeader {
                effects: vec![self.ty()],
                tail: None,
            };
        }
        let mut effects = vec![];
        let mut tail = None;
        while self.current().is_some() && !self.at_punctuation('}') {
            if self.operator("|") {
                tail = self.identifier();
                if tail.is_none() {
                    self.error("G3262", "expected effect-row tail after `|`");
                }
                break;
            }
            effects.push(self.ty());
            if !self.punctuation(',') {
                if !self.at_punctuation('}') && !self.at_operator("|") {
                    self.error("G3263", "expected `,` between effect-row members");
                }
                continue;
            }
        }
        if !self.punctuation('}') {
            self.error("G3264", "expected `}` after effect row");
        }
        EffectRowHeader { effects, tail }
    }
    fn fixity(&mut self, keyword: Option<&str>) -> FixityHeader {
        let form = match keyword {
            Some("prefix") => Some(FixityForm::Prefix),
            Some("infixl") => Some(FixityForm::InfixLeft),
            Some("infixr") => Some(FixityForm::InfixRight),
            Some("infix") => Some(FixityForm::InfixNonAssociative),
            _ => None,
        };
        let form = form.unwrap_or_else(|| {
            self.error("G3209", "expected a fixity declaration form");
            FixityForm::InfixNonAssociative
        });
        let precedence = match self.current() {
            Some(index) if self.lexed.tokens[index].kind == TokenKind::Integer => {
                let text = self.text(index).to_owned();
                self.position += 1;
                match text.parse::<u8>() {
                    Ok(value) => value,
                    Err(_) => {
                        self.error(
                            "G3210",
                            "fixity precedence must be an integer from 0 through 255",
                        );
                        0
                    }
                }
            }
            _ => {
                self.error(
                    "G3210",
                    "fixity precedence must be an integer from 0 through 255",
                );
                0
            }
        };
        let operator = match self.current() {
            Some(index)
                if matches!(
                    self.lexed.tokens[index].kind,
                    TokenKind::Identifier | TokenKind::Operator
                ) =>
            {
                let value = self.text(index).to_owned();
                self.position += 1;
                value
            }
            _ => {
                self.error("G3211", "expected a fixity operator");
                "<error>".into()
            }
        };
        if !self.punctuation(';') {
            self.error("G3212", "expected `;` after fixity declaration");
        }
        if self.current().is_some() {
            self.error("G3213", "unexpected trailing token in fixity declaration");
        }
        FixityHeader {
            form,
            precedence,
            operator,
        }
    }
    fn import(&mut self) -> ImportHeader {
        let bindings = self.import_bindings(vec![]);
        if !self.punctuation(';') {
            self.error("G3214", "expected `;` after import declaration");
        }
        if self.current().is_some() {
            self.error("G3215", "unexpected trailing token in import declaration");
        }
        ImportHeader { bindings }
    }
    fn import_bindings(&mut self, prefix: Vec<String>) -> Vec<ImportBindingHeader> {
        let mut path = prefix;
        let Some(first) = self.identifier() else {
            self.error("G3216", "expected an imported path");
            return vec![];
        };
        path.push(first);
        while self.path_separator() {
            if self.punctuation('{') {
                let mut bindings = vec![];
                while self.current().is_some() && !self.at_punctuation('}') {
                    bindings.extend(self.import_bindings(path.clone()));
                    if !self.punctuation(',') {
                        break;
                    }
                }
                if !self.punctuation('}') {
                    self.error("G3217", "expected `}` in grouped import");
                }
                return bindings;
            }
            if self.at_operator("*") {
                self.position += 1;
                self.error("G3218", "glob imports are not supported");
                return vec![];
            }
            let Some(segment) = self.identifier() else {
                self.error("G3216", "expected an imported path segment");
                return vec![];
            };
            path.push(segment);
        }
        let alias = if self.word() == Some("as") {
            self.position += 1;
            self.identifier()
        } else {
            None
        };
        vec![ImportBindingHeader { path, alias }]
    }
    fn generics(&mut self) -> Vec<String> {
        if !self.operator("<") {
            return vec![];
        }
        let mut names = vec![];
        while self.current().is_some() && !self.at_operator(">") {
            if let Some(name) = self.identifier() {
                names.push(name);
            } else {
                self.position += 1;
                self.recovered = true;
            }
            if !self.punctuation(',') {
                break;
            }
        }
        if !self.operator(">") {
            self.error("G3205", "expected `>` after generic parameters");
        }
        names
    }
    fn ty(&mut self) -> HeaderType {
        if self.operator("<") {
            let subject = self.ty();
            if self.word() != Some("as") {
                self.error("G3209", "expected `as` in associated type projection");
                return HeaderType::Recovered;
            }
            self.position += 1;
            let trait_path = self.path();
            if trait_path.is_empty() {
                self.error("G3210", "expected trait path in associated type projection");
                return HeaderType::Recovered;
            }
            let trait_arguments = self.type_arguments();
            if !self.operator(">") {
                self.error("G3211", "expected `>` in associated type projection");
                return HeaderType::Recovered;
            }
            if !self.path_separator() {
                self.error("G3212", "expected `::` before associated type name");
                return HeaderType::Recovered;
            }
            let Some(name) = self.identifier() else {
                self.error("G3213", "expected associated type name");
                return HeaderType::Recovered;
            };
            return HeaderType::Projection {
                subject: Box::new(subject),
                trait_path,
                trait_arguments,
                name,
            };
        }
        if self.operator("!") {
            return HeaderType::Never;
        }
        if self.operator("&") {
            let unique = self.word() == Some("mut");
            if unique {
                self.position += 1;
            }
            return HeaderType::Reference {
                unique,
                referent: Box::new(self.ty()),
            };
        }
        if self.punctuation('(') {
            let mut values = vec![];
            while self.current().is_some() && !self.at_punctuation(')') {
                values.push(self.ty());
                if !self.punctuation(',') {
                    break;
                }
            }
            if !self.punctuation(')') {
                self.error("G3206", "expected `)` in tuple type");
            }
            if self.operator("->") {
                return HeaderType::Callable {
                    parameters: values,
                    result: Box::new(self.ty()),
                };
            }
            return HeaderType::Tuple(values);
        }
        let path = self.path();
        if path.is_empty() {
            self.error("G3207", "expected a type");
            return HeaderType::Recovered;
        }
        let mut value = HeaderType::Path(path);
        if self.at_operator("<") {
            let arguments = self.type_arguments();
            value = HeaderType::Application(Box::new(value), arguments);
        }
        value
    }
    fn type_arguments(&mut self) -> Vec<HeaderType> {
        if !self.at_operator("<") {
            return vec![];
        }
        self.position += 1;
        let mut arguments = vec![];
        while self.current().is_some() && !self.at_operator(">") {
            arguments.push(self.ty());
            if !self.punctuation(',') {
                break;
            }
        }
        if !self.operator(">") {
            self.error("G3208", "expected `>` after type arguments");
        }
        arguments
    }
    fn path(&mut self) -> Vec<String> {
        let mut path = vec![];
        while let Some(name) = self.identifier() {
            path.push(name);
            if !self.path_separator() {
                break;
            }
        }
        path
    }
    fn path_separator(&mut self) -> bool {
        if self.operator("::") {
            return true;
        }
        let paired_punctuation = self
            .tokens
            .get(self.position)
            .zip(self.tokens.get(self.position + 1))
            .is_some_and(|(left, right)| {
                self.lexed.tokens[*left].kind == TokenKind::Punctuation(':')
                    && self.lexed.tokens[*right].kind == TokenKind::Punctuation(':')
            });
        if paired_punctuation {
            self.position += 2;
        }
        paired_punctuation
    }
    fn current(&self) -> Option<usize> {
        self.tokens.get(self.position).copied()
    }
    fn previous(&self) -> Option<usize> {
        self.position
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .copied()
    }
    fn word(&self) -> Option<&str> {
        let i = self.current()?;
        (self.lexed.tokens[i].kind == TokenKind::Identifier)
            .then(|| self.lexed.text(self.source, &self.lexed.tokens[i]))
    }
    fn text(&self, index: usize) -> &str {
        self.lexed.text(self.source, &self.lexed.tokens[index])
    }
    fn identifier(&mut self) -> Option<String> {
        let value = self.word()?.to_owned();
        self.position += 1;
        Some(value)
    }
    fn at_punctuation(&self, value: char) -> bool {
        self.current()
            .is_some_and(|i| self.lexed.tokens[i].kind == TokenKind::Punctuation(value))
    }
    fn punctuation(&mut self, value: char) -> bool {
        if self.at_punctuation(value) {
            self.position += 1;
            true
        } else {
            false
        }
    }
    fn at_operator(&self, value: &str) -> bool {
        self.current().is_some_and(|i| {
            self.lexed.tokens[i].kind == TokenKind::Operator
                && self.lexed.text(self.source, &self.lexed.tokens[i]) == value
        })
    }
    fn operator(&mut self, value: &str) -> bool {
        if self.at_operator(value) {
            self.position += 1;
            true
        } else {
            false
        }
    }
    fn error(&mut self, code: &'static str, message: &'static str) {
        self.recovered = true;
        let span = self
            .current()
            .map(|i| self.lexed.tokens[i].span)
            .or_else(|| self.previous().map(|i| self.lexed.tokens[i].span))
            .unwrap_or(Span {
                file: self.lexed.file,
                start: 0,
                end: 0,
            });
        self.diagnostics.push(HeaderDiagnostic {
            code,
            span,
            message,
        });
    }
}
