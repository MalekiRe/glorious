use std::{collections::HashMap, mem::discriminant, rc::Rc};

use crate::frontend::{
    ast::{
        AssociatedArgumentSyntax, AssociatedBinding, AssociatedBindingValue, AssociatedTypeDecl,
        AssociatedTypeDefinition, Associativity, BinaryOp, ConstKind, DeconstructField, DropDecl,
        EffectDecl, EffectOperationDecl, EffectRowAliasDecl, EffectRowSyntax, EnumDecl, Expr,
        ExprKind, FieldDecl, FieldVisibility, FixityDecl, FixityKind, Function, GenericParam,
        GenericParamKind, GenericParams, GlobalBinding, GoalArgument, GoalPolarity, HandlerClause,
        ImplDecl, LifetimeOutlivesSyntax, LifetimeSyntax, Param, Pattern, PatternKind, Program,
        QuantitySyntax, ReferenceLifetimeSyntax, Stmt, StructDecl, TraitDecl, TraitRefSyntax,
        TypeAliasDecl, TypePathSegment, TypeSyntax, TypeSyntaxKind, UnaryOp, UseDecl, VariantDecl,
        WhereClause, WhereGoal,
    },
    diagnostic::Diagnostic,
    lexer::{Token, TokenKind},
    span::Span,
};

pub fn parse(tokens: Vec<Token>) -> Result<Program, Diagnostic> {
    let fixities = collect_fixities(&tokens)?;
    Parser {
        tokens,
        cursor: 0,
        fixities,
        reference_lifetimes: Vec::new(),
    }
    .program()
}

/// LSP divergence (see tooling/lsp/DIVERGENCES.md): parse collecting EVERY
/// declaration-level error instead of stopping at the first, synchronizing at
/// declaration boundaries, and returning the partial program alongside the
/// diagnostics. The batch `parse` above is untouched.
pub fn parse_resilient(tokens: Vec<Token>) -> (Program, Vec<Diagnostic>) {
    let (fixities, mut diagnostics) = match collect_fixities(&tokens) {
        Ok(fixities) => (fixities, Vec::new()),
        Err(diagnostic) => (HashMap::new(), vec![diagnostic]),
    };
    let parser = Parser {
        tokens,
        cursor: 0,
        fixities,
        reference_lifetimes: Vec::new(),
    };
    let (program, mut errors) = parser.program_resilient();
    diagnostics.append(&mut errors);
    (program, diagnostics)
}

struct Parser {
    tokens: Vec<Token>,
    cursor: usize,
    fixities: HashMap<String, (FixityKind, u8)>,
    reference_lifetimes: Vec<ReferenceLifetimeSyntax>,
}

/// Accumulator for top-level declarations (shared by the strict and the
/// resilient program loops).
#[derive(Default)]
struct Draft {
    effects: Vec<EffectDecl>,
    effect_row_aliases: Vec<EffectRowAliasDecl>,
    drops: Vec<DropDecl>,
    type_aliases: Vec<TypeAliasDecl>,
    globals: Vec<GlobalBinding>,
    fixities: Vec<FixityDecl>,
    structs: Vec<StructDecl>,
    enums: Vec<EnumDecl>,
    traits: Vec<TraitDecl>,
    impls: Vec<ImplDecl>,
    uses: Vec<UseDecl>,
    functions: Vec<Function>,
}

impl Draft {
    fn into_program(self, reference_lifetimes: Vec<ReferenceLifetimeSyntax>) -> Program {
        Program {
            type_aliases: self.type_aliases,
            effect_row_aliases: self.effect_row_aliases,
            globals: self.globals,
            fixities: self.fixities,
            structs: self.structs,
            enums: self.enums,
            traits: self.traits,
            impls: self.impls,
            uses: self.uses,
            effects: self.effects,
            drops: self.drops,
            functions: self.functions,
            reference_lifetimes,
        }
    }
}

impl Parser {
    /// Parse one top-level declaration into `draft`.
    fn declaration_step(&mut self, draft: &mut Draft) -> Result<(), Diagnostic> {
        if self.at_ident("type") {
            draft.type_aliases.push(self.type_alias()?);
        } else if self.at_ident("cases") {
            draft.effect_row_aliases.push(self.effect_row_alias()?);
        } else if self.at_ident("let") {
            draft.globals.push(self.global_binding()?);
        } else if self.at_ident("infixl") || self.at_ident("infixr") || self.at_ident("prefix") {
            draft.fixities.push(self.fixity_decl()?);
        } else if self.at_ident("effect") {
            draft.effects.push(self.effect()?);
        } else if self.at_ident("struct") {
            draft.structs.push(self.struct_decl()?);
        } else if self.at_ident("enum") {
            draft.enums.push(self.enum_decl()?);
        } else if self.at_ident("trait") {
            draft.traits.push(self.trait_decl()?);
        } else if self.at_ident("impl") {
            if self.at_drop_impl() {
                draft.drops.push(self.drop_impl()?);
            } else if self.at_use_impl() {
                draft.uses.push(self.use_impl()?);
            } else {
                draft.impls.push(self.impl_decl()?);
            }
        } else {
            draft.functions.push(self.function()?);
        }
        Ok(())
    }

    fn program(mut self) -> Result<Program, Diagnostic> {
        let mut draft = Draft::default();
        while !self.at(&TokenKind::Eof) {
            self.declaration_step(&mut draft)?;
        }
        if draft.functions.is_empty() {
            return Err(self.error(
                "program has no callables",
                "expected at least a `main() -> { ... }` declaration",
            ));
        }
        let reference_lifetimes = std::mem::take(&mut self.reference_lifetimes);
        Ok(draft.into_program(reference_lifetimes))
    }

    /// LSP divergence: collect every declaration-level error, resynchronize,
    /// keep the declarations that did parse.
    fn program_resilient(mut self) -> (Program, Vec<Diagnostic>) {
        let mut draft = Draft::default();
        let mut diagnostics = Vec::new();
        while !self.at(&TokenKind::Eof) {
            let before = self.cursor;
            if let Err(diagnostic) = self.declaration_step(&mut draft) {
                diagnostics.push(diagnostic);
                self.synchronize(before);
            }
        }
        let reference_lifetimes = std::mem::take(&mut self.reference_lifetimes);
        (draft.into_program(reference_lifetimes), diagnostics)
    }

    /// Skip forward to a plausible declaration boundary: either a top-level
    /// declaration keyword, or just past the `}` that closes the broken
    /// declaration's body. Guarantees progress.
    fn synchronize(&mut self, before: usize) {
        if self.cursor == before {
            self.bump();
        }
        let mut depth: i32 = 0;
        loop {
            match &self.peek().kind {
                TokenKind::Eof => return,
                TokenKind::LBrace => {
                    depth += 1;
                    self.bump();
                }
                TokenKind::RBrace => {
                    self.bump();
                    if depth <= 1 {
                        return;
                    }
                    depth -= 1;
                }
                TokenKind::Ident(word)
                    if depth == 0
                        && matches!(
                            word.as_str(),
                            "type" | "cases" | "let" | "infixl" | "infixr" | "prefix"
                                | "effect" | "struct" | "enum" | "trait" | "impl"
                        ) =>
                {
                    return;
                }
                _ => {
                    self.bump();
                }
            }
        }
    }

    fn trait_decl(&mut self) -> Result<TraitDecl, Diagnostic> {
        let start = self.bump().span;
        let (name, _) = self.ident("expected a marker trait name")?;
        let generics = self.generic_params()?;
        let mut supertraits = Vec::new();
        if self.eat(&TokenKind::Colon) {
            loop {
                supertraits.push(self.trait_ref()?);
                if !self.eat(&TokenKind::Plus) {
                    break;
                }
            }
        }
        self.expect(
            TokenKind::LBrace,
            "expected `{` after the marker trait declaration",
        )?;
        let mut associated_types = Vec::new();
        let mut names = std::collections::HashSet::new();
        while !self.at(&TokenKind::RBrace) {
            let item_start = self
                .expect_ident("type", "traits may declare only associated types")?
                .span;
            let (item_name, name_span) = self.ident("expected an associated type name")?;
            let generics = self.generic_params()?;
            self.reject_const_params(&generics, "associated type declarations")?;
            if self.at(&TokenKind::Eq) {
                return Err(self.error(
                    "associated type default",
                    "associated type defaults are not supported",
                ));
            }
            let end = self
                .expect(
                    TokenKind::Semicolon,
                    "expected `;` after the associated type declaration",
                )?
                .span;
            if !names.insert(item_name.clone()) {
                return Err(Diagnostic::error(
                    "duplicate associated type",
                    format!("associated type `{item_name}` is declared more than once"),
                    name_span,
                ));
            }
            associated_types.push(AssociatedTypeDecl {
                name: item_name,
                generics,
                span: item_start.join(end),
            });
        }
        let end = self.bump().span;
        Ok(TraitDecl {
            name,
            generics,
            supertraits,
            associated_types,
            span: start.join(end),
        })
    }

    fn impl_decl(&mut self) -> Result<ImplDecl, Diagnostic> {
        let start = self.bump().span;
        let generics = self.generic_params()?;
        let polarity = if self.eat(&TokenKind::Bang) {
            GoalPolarity::Negative
        } else {
            GoalPolarity::Positive
        };
        let trait_ref = self.trait_ref()?;
        if trait_ref.path.len() != 1 || !trait_ref.bindings.is_empty() {
            return Err(Diagnostic::error(
                "unsupported implementation trait",
                "marker implementations require one unqualified trait name and no associated bindings",
                trait_ref.span,
            ));
        }
        self.expect_ident("for", "expected `for` after the marker trait name")?;
        let self_ty = self.type_syntax()?;
        let where_clause = self.where_clause()?;
        self.expect(
            TokenKind::LBrace,
            "expected `{` after the marker implementation header",
        )?;
        let mut associated_types = Vec::new();
        let mut names = std::collections::HashSet::new();
        while !self.at(&TokenKind::RBrace) {
            let item_start = self
                .expect_ident(
                    "type",
                    "trait implementations may define only associated types",
                )?
                .span;
            let (item_name, name_span) = self.ident("expected an associated type name")?;
            let generics = self.generic_params()?;
            self.expect(
                TokenKind::Eq,
                "expected `=` in the associated type definition",
            )?;
            let value = self.type_syntax()?;
            let end = self
                .expect(
                    TokenKind::Semicolon,
                    "expected `;` after the associated type definition",
                )?
                .span;
            if !names.insert(item_name.clone()) {
                return Err(Diagnostic::error(
                    "duplicate associated type definition",
                    format!("associated type `{item_name}` is defined more than once"),
                    name_span,
                ));
            }
            associated_types.push(AssociatedTypeDefinition {
                name: item_name,
                generics,
                span: item_start.join(end),
                value,
            });
        }
        let end = self.bump().span;
        Ok(ImplDecl {
            generics,
            polarity,
            trait_ref,
            self_ty,
            where_clause,
            associated_types,
            span: start.join(end),
        })
    }

    fn use_impl(&mut self) -> Result<UseDecl, Diagnostic> {
        let start = self.bump().span;
        let generics = self.generic_params()?;
        self.reject_const_params(&generics, "dedicated Use implementations")?;
        let trait_ref = self.trait_ref()?;
        let [crate::frontend::ast::GoalArgument::Quantity(quantity)] = trait_ref.arguments.as_slice() else {
            return Err(Diagnostic::error(
                "invalid Use implementation",
                "Use requires exactly one `[lower, upper]` quantity argument",
                trait_ref.span,
            ));
        };
        if trait_ref.path.len() != 1
            || trait_ref.path[0].name != "Use"
            || !trait_ref.bindings.is_empty()
        {
            return Err(Diagnostic::error(
                "invalid Use implementation",
                "expected the intrinsic `Use<[lower, upper]>` trait",
                trait_ref.span,
            ));
        }
        self.expect_ident("for", "expected `for` after the Use quantity")?;
        let target = self.type_syntax()?;
        let where_clause = self.where_clause()?;
        self.expect(TokenKind::LBrace, "expected `{` after the Use target")?;
        if !self.at(&TokenKind::RBrace) {
            return Err(self.error(
                "nonempty Use implementation",
                "Use implementations cannot define methods or associated items",
            ));
        }
        let end = self.bump().span;
        Ok(UseDecl {
            generics,
            quantity: quantity.clone(),
            target,
            where_clause,
            span: start.join(end),
        })
    }

    fn drop_impl(&mut self) -> Result<DropDecl, Diagnostic> {
        let start = self.bump().span;
        let generics = self.generic_params()?;
        self.reject_const_params(&generics, "dedicated Drop implementations")?;
        self.expect_ident("Drop", "expected the intrinsic `Drop` trait")?;
        self.expect_ident("for", "expected `for` after `Drop`")?;
        let target_type = self.type_syntax()?;
        let target = match &target_type.kind {
            TypeSyntaxKind::Path(path) if path.len() == 1 => path[0].name.clone(),
            TypeSyntaxKind::Application { constructor, .. } => constructor
                .simple_name()
                .ok_or_else(|| {
                    Diagnostic::error(
                        "invalid Drop target",
                        "Drop requires one unqualified nominal constructor",
                        target_type.span,
                    )
                })?
                .to_owned(),
            _ => {
                return Err(Diagnostic::error(
                    "invalid Drop target",
                    "Drop requires one unqualified nominal type",
                    target_type.span,
                ));
            }
        };
        let where_clause = self.where_clause()?;
        self.expect(TokenKind::LBrace, "expected `{` after the Drop target")?;
        self.expect_ident("drop", "a Drop implementation must define `drop`")?;
        self.expect(TokenKind::LParen, "expected `(` after `drop`")?;
        self.expect(TokenKind::Amp, "Drop::drop receives `&mut self`")?;
        self.expect_ident("mut", "Drop::drop receives `&mut self`")?;
        let (receiver, self_span) = self.ident("Drop::drop must name its receiver `self`")?;
        if receiver != "self" {
            return Err(Diagnostic::error(
                "invalid Drop receiver",
                "the receiver must be named `self`",
                self_span,
            ));
        }
        self.expect(TokenKind::RParen, "expected `)` after `&mut self`")?;
        self.expect(TokenKind::Arrow, "Drop::drop must contain `->`")?;
        if self.at(&TokenKind::Slash) {
            return Err(Diagnostic::error(
                "Drop hook exposes effects",
                "Drop::drop cannot declare an outward effect row",
                self.peek().span,
            ));
        }
        let body = self.block()?;
        let end = self
            .expect(
                TokenKind::RBrace,
                "expected `}` after the Drop implementation",
            )?
            .span;
        Ok(DropDecl {
            target,
            generics,
            target_type,
            where_clause,
            body,
            self_span,
            span: start.join(end),
        })
    }

    fn at_drop_impl(&self) -> bool {
        self.at_intrinsic_impl("Drop")
    }

    fn at_use_impl(&self) -> bool {
        self.at_intrinsic_impl("Use")
    }

    fn at_intrinsic_impl(&self, intrinsic: &str) -> bool {
        let mut cursor = self.cursor + 1;
        if self
            .tokens
            .get(cursor)
            .is_some_and(|token| token.kind == TokenKind::Lt)
        {
            let mut depth = 0usize;
            while let Some(token) = self.tokens.get(cursor) {
                match token.kind {
                    TokenKind::Lt => depth += 1,
                    TokenKind::Gt => {
                        depth -= 1;
                        if depth == 0 {
                            cursor += 1;
                            break;
                        }
                    }
                    TokenKind::Eof => return false,
                    _ => {}
                }
                cursor += 1;
            }
        }
        self.tokens
            .get(cursor)
            .is_some_and(|token| matches!(&token.kind, TokenKind::Ident(name) if name == intrinsic))
    }

    fn type_alias(&mut self) -> Result<TypeAliasDecl, Diagnostic> {
        let start = self.bump().span;
        let (name, _) = self.ident("expected a type alias name")?;
        let generics = self.generic_params()?;
        self.reject_const_params(&generics, "type aliases")?;
        let generic_span = generics.as_ref().map(|generics| generics.span);
        self.expect(TokenKind::Eq, "expected `=` in the type alias")?;
        let target = self.type_syntax()?;
        let end = self
            .expect(TokenKind::Semicolon, "expected `;` after the type alias")?
            .span;
        Ok(TypeAliasDecl {
            name,
            generics,
            generic_span,
            target,
            span: start.join(end),
        })
    }

    fn effect_row_alias(&mut self) -> Result<EffectRowAliasDecl, Diagnostic> {
        let start = self.bump().span;
        let (name, _) = self.ident("expected an effect-row alias name")?;
        self.expect(TokenKind::Eq, "expected `=` in the effect-row alias")?;
        let row = self.effect_row()?;
        if let Some(tail) = &row.tail {
            return Err(Diagnostic::error(
                "unsupported open effect-row alias",
                "effect-row aliases are closed in this compiler slice",
                tail.span,
            ));
        }
        let end = self
            .expect(
                TokenKind::Semicolon,
                "expected `;` after the effect-row alias",
            )?
            .span;
        Ok(EffectRowAliasDecl {
            name,
            row,
            span: start.join(end),
        })
    }

    fn global_binding(&mut self) -> Result<GlobalBinding, Diagnostic> {
        let start = self.bump().span;
        let (first, _) = self.ident("expected a global binding name")?;
        let (owner, name) = if self.eat(&TokenKind::DoubleColon) {
            let (name, _) = self.ident("expected an associated binding name after `::`")?;
            if self.at(&TokenKind::DoubleColon) {
                return Err(self.error(
                    "associated binding owner is too deeply qualified",
                    "top-level qualified value declarations have exactly one type owner",
                ));
            }
            (Some(first), name)
        } else {
            (None, first)
        };
        self.expect(TokenKind::Eq, "expected `=` in the global binding")?;
        let value = self.expression(0)?;
        let end = self
            .expect(
                TokenKind::Semicolon,
                "expected `;` after the global binding",
            )?
            .span;
        Ok(GlobalBinding {
            owner,
            name,
            value,
            span: start.join(end),
        })
    }

    fn fixity_decl(&mut self) -> Result<FixityDecl, Diagnostic> {
        let keyword = self.bump().clone();
        let kind = match &keyword.kind {
            TokenKind::Ident(name) if name == "infixl" => FixityKind::Infix(Associativity::Left),
            TokenKind::Ident(name) if name == "infixr" => FixityKind::Infix(Associativity::Right),
            TokenKind::Ident(name) if name == "prefix" => FixityKind::Prefix,
            _ => unreachable!(),
        };
        let precedence_token = self.bump().clone();
        let TokenKind::Int(precedence) = precedence_token.kind else {
            return Err(Diagnostic::error(
                "expected operator precedence",
                "fixity declarations use an integer from 0 through 255",
                precedence_token.span,
            ));
        };
        let precedence = u8::try_from(precedence).map_err(|_| {
            Diagnostic::error(
                "invalid operator precedence",
                "operator precedence must be from 0 through 255",
                precedence_token.span,
            )
        })?;
        let (name, _) = self.ident("expected an operator name")?;
        let end = self
            .expect(
                TokenKind::Semicolon,
                "expected `;` after the fixity declaration",
            )?
            .span;
        Ok(FixityDecl {
            name,
            kind,
            precedence,
            span: keyword.span.join(end),
        })
    }

    fn struct_decl(&mut self) -> Result<StructDecl, Diagnostic> {
        let start = self.bump().span;
        let (name, _) = self.ident("expected a struct name")?;
        let generics = self.generic_params()?;
        self.reject_const_params(&generics, "struct declarations")?;
        let generic_span = generics.as_ref().map(|generics| generics.span);
        self.expect(TokenKind::LBrace, "expected `{` after the struct name")?;
        let mut fields = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            let (visibility, visibility_span) = if self.at_ident("private")
                && matches!(
                    self.peek_n(1).map(|token| &token.kind),
                    Some(TokenKind::Ident(_))
                ) {
                let span = self.bump().span;
                (FieldVisibility::Private, Some(span))
            } else {
                (FieldVisibility::Public, None)
            };
            let (field, field_span) = self.ident("expected a field name")?;
            self.expect(TokenKind::Colon, "expected `:` and a field type")?;
            let ty = self.type_syntax()?;
            fields.push(FieldDecl {
                name: field,
                span: visibility_span.unwrap_or(field_span).join(ty.span),
                ty,
                visibility,
            });
            self.eat(&TokenKind::Comma);
            self.eat(&TokenKind::Semicolon);
        }
        let end = self
            .expect(TokenKind::RBrace, "expected `}` after struct fields")?
            .span;
        Ok(StructDecl {
            name,
            generics,
            generic_span,
            fields,
            span: start.join(end),
        })
    }

    fn enum_decl(&mut self) -> Result<EnumDecl, Diagnostic> {
        let start = self.bump().span;
        let (name, _) = self.ident("expected an enum name")?;
        let generics = self.generic_params()?;
        self.reject_const_params(&generics, "enum declarations")?;
        let generic_span = generics.as_ref().map(|generics| generics.span);
        self.expect(TokenKind::LBrace, "expected `{` after the enum name")?;
        let mut variants = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            let (variant, variant_span) = self.ident("expected a variant name")?;
            let mut fields = Vec::new();
            if self.eat(&TokenKind::LParen) {
                while !self.at(&TokenKind::RParen) {
                    fields.push(self.type_syntax()?);
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                self.expect(TokenKind::RParen, "expected `)` after variant fields")?;
            }
            variants.push(VariantDecl {
                name: variant,
                fields,
                span: variant_span,
            });
            self.eat(&TokenKind::Comma);
            self.eat(&TokenKind::Semicolon);
        }
        let end = self
            .expect(TokenKind::RBrace, "expected `}` after enum variants")?
            .span;
        Ok(EnumDecl {
            name,
            generics,
            generic_span,
            variants,
            span: start.join(end),
        })
    }

    fn effect(&mut self) -> Result<EffectDecl, Diagnostic> {
        let start = self.bump().span;
        let (name, _) = self.ident("expected an effect name")?;
        let generics = self.generic_params()?;
        self.reject_const_params(&generics, "effect declarations")?;
        let generic_span = generics.as_ref().map(|generics| generics.span);
        self.expect(TokenKind::LBrace, "expected `{` after the effect name")?;
        let mut operations = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            if self.at(&TokenKind::Eof) {
                return Err(self.error("unfinished effect", "expected `}` to close this effect"));
            }
            let (resumption_lower, resumption_upper, has_resumption_quantity) =
                if self.eat(&TokenKind::LBracket) {
                    let lower = match self.bump().clone() {
                        Token {
                            kind: TokenKind::Int(value),
                            span: _,
                        } if value >= 0 => value as usize,
                        token => {
                            return Err(Diagnostic::error(
                                "invalid resumption quantity",
                                "the lower bound must be a non-negative integer",
                                token.span,
                            ));
                        }
                    };
                    self.expect(TokenKind::Comma, "expected `,` between quantity bounds")?;
                    let upper = match self.bump().clone() {
                        Token {
                            kind: TokenKind::Int(value),
                            span: _,
                        } if value >= 0 => Some(value as usize),
                        Token {
                            kind: TokenKind::Star,
                            ..
                        } => None,
                        Token {
                            kind: TokenKind::Ident(name),
                            ..
                        } if name == "infinity" => None,
                        token => {
                            return Err(Diagnostic::error(
                                "invalid resumption quantity",
                                "the upper bound must be a non-negative integer or `infinity`",
                                token.span,
                            ));
                        }
                    };
                    self.expect(TokenKind::RBracket, "expected `]` after quantity bounds")?;
                    (lower, upper, true)
                } else {
                    (1, Some(1), false)
                };
            let (operation, operation_span) = self.ident("expected an operation name")?;
            self.expect(TokenKind::LParen, "expected `(` after the operation name")?;
            let mut params = Vec::new();
            while !self.at(&TokenKind::RParen) {
                let (name, span) = self.ident("expected an operation parameter name")?;
                self.expect(TokenKind::Colon, "expected `:` and a parameter type")?;
                let ty = self.type_syntax()?;
                params.push(Param {
                    name,
                    span: span.join(ty.span),
                    ty,
                });
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(TokenKind::RParen, "expected `)` after operation parameters")?;
            self.expect(TokenKind::Arrow, "expected `->` in the operation signature")?;
            let terminal = self.at(&TokenKind::Bang);
            let return_type = if self.at(&TokenKind::Semicolon) || self.at(&TokenKind::RBrace) {
                None
            } else {
                Some(self.type_syntax()?)
            };
            operations.push(EffectOperationDecl {
                name: operation,
                params,
                return_type,
                terminal,
                resumption_lower,
                resumption_upper,
                has_resumption_quantity,
                span: operation_span,
            });
            self.eat(&TokenKind::Semicolon);
        }
        let end = self.bump().span;
        Ok(EffectDecl {
            name,
            generics,
            generic_span,
            operations,
            span: start.join(end),
        })
    }

    fn function(&mut self) -> Result<Function, Diagnostic> {
        let (name, name_span) = self.ident("expected a callable declaration")?;
        let generics = self.generic_params()?;
        self.reject_const_params(&generics, "callable declarations")?;
        self.expect(TokenKind::LParen, "expected `(` after the callable name")?;
        let mut params = Vec::new();
        while !self.at(&TokenKind::RParen) {
            let (param_name, span) = self.ident("expected a parameter name")?;
            self.expect(TokenKind::Colon, "expected `:` and a parameter type")?;
            let ty = self.type_syntax()?;
            let span = span.join(ty.span);
            params.push(Param {
                name: param_name,
                ty,
                span,
            });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RParen, "expected `)` after parameters")?;
        self.expect(
            TokenKind::Arrow,
            "every callable signature must contain `->`",
        )?;
        let return_type = if self.at(&TokenKind::LBrace) || self.at(&TokenKind::Slash) {
            None
        } else {
            Some(self.type_syntax()?)
        };
        let outward_effects = if self.eat(&TokenKind::Slash) {
            Some(self.effect_row()?)
        } else {
            None
        };
        let where_clause = self.where_clause()?;
        for tail in outward_effects
            .iter()
            .filter_map(|row| row.tail.as_ref())
            .chain(
                where_clause
                    .iter()
                    .flat_map(|clause| &clause.goals)
                    .flat_map(|goal| &goal.relation.bindings)
                    .filter_map(|binding| match &binding.value {
                        AssociatedBindingValue::EffectRow(row) => row.tail.as_ref(),
                        AssociatedBindingValue::Type(_) => None,
                    }),
            )
        {
            let binder = generics
                .iter()
                .flat_map(|generics| &generics.params)
                .find(|parameter| parameter.name == tail.name);
            match binder.map(|binder| binder.kind) {
                Some(GenericParamKind::EffectRow) => {}
                Some(_) => {
                    return Err(Diagnostic::error(
                        "effect-row tail kind mismatch",
                        format!(
                            "`{}` is not an `EffectRow` binder; declare `<{}: EffectRow>`",
                            tail.name, tail.name
                        ),
                        tail.span,
                    ));
                }
                None => {
                    return Err(Diagnostic::error(
                        "unbound effect-row tail",
                        format!(
                            "effect-row variable `{}` is not bound by this callable",
                            tail.name
                        ),
                        tail.span,
                    ));
                }
            }
        }
        let body = self.block()?;
        let span = name_span.join(body.span);
        Ok(Function {
            name,
            generics,
            params,
            return_type,
            effectful: outward_effects.is_some(),
            outward_effects,
            where_clause,
            body,
            span,
        })
    }

    fn generic_params(&mut self) -> Result<Option<GenericParams>, Diagnostic> {
        if !self.at(&TokenKind::Lt) {
            return Ok(None);
        }
        let start = self.bump().span;
        let mut params = Vec::new();
        let mut names = std::collections::HashSet::new();
        if self.at(&TokenKind::Gt) {
            return Err(self.error("empty generic binder list", "expected a type parameter"));
        }
        loop {
            if self.at(&TokenKind::Amp) || self.at_ident("for") {
                return Err(self.error(
                    "unsupported generic binder",
                    "higher-ranked `for<...>` binders are not implemented",
                ));
            }
            let (name, span, kind) = if let TokenKind::Lifetime(name) = &self.peek().kind {
                let name = name.clone();
                let span = self.bump().span;
                (name, span, GenericParamKind::Lifetime)
            } else if self.at_ident("const") {
                let start = self.bump().span;
                let (name, _) = self.ident("expected a const parameter name")?;
                self.expect(TokenKind::Colon, "expected `:` after const parameter name")?;
                let (kind, kind_span) = if self.at_ident("Quantity") {
                    (ConstKind::Quantity, self.bump().span)
                } else if self.at_ident("u32") {
                    (ConstKind::U32, self.bump().span)
                } else {
                    return Err(self.error(
                        "unsupported const parameter type",
                        "trait const parameters currently support only `Quantity` and `u32`",
                    ));
                };
                (name, start.join(kind_span), GenericParamKind::Const(kind))
            } else {
                let (name, start) = self.ident("expected a generic type parameter")?;
                if self.eat(&TokenKind::Colon) {
                    if !self.at_ident("EffectRow") {
                        return Err(self.error(
                            "unsupported generic parameter kind",
                            "generic parameters may be types or explicitly kinded as `EffectRow`",
                        ));
                    }
                    let end = self.bump().span;
                    (name, start.join(end), GenericParamKind::EffectRow)
                } else {
                    (name, start, GenericParamKind::Type)
                }
            };
            if !names.insert(name.clone()) {
                return Err(Diagnostic::error(
                    "duplicate generic parameter",
                    format!("`{name}` is bound more than once"),
                    span,
                ));
            }
            params.push(GenericParam { name, kind, span });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
            if self.at(&TokenKind::Gt) {
                break;
            }
        }
        let end = self
            .expect(TokenKind::Gt, "expected `>` after generic parameters")?
            .span;
        Ok(Some(GenericParams {
            params,
            span: start.join(end),
        }))
    }

    fn reject_const_params(
        &self,
        generics: &Option<GenericParams>,
        context: &str,
    ) -> Result<(), Diagnostic> {
        if let Some(parameter) = generics
            .iter()
            .flat_map(|generics| &generics.params)
            .find(|parameter| matches!(parameter.kind, GenericParamKind::Const(_)))
        {
            return Err(Diagnostic::error(
                "unsupported const generic binder",
                format!(
                    "const generic binders are currently supported only on traits and ordinary trait implementations, not {context}"
                ),
                parameter.span,
            ));
        }
        Ok(())
    }

    fn effect_row(&mut self) -> Result<EffectRowSyntax, Diagnostic> {
        let start = self
            .expect(TokenKind::LBrace, "expected `{` to begin an effect row")?
            .span;
        let mut effects = Vec::new();
        while !self.at(&TokenKind::RBrace) && !self.at(&TokenKind::Pipe) {
            if self.at(&TokenKind::Eof) {
                return Err(self.error("unfinished effect row", "expected `}` to close the row"));
            }
            effects.push(self.type_syntax()?);
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        let tail = if self.eat(&TokenKind::Pipe) {
            let (name, span) = self.ident("expected an effect-row variable after `|`")?;
            Some(TypePathSegment { name, span })
        } else {
            None
        };
        let end = self
            .expect(TokenKind::RBrace, "expected `}` after the effect row")?
            .span;
        Ok(EffectRowSyntax {
            effects,
            tail,
            span: start.join(end),
        })
    }

    fn where_clause(&mut self) -> Result<Option<WhereClause>, Diagnostic> {
        if !self.at_ident("where") {
            return Ok(None);
        }
        let start = self.bump().span;
        let mut goals = Vec::new();
        let mut lifetime_outlives = Vec::new();
        loop {
            let higher_ranked_lifetimes = if self.at_ident("for") {
                self.bump();
                let Some(parameters) = self.generic_params()? else {
                    return Err(self.error(
                        "malformed higher-ranked binder",
                        "expected a non-empty lifetime binder list after `for`",
                    ));
                };
                if let Some(parameter) = parameters
                    .params
                    .iter()
                    .find(|parameter| parameter.kind != GenericParamKind::Lifetime)
                {
                    return Err(Diagnostic::error(
                        "unsupported higher-ranked binder kind",
                        "higher-ranked where goals currently bind lifetimes only",
                        parameter.span,
                    ));
                }
                parameters.params
            } else {
                vec![]
            };
            if let TokenKind::Lifetime(name) = &self.peek().kind {
                if !higher_ranked_lifetimes.is_empty() {
                    return Err(self.error(
                        "unsupported higher-ranked outlives constraint",
                        "higher-ranked lifetime outlives constraints are not implemented",
                    ));
                }
                let longer = LifetimeSyntax {
                    name: name.clone(),
                    span: self.bump().span,
                };
                self.expect(TokenKind::Colon, "expected `:` in a lifetime outlives goal")?;
                let TokenKind::Lifetime(name) = &self.peek().kind else {
                    return Err(self.error(
                        "malformed lifetime outlives constraint",
                        "expected a lifetime after `:`",
                    ));
                };
                let shorter = LifetimeSyntax {
                    name: name.clone(),
                    span: self.bump().span,
                };
                let span = longer.span.join(shorter.span);
                lifetime_outlives.push(LifetimeOutlivesSyntax {
                    longer,
                    shorter,
                    span,
                });
                if !self.eat(&TokenKind::Comma) || self.at(&TokenKind::LBrace) {
                    break;
                }
                continue;
            }
            let subject = self.type_syntax()?;
            self.expect(TokenKind::Colon, "expected `:` in a where goal")?;
            let polarity = if self.eat(&TokenKind::Bang) {
                GoalPolarity::Negative
            } else {
                GoalPolarity::Positive
            };
            let relation = self.trait_ref()?;
            let span = subject.span.join(relation.span);
            goals.push(WhereGoal {
                higher_ranked_lifetimes,
                subject,
                polarity,
                relation,
                span,
            });
            if !self.eat(&TokenKind::Comma) || self.at(&TokenKind::LBrace) {
                break;
            }
        }
        let end = goals
            .last()
            .map(|goal| goal.span)
            .into_iter()
            .chain(lifetime_outlives.last().map(|constraint| constraint.span))
            .max_by_key(|span| span.end)
            .expect("where has a goal");
        Ok(Some(WhereClause {
            goals,
            lifetime_outlives,
            span: start.join(end),
        }))
    }

    fn trait_ref(&mut self) -> Result<TraitRefSyntax, Diagnostic> {
        let (name, start) = self.ident("expected a relation name in the where goal")?;
        let mut path = vec![TypePathSegment { name, span: start }];
        while self.eat(&TokenKind::DoubleColon) {
            let (name, span) = self.ident("expected a relation path segment")?;
            path.push(TypePathSegment { name, span });
        }
        let mut arguments = Vec::new();
        let mut bindings = Vec::new();
        let mut binding_keys = Vec::<(String, Vec<AssociatedArgumentSyntax>)>::new();
        let mut end = path.last().unwrap().span;
        if self.eat(&TokenKind::Lt) {
            if self.at(&TokenKind::Gt) {
                return Err(self.error("empty relation arguments", "expected an argument"));
            }
            loop {
                if self.at_associated_binding() {
                    let TokenKind::Ident(binding) = &self.peek().kind else {
                        unreachable!()
                    };
                    let binding = binding.clone();
                    let binding_span = self.bump().span;
                    let arguments = self.type_argument_list()?;
                    self.expect(TokenKind::Eq, "expected `=` in associated binding")?;
                    if binding_keys
                        .iter()
                        .any(|(name, existing)| name == &binding && existing == &arguments)
                    {
                        return Err(Diagnostic::error(
                            "duplicate associated binding",
                            format!(
                                "`{binding}` with the same arguments is assigned more than once"
                            ),
                            binding_span,
                        ));
                    }
                    binding_keys.push((binding.clone(), arguments.clone()));
                    let value = if self.at(&TokenKind::LBrace) {
                        AssociatedBindingValue::EffectRow(self.effect_row()?)
                    } else {
                        AssociatedBindingValue::Type(self.type_syntax()?)
                    };
                    let value_span = value.span();
                    bindings.push(AssociatedBinding {
                        name: binding,
                        arguments,
                        span: binding_span.join(value_span),
                        value,
                    });
                } else if let TokenKind::Lifetime(name) = &self.peek().kind {
                    let name = name.clone();
                    let span = self.bump().span;
                    arguments.push(GoalArgument::Lifetime { name, span });
                } else if self.at(&TokenKind::LBracket) {
                    arguments.push(GoalArgument::Quantity(self.quantity()?));
                } else if let TokenKind::Int(value) = self.peek().kind
                    && value >= 0
                {
                    let span = self.bump().span;
                    arguments.push(GoalArgument::U32 {
                        value: value as u64,
                        span,
                    });
                } else {
                    arguments.push(GoalArgument::Type(self.type_syntax()?));
                }
                if !self.eat(&TokenKind::Comma) || self.at(&TokenKind::Gt) {
                    break;
                }
            }
            end = self
                .expect(TokenKind::Gt, "expected `>` after relation arguments")?
                .span;
        }
        Ok(TraitRefSyntax {
            path,
            arguments,
            bindings,
            span: start.join(end),
        })
    }

    fn quantity(&mut self) -> Result<QuantitySyntax, Diagnostic> {
        let start = self.bump().span;
        let lower = match self.bump().clone() {
            Token {
                kind: TokenKind::Int(value),
                ..
            } if value >= 0 => value as u64,
            token => {
                return Err(Diagnostic::error(
                    "invalid use quantity",
                    "expected a non-negative lower bound",
                    token.span,
                ));
            }
        };
        self.expect(TokenKind::Comma, "expected `,` between quantity bounds")?;
        let upper = match self.bump().clone() {
            Token {
                kind: TokenKind::Int(value),
                ..
            } if value >= 0 => Some(value as u64),
            Token {
                kind: TokenKind::Star,
                ..
            } => None,
            Token {
                kind: TokenKind::Ident(name),
                ..
            } if name == "infinity" => None,
            token => {
                return Err(Diagnostic::error(
                    "invalid use quantity",
                    "expected a non-negative upper bound, `infinity`, or `*`",
                    token.span,
                ));
            }
        };
        let end = self
            .expect(TokenKind::RBracket, "expected `]` after quantity")?
            .span;
        Ok(QuantitySyntax {
            lower,
            upper,
            span: start.join(end),
        })
    }

    fn block(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.expect(TokenKind::LBrace, "expected a block")?.span;
        let mut statements = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            if self.at(&TokenKind::Eof) {
                return Err(self.error("unfinished block", "expected `}` to close this block"));
            }
            if self.at_ident("let") {
                let let_span = self.bump().span;
                if self.eat(&TokenKind::LParen) {
                    let mut fields = Vec::new();
                    let mut before_rest = 0usize;
                    let mut after_rest = 0usize;
                    let mut rest = None;
                    let mut saw_comma = false;
                    while !self.at(&TokenKind::RParen) {
                        if self.at(&TokenKind::DotDot) {
                            let rest_span = self.bump().span;
                            if rest.replace(rest_span).is_some() {
                                return Err(Diagnostic::error(
                                    "duplicate tuple remainder",
                                    "a tuple deconstruction may contain only one `..` remainder",
                                    rest_span,
                                ));
                            }
                            if !self.eat(&TokenKind::Comma) {
                                break;
                            }
                            saw_comma = true;
                            continue;
                        }
                        let (name, binding_span) =
                            self.ident("expected a binding, `_`, or `..` in tuple deconstruction")?;
                        let from_end = rest.is_some();
                        let field = if from_end {
                            after_rest += 1;
                            after_rest.to_string()
                        } else {
                            let field = before_rest.to_string();
                            before_rest += 1;
                            field
                        };
                        fields.push(DeconstructField {
                            field,
                            binding: (name != "_").then_some(name),
                            from_end,
                            span: binding_span,
                        });
                        if !self.eat(&TokenKind::Comma) {
                            break;
                        }
                        saw_comma = true;
                    }
                    if rest.is_none() && fields.len() == 1 && !saw_comma {
                        return Err(self.error(
                            "invalid singleton tuple deconstruction",
                            "a singleton tuple pattern requires a trailing comma: `(binding,)`",
                        ));
                    }
                    if rest.is_some() {
                        for field in fields.iter_mut().filter(|field| field.from_end) {
                            let ordinal = field.field.parse::<usize>().unwrap();
                            field.field = (after_rest - ordinal + 1).to_string();
                        }
                    }
                    self.expect(TokenKind::RParen, "expected `)` after tuple deconstruction")?;
                    self.expect(TokenKind::Eq, "expected `=` after tuple deconstruction")?;
                    let value = self.expression(0)?;
                    let span = let_span.join(value.span);
                    statements.push(Stmt::Deconstruct {
                        ty: None,
                        fields,
                        rest,
                        value,
                        span,
                    });
                    self.eat(&TokenKind::Semicolon);
                    continue;
                }
                let (name, _) = self.ident("expected a binding or struct name after `let`")?;
                if self.eat(&TokenKind::LBrace) {
                    let mut fields = Vec::new();
                    let mut rest = None;
                    while !self.at(&TokenKind::RBrace) {
                        if self.at(&TokenKind::DotDot) {
                            let rest_span = self.bump().span;
                            if rest.replace(rest_span).is_some() {
                                return Err(Diagnostic::error(
                                    "duplicate struct remainder",
                                    "a struct deconstruction may contain only one `..` remainder",
                                    rest_span,
                                ));
                            }
                            if !self.eat(&TokenKind::Comma) {
                                break;
                            }
                            continue;
                        }
                        let (field, field_span) = self.ident("expected a struct field name")?;
                        let (binding, end) = if self.eat(&TokenKind::Colon) {
                            let (binding, span) =
                                self.ident("expected a binding name or `_` after `:`")?;
                            ((binding != "_").then_some(binding), span)
                        } else {
                            (Some(field.clone()), field_span)
                        };
                        fields.push(DeconstructField {
                            field,
                            binding,
                            from_end: false,
                            span: field_span.join(end),
                        });
                        if !self.eat(&TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(
                        TokenKind::RBrace,
                        "expected `}` after struct deconstruction",
                    )?;
                    self.expect(TokenKind::Eq, "expected `=` after struct deconstruction")?;
                    let value = self.expression(0)?;
                    let span = let_span.join(value.span);
                    statements.push(Stmt::Deconstruct {
                        ty: Some(name),
                        fields,
                        rest,
                        value,
                        span,
                    });
                } else {
                    self.expect(TokenKind::Eq, "expected `=` in this binding")?;
                    let value = self.expression(0)?;
                    let span = let_span.join(value.span);
                    statements.push(Stmt::Let { name, value, span });
                }
            } else {
                statements.push(Stmt::Expr(self.expression(0)?));
            }
            self.eat(&TokenKind::Semicolon);
        }
        let end = self.bump().span;
        Ok(Expr {
            kind: ExprKind::Block(Rc::new(statements)),
            span: start.join(end),
        })
    }

    fn expression(&mut self, min_precedence: u8) -> Result<Expr, Diagnostic> {
        let mut lhs = self.primary()?;
        loop {
            if let Some((name, associativity, precedence, operator_span)) = self.word_infix()
                && precedence >= min_precedence
            {
                self.bump();
                let rhs_precedence = match associativity {
                    Associativity::Left => precedence.saturating_add(1),
                    Associativity::Right => precedence,
                };
                let rhs = self.expression(rhs_precedence)?;
                let span = lhs.span.join(rhs.span);
                lhs = Expr {
                    kind: ExprKind::Call(
                        Rc::new(Expr {
                            kind: ExprKind::Variable(Rc::from([Rc::from(name.as_str())])),
                            span: operator_span,
                        }),
                        Rc::new(vec![lhs, rhs]),
                    ),
                    span,
                };
                continue;
            }
            if let Some((op, precedence)) = self.binary_op()
                && precedence >= min_precedence
            {
                self.bump();
                let rhs = self.expression(precedence.saturating_add(1))?;
                let span = lhs.span.join(rhs.span);
                lhs = Expr {
                    kind: ExprKind::Binary {
                        op,
                        lhs: Rc::new(lhs),
                        rhs: Rc::new(rhs),
                    },
                    span,
                };
                continue;
            }
            break;
        }
        Ok(lhs)
    }

    fn primary(&mut self) -> Result<Expr, Diagnostic> {
        if self.at_ident("perform") {
            return self.perform();
        }
        if self.at_ident("handle") {
            return self.handle();
        }
        if self.at_ident("move") {
            let start = self.bump().span;
            let operand = self.primary()?;
            let span = start.join(operand.span);
            return Ok(Expr {
                kind: ExprKind::Move(Rc::new(operand)),
                span,
            });
        }
        if self.at(&TokenKind::Minus) {
            let start = self.bump().span;
            let operand = self.primary()?;
            let span = start.join(operand.span);
            return Ok(Expr {
                kind: ExprKind::Unary {
                    op: UnaryOp::Negate,
                    operand: Rc::new(operand),
                },
                span,
            });
        }
        if self.at(&TokenKind::Amp) {
            let start = self.bump().span;
            let unique = if self.at_ident("mut") {
                self.bump();
                true
            } else {
                false
            };
            let operand = self.primary()?;
            let span = start.join(operand.span);
            return Ok(Expr {
                kind: ExprKind::Unary {
                    op: if unique {
                        UnaryOp::BorrowUnique
                    } else {
                        UnaryOp::BorrowShared
                    },
                    operand: Rc::new(operand),
                },
                span,
            });
        }
        if self.at(&TokenKind::Star) {
            let start = self.bump().span;
            let operand = self.primary()?;
            let span = start.join(operand.span);
            return Ok(Expr {
                kind: ExprKind::Unary {
                    op: UnaryOp::Dereference,
                    operand: Rc::new(operand),
                },
                span,
            });
        }
        if let TokenKind::Ident(name) = &self.peek().kind
            && let Some((FixityKind::Prefix, precedence)) = self.fixities.get(name).copied()
        {
            let name = name.clone();
            let operator = self.bump().clone();
            let operand = self.expression(precedence)?;
            let span = operator.span.join(operand.span);
            return Ok(Expr {
                kind: ExprKind::Call(
                    Rc::new(Expr {
                        kind: ExprKind::Variable(Rc::from([Rc::from(name.as_str())])),
                        span: operator.span,
                    }),
                    Rc::new(vec![operand]),
                ),
                span,
            });
        }
        let token = self.bump().clone();
        let mut expr = match token.kind {
            TokenKind::Int(value) => Expr {
                kind: ExprKind::Int(value),
                span: token.span,
            },
            TokenKind::String(value) => Expr {
                kind: ExprKind::String(value.into()),
                span: token.span,
            },
            TokenKind::Ident(name) => {
                let mut path: Vec<Rc<str>> = vec![Rc::from(name.as_str())];
                let mut end = token.span;
                while self.eat(&TokenKind::DoubleColon) {
                    let (part, span) = self.ident("expected a name after `::`")?;
                    path.push(Rc::from(part.as_str()));
                    end = span;
                }
                Expr {
                    kind: ExprKind::Variable(Rc::from(path)),
                    span: token.span.join(end),
                }
            }
            TokenKind::LParen => {
                if self.eat(&TokenKind::RParen) {
                    Expr {
                        kind: ExprKind::Unit,
                        span: token.span.join(self.previous().span),
                    }
                } else {
                    let first = self.expression(0)?;
                    if self.eat(&TokenKind::Comma) {
                        let mut elements = vec![first];
                        while !self.at(&TokenKind::RParen) {
                            elements.push(self.expression(0)?);
                            if !self.eat(&TokenKind::Comma) {
                                break;
                            }
                        }
                        let end = self.expect(TokenKind::RParen, "expected `)`")?.span;
                        return Ok(Expr {
                            kind: ExprKind::Tuple(Rc::new(elements)),
                            span: token.span.join(end),
                        });
                    }
                    let end = self.expect(TokenKind::RParen, "expected `)`")?.span;
                    Expr {
                        kind: first.kind,
                        span: token.span.join(end),
                    }
                }
            }
            TokenKind::LBracket => {
                let mut values = Vec::new();
                while !self.at(&TokenKind::RBracket) {
                    values.push(self.expression(0)?);
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                let end = self
                    .expect(TokenKind::RBracket, "expected `]` after list elements")?
                    .span;
                Expr {
                    kind: ExprKind::List(Rc::new(values)),
                    span: token.span.join(end),
                }
            }
            TokenKind::LBrace => self.braced_expression(token.span)?,
            _ => {
                return Err(Diagnostic::error(
                    "expected an expression",
                    "a value or callable invocation is required here",
                    token.span,
                ));
            }
        };
        loop {
            if self.at(&TokenKind::LBrace)
                && matches!(&expr.kind, ExprKind::Call(_, _))
                && !self.looks_like_handler_clause_block()
            {
                let block = self.block()?;
                let span = expr.span.join(block.span);
                let ExprKind::Call(callee, args) = expr.kind else {
                    unreachable!()
                };
                let mut args = Rc::try_unwrap(args).unwrap_or_else(|shared| (*shared).clone());
                args.push(block);
                expr = Expr {
                    kind: ExprKind::Call(callee, Rc::new(args)),
                    span,
                };
            } else if self.at(&TokenKind::LBrace)
                && matches!(&expr.kind, ExprKind::Variable(path) if path.len() == 1)
            {
                let ExprKind::Variable(path) = &expr.kind else {
                    unreachable!()
                };
                let name: Rc<str> = path[0].clone();
                self.bump();
                let mut fields = Vec::new();
                while !self.at(&TokenKind::RBrace) {
                    let (field, _) = self.ident("expected a struct field name")?;
                    self.expect(TokenKind::Colon, "expected `:` after the field name")?;
                    fields.push((field, self.expression(0)?));
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                let end = self
                    .expect(TokenKind::RBrace, "expected `}` after struct fields")?
                    .span;
                let span = expr.span.join(end);
                expr = Expr {
                    kind: ExprKind::Struct {
                        name,
                        fields: Rc::new(fields),
                    },
                    span,
                };
            } else if self.eat(&TokenKind::Dot) {
                let (field, end) = match self.bump().clone() {
                    Token {
                        kind: TokenKind::Ident(field),
                        span,
                    } => (field, span),
                    Token {
                        kind: TokenKind::Int(field),
                        span,
                    } if field >= 0 => (field.to_string(), span),
                    token => {
                        return Err(Diagnostic::error(
                            "unexpected syntax",
                            "expected a field name or tuple index after `.`",
                            token.span,
                        ));
                    }
                };
                let span = expr.span.join(end);
                expr = Expr {
                    kind: ExprKind::Field(Rc::new(expr), field),
                    span,
                };
            } else if self.at(&TokenKind::LParen) {
                self.bump();
                let mut args = Vec::new();
                while !self.at(&TokenKind::RParen) {
                    args.push(self.expression(0)?);
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                let end = self
                    .expect(TokenKind::RParen, "expected `)` after arguments")?
                    .span;
                let span = expr.span.join(end);
                expr = Expr {
                    kind: ExprKind::Call(Rc::new(expr), Rc::new(args)),
                    span,
                };
            } else {
                break;
            }
        }
        Ok(expr)
    }

    /// A call followed by `{...}` normally receives a contextual block
    /// argument. Inside `handle call(...) { Effect::op(...) ... => ... }`, the
    /// same brace starts the handler matrix. Recognize that boundary by nested
    /// delimiter structure rather than by searching for the first `}`.
    fn looks_like_handler_clause_block(&self) -> bool {
        if !self.at(&TokenKind::LBrace) {
            return false;
        }
        let mut cursor = self.cursor + 1;
        if !matches!(
            self.tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::Ident(_))
        ) || !matches!(
            self.tokens.get(cursor + 1).map(|token| &token.kind),
            Some(TokenKind::DoubleColon)
        ) || !matches!(
            self.tokens.get(cursor + 2).map(|token| &token.kind),
            Some(TokenKind::Ident(_))
        ) || !matches!(
            self.tokens.get(cursor + 3).map(|token| &token.kind),
            Some(TokenKind::LParen)
        ) {
            return false;
        }
        cursor += 4;
        let mut depth = 1_usize;
        while depth != 0 {
            let Some(token) = self.tokens.get(cursor) else {
                return false;
            };
            match token.kind {
                TokenKind::LParen => depth += 1,
                TokenKind::RParen => depth -= 1,
                TokenKind::Eof => return false,
                _ => {}
            }
            cursor += 1;
        }
        if matches!(
            self.tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::Ident(name)) if name == "with"
        ) {
            cursor += 1;
            if !matches!(
                self.tokens.get(cursor).map(|token| &token.kind),
                Some(TokenKind::Ident(_))
            ) {
                return false;
            }
            cursor += 1;
        }
        matches!(
            self.tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::FatArrow)
        )
    }

    fn braced_expression(&mut self, start: Span) -> Result<Expr, Diagnostic> {
        let closure = self.at(&TokenKind::FatArrow)
            || matches!(self.peek().kind, TokenKind::Ident(_))
                && (self.tokens.get(self.cursor + 1).is_some_and(|token| {
                    self.same_token(&token.kind, &TokenKind::FatArrow)
                        || self.same_token(&token.kind, &TokenKind::Comma)
                }));
        if !closure {
            self.cursor -= 1;
            return self.block();
        }
        let mut params: Vec<Rc<str>> = Vec::new();
        while !self.at(&TokenKind::FatArrow) {
            let (param, _) = self.ident("expected a closure parameter")?;
            params.push(Rc::from(param.as_str()));
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::FatArrow, "expected `=>` in this closure")?;
        let body = self.expression(0)?;
        let end = self
            .expect(TokenKind::RBrace, "expected `}` after the closure body")?
            .span;
        Ok(Expr {
            kind: ExprKind::Closure {
                params: Rc::from(params),
                body: Rc::new(body),
            },
            span: start.join(end),
        })
    }

    fn handle(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.bump().span;
        let computation = self.expression(0)?;
        self.expect(TokenKind::LBrace, "expected `{` and handler clauses")?;
        let mut clauses = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            let clause_start = self.peek().span;
            let (effect, _) = self.ident("expected an effect name in this handler clause")?;
            self.expect(
                TokenKind::DoubleColon,
                "expected `::` in the handler clause",
            )?;
            let (operation, _) = self.ident("expected an operation name in the handler clause")?;
            self.expect(TokenKind::LParen, "expected `(` before handler patterns")?;
            let mut patterns = Vec::new();
            while !self.at(&TokenKind::RParen) {
                patterns.push(self.pattern()?);
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(TokenKind::RParen, "expected `)` after handler patterns")?;
            let resumption = if self.at_ident("with") {
                self.bump();
                Some(self.ident("expected a resumption binding after `with`")?.0)
            } else {
                None
            };
            self.expect(TokenKind::FatArrow, "expected `=>` before the handler body")?;
            let body = self.expression(0)?;
            let span = clause_start.join(body.span);
            clauses.push(HandlerClause {
                effect,
                operation,
                patterns,
                resumption,
                body,
                span,
            });
            self.eat(&TokenKind::Comma);
            self.eat(&TokenKind::Semicolon);
        }
        let end = self
            .expect(TokenKind::RBrace, "expected `}` after handler clauses")?
            .span;
        Ok(Expr {
            kind: ExprKind::Handle {
                computation: Rc::new(computation),
                clauses: Rc::new(clauses),
            },
            span: start.join(end),
        })
    }

    fn pattern(&mut self) -> Result<Pattern, Diagnostic> {
        let token = self.bump().clone();
        let mut pattern = match token.kind {
            TokenKind::Ident(name) if name == "_" => Pattern {
                kind: PatternKind::Wildcard,
                span: token.span,
            },
            TokenKind::Ident(name) => {
                let mut path = vec![name];
                let mut end = token.span;
                while self.eat(&TokenKind::DoubleColon) {
                    let (part, span) = self.ident("expected a variant name after `::`")?;
                    path.push(part);
                    end = span;
                }
                if path.len() == 1 {
                    Pattern {
                        kind: PatternKind::Binding(path.remove(0)),
                        span: token.span,
                    }
                } else {
                    Pattern {
                        kind: PatternKind::Variant {
                            path,
                            fields: Vec::new(),
                        },
                        span: token.span.join(end),
                    }
                }
            }
            TokenKind::Int(value) => Pattern {
                kind: PatternKind::Int(value),
                span: token.span,
            },
            TokenKind::String(value) => Pattern {
                kind: PatternKind::String(value),
                span: token.span,
            },
            TokenKind::LParen if self.eat(&TokenKind::RParen) => Pattern {
                kind: PatternKind::Unit,
                span: token.span.join(self.previous().span),
            },
            _ => {
                return Err(Diagnostic::error(
                    "expected a pattern",
                    "handler clauses accept literals, bindings, `_`, and enum variants",
                    token.span,
                ));
            }
        };
        if matches!(pattern.kind, PatternKind::Variant { .. }) && self.eat(&TokenKind::LParen) {
            let mut fields = Vec::new();
            while !self.at(&TokenKind::RParen) {
                fields.push(self.pattern()?);
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            let end = self
                .expect(TokenKind::RParen, "expected `)` after variant patterns")?
                .span;
            let PatternKind::Variant { path, .. } = pattern.kind else {
                unreachable!()
            };
            pattern = Pattern {
                kind: PatternKind::Variant { path, fields },
                span: pattern.span.join(end),
            };
        }
        Ok(pattern)
    }

    fn perform(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.bump().span;
        let (effect, _) = self.ident("expected an effect name after `perform`")?;
        self.expect(
            TokenKind::DoubleColon,
            "expected `::` between the effect and operation",
        )?;
        let (operation, _) = self.ident("expected an operation name")?;
        self.expect(TokenKind::LParen, "expected `(` after the operation")?;
        let mut args = Vec::new();
        while !self.at(&TokenKind::RParen) {
            args.push(self.expression(0)?);
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        let end = self
            .expect(TokenKind::RParen, "expected `)` after operation arguments")?
            .span;
        Ok(Expr {
            kind: ExprKind::Perform {
                effect: effect.into(),
                operation: operation.into(),
                args: Rc::new(args),
            },
            span: start.join(end),
        })
    }

    fn binary_op(&self) -> Option<(BinaryOp, u8)> {
        Some(match self.peek().kind {
            TokenKind::EqEq => (BinaryOp::Eq, 20),
            TokenKind::BangEq => (BinaryOp::NotEq, 20),
            TokenKind::Lt => (BinaryOp::Lt, 20),
            TokenKind::LtEq => (BinaryOp::LtEq, 20),
            TokenKind::Gt => (BinaryOp::Gt, 20),
            TokenKind::GtEq => (BinaryOp::GtEq, 20),
            TokenKind::Plus => (BinaryOp::Add, 30),
            TokenKind::Minus => (BinaryOp::Sub, 30),
            TokenKind::Star => (BinaryOp::Mul, 40),
            TokenKind::Slash => (BinaryOp::Div, 40),
            _ => return None,
        })
    }

    fn word_infix(&self) -> Option<(String, Associativity, u8, Span)> {
        let TokenKind::Ident(name) = &self.peek().kind else {
            return None;
        };
        let (FixityKind::Infix(associativity), precedence) = self.fixities.get(name).copied()?
        else {
            return None;
        };
        Some((name.clone(), associativity, precedence, self.peek().span))
    }

    fn type_syntax(&mut self) -> Result<TypeSyntax, Diagnostic> {
        let mut ty = if self.at(&TokenKind::Lt) {
            let start = self.bump().span;
            let subject = self.type_syntax()?;
            self.expect_ident("as", "expected `as` in a fully qualified projection")?;
            let trait_ref = self.trait_ref()?;
            self.expect(
                TokenKind::Gt,
                "expected `>` after the projection trait reference",
            )?;
            self.expect(
                TokenKind::DoubleColon,
                "expected `::` before the associated type name",
            )?;
            let (name, span) = self.ident("expected an associated type name")?;
            let arguments = self.type_argument_list()?;
            TypeSyntax {
                span: start.join(
                    arguments
                        .last()
                        .map_or(span, AssociatedArgumentSyntax::span),
                ),
                kind: TypeSyntaxKind::Projection {
                    subject: Box::new(subject),
                    trait_ref,
                    item: TypePathSegment { name, span },
                    arguments,
                },
            }
        } else if self.at(&TokenKind::Amp) {
            let start = self.bump().span;
            let lifetime = if let TokenKind::Lifetime(name) = &self.peek().kind {
                Some(LifetimeSyntax {
                    name: name.clone(),
                    span: self.bump().span,
                })
            } else {
                None
            };
            let unique = self.at_ident("mut");
            if unique {
                self.bump();
            }
            let referent = self.type_syntax()?;
            let ty = TypeSyntax {
                span: start.join(referent.span),
                kind: if unique {
                    TypeSyntaxKind::UniqueReference(Box::new(referent))
                } else {
                    TypeSyntaxKind::SharedReference(Box::new(referent))
                },
            };
            if let Some(lifetime) = lifetime {
                self.reference_lifetimes.push(ReferenceLifetimeSyntax {
                    reference: ty.span,
                    lifetime,
                });
            }
            ty
        } else if self.at(&TokenKind::LParen) {
            let start = self.bump().span;
            if self.eat(&TokenKind::RParen) {
                return Ok(TypeSyntax {
                    kind: TypeSyntaxKind::Tuple(vec![]),
                    span: start.join(self.previous().span),
                });
            }
            let first = self.type_syntax()?;
            if !self.eat(&TokenKind::Comma) {
                let end = self
                    .expect(TokenKind::RParen, "expected `)` to close the grouped type")?
                    .span;
                return Ok(TypeSyntax {
                    kind: first.kind,
                    span: start.join(end),
                });
            }
            let mut elements = vec![first];
            while !self.at(&TokenKind::RParen) {
                elements.push(self.type_syntax()?);
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            let end = self
                .expect(TokenKind::RParen, "expected `)` to close the tuple type")?
                .span;
            TypeSyntax {
                kind: TypeSyntaxKind::Tuple(elements),
                span: start.join(end),
            }
        } else if self.at(&TokenKind::Bang) {
            let span = self.bump().span;
            TypeSyntax {
                kind: TypeSyntaxKind::Never,
                span,
            }
        } else {
            let (name, span) = self.ident("expected a path, reference, or tuple type")?;
            let mut segments = vec![TypePathSegment { name, span }];
            while self.eat(&TokenKind::DoubleColon) {
                let (name, span) = self.ident("expected a path segment after `::`")?;
                segments.push(TypePathSegment { name, span });
            }
            let span = segments
                .first()
                .expect("a type path has a segment")
                .span
                .join(segments.last().expect("a type path has a segment").span);
            TypeSyntax {
                kind: TypeSyntaxKind::Path(segments),
                span,
            }
        };

        if self.eat(&TokenKind::Lt) {
            let mut arguments = Vec::new();
            if self.at(&TokenKind::Gt) {
                return Err(self.error(
                    "empty generic application",
                    "expected at least one type argument between `<` and `>`",
                ));
            }
            loop {
                arguments.push(self.type_syntax()?);
                if !self.eat(&TokenKind::Comma) || self.at(&TokenKind::Gt) {
                    break;
                }
            }
            let end = self
                .expect(TokenKind::Gt, "expected `>` after generic type arguments")?
                .span;
            ty = TypeSyntax {
                span: ty.span.join(end),
                kind: TypeSyntaxKind::Application {
                    constructor: Box::new(ty),
                    arguments,
                },
            };
        }
        Ok(ty)
    }

    fn type_argument_list(&mut self) -> Result<Vec<AssociatedArgumentSyntax>, Diagnostic> {
        if !self.eat(&TokenKind::Lt) {
            return Ok(vec![]);
        }
        if self.at(&TokenKind::Gt) {
            return Err(self.error(
                "empty associated type arguments",
                "expected at least one associated type argument",
            ));
        }
        let mut arguments = Vec::new();
        loop {
            if matches!(self.peek().kind, TokenKind::Int(_) | TokenKind::LBracket) {
                return Err(Diagnostic::error(
                    "unsupported const associated type argument",
                    "const associated type arguments are not yet supported by projection syntax",
                    self.peek().span,
                )
                .with_code("G1TR001"));
            }
            if let TokenKind::Lifetime(name) = &self.peek().kind {
                let name = name.clone();
                let span = self.bump().span;
                arguments.push(AssociatedArgumentSyntax::Lifetime { name, span });
            } else {
                arguments.push(AssociatedArgumentSyntax::Type(self.type_syntax()?));
            }
            if !self.eat(&TokenKind::Comma) || self.at(&TokenKind::Gt) {
                break;
            }
        }
        self.expect(
            TokenKind::Gt,
            "expected `>` after associated type arguments",
        )?;
        Ok(arguments)
    }

    fn at_associated_binding(&self) -> bool {
        if !matches!(self.peek().kind, TokenKind::Ident(_)) {
            return false;
        }
        if self
            .tokens
            .get(self.cursor + 1)
            .is_some_and(|token| same_kind(&token.kind, &TokenKind::Eq))
        {
            return true;
        }
        if !self
            .tokens
            .get(self.cursor + 1)
            .is_some_and(|token| same_kind(&token.kind, &TokenKind::Lt))
        {
            return false;
        }
        let mut depth = 0usize;
        for (offset, token) in self.tokens.iter().enumerate().skip(self.cursor + 1) {
            if same_kind(&token.kind, &TokenKind::Lt) {
                depth += 1;
            } else if same_kind(&token.kind, &TokenKind::GtEq) && depth == 1 {
                return true;
            } else if same_kind(&token.kind, &TokenKind::Gt) {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return self
                        .tokens
                        .get(offset + 1)
                        .is_some_and(|next| same_kind(&next.kind, &TokenKind::Eq));
                }
            }
        }
        false
    }

    fn ident(&mut self, message: &str) -> Result<(String, Span), Diagnostic> {
        let token = self.bump().clone();
        match token.kind {
            TokenKind::Ident(name) => Ok((name, token.span)),
            _ => Err(Diagnostic::error("expected a name", message, token.span)),
        }
    }
    fn expect_ident(&mut self, expected: &str, message: &str) -> Result<Token, Diagnostic> {
        if self.at_ident(expected) {
            Ok(self.bump().clone())
        } else {
            Err(self.error("unexpected syntax", message))
        }
    }
    fn at_ident(&self, value: &str) -> bool {
        matches!(&self.peek().kind, TokenKind::Ident(name) if name == value)
    }
    fn at(&self, kind: &TokenKind) -> bool {
        same_kind(&self.peek().kind, kind)
    }
    fn same_token(&self, lhs: &TokenKind, rhs: &TokenKind) -> bool {
        same_kind(lhs, rhs)
    }
    fn eat(&mut self, kind: &TokenKind) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, kind: TokenKind, message: &str) -> Result<Token, Diagnostic> {
        if self.at(&kind) {
            Ok(self.bump().clone())
        } else {
            Err(self.error("unexpected syntax", message))
        }
    }
    fn error(&self, title: &str, message: &str) -> Diagnostic {
        Diagnostic::error(title, message, self.peek().span)
    }
    fn peek(&self) -> &Token {
        &self.tokens[self.cursor]
    }
    fn peek_n(&self, offset: usize) -> Option<&Token> {
        self.tokens.get(self.cursor + offset)
    }
    fn previous(&self) -> &Token {
        &self.tokens[self.cursor - 1]
    }
    fn bump(&mut self) -> &Token {
        let index = self.cursor;
        if !self.at(&TokenKind::Eof) {
            self.cursor += 1;
        }
        &self.tokens[index]
    }
}

fn same_kind(lhs: &TokenKind, rhs: &TokenKind) -> bool {
    discriminant(lhs) == discriminant(rhs)
}

fn collect_fixities(tokens: &[Token]) -> Result<HashMap<String, (FixityKind, u8)>, Diagnostic> {
    let mut fixities = HashMap::new();
    let mut cursor = 0;
    while cursor < tokens.len() {
        let TokenKind::Ident(keyword) = &tokens[cursor].kind else {
            cursor += 1;
            continue;
        };
        let kind = match keyword.as_str() {
            "infixl" => FixityKind::Infix(Associativity::Left),
            "infixr" => FixityKind::Infix(Associativity::Right),
            "prefix" => FixityKind::Prefix,
            _ => {
                cursor += 1;
                continue;
            }
        };
        let Some(Token {
            kind: TokenKind::Int(precedence),
            span: precedence_span,
        }) = tokens.get(cursor + 1)
        else {
            cursor += 1;
            continue;
        };
        let Some(Token {
            kind: TokenKind::Ident(name),
            span: name_span,
        }) = tokens.get(cursor + 2)
        else {
            cursor += 1;
            continue;
        };
        let terminator = cursor + 3;
        if !tokens
            .get(terminator)
            .is_some_and(|token| matches!(token.kind, TokenKind::Semicolon))
        {
            cursor += 1;
            continue;
        }
        let precedence = u8::try_from(*precedence).map_err(|_| {
            Diagnostic::error(
                "invalid operator precedence",
                "operator precedence must be from 0 through 255",
                *precedence_span,
            )
        })?;
        if fixities.insert(name.clone(), (kind, precedence)).is_some() {
            return Err(Diagnostic::error(
                "operator fixity declared more than once",
                format!("`{name}` has multiple fixity declarations"),
                *name_span,
            ));
        }
        cursor = terminator + 1;
    }
    Ok(fixities)
}
