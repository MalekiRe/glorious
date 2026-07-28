use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    mem::discriminant,
    rc::Rc,
};

use crate::{
    ast::{
        AssignmentField, AssignmentPlace, AssignmentPlaceKind, AssociatedArgumentSyntax,
        AssociatedBinding, AssociatedBindingValue, AssociatedItemSyntaxKind, AssociatedTypeDecl,
        AssociatedTypeDefinition, Associativity, BinaryOp, ConstArgumentValueSyntax,
        ConstAssociatedArgumentSyntax, ConstBinaryOp, ConstExprSyntax, ConstExprSyntaxKind,
        ConstKind, DeconstructField, DropDecl, EffectDecl, EffectOperationDecl, EffectPathSyntax,
        EffectRowAliasDecl, EffectRowSyntax, EnumDecl, Expr, ExprKind, FieldDecl, FieldVisibility,
        FixityDecl, FixityKind, Function, GenericParam, GenericParamKind, GenericParams,
        GlobalBinding, GoalArgument, GoalPolarity, HandlerClause, ImplDecl, ImportDecl, ImportTree,
        ItemVisibility, LabelSyntax, LifetimeOutlivesSyntax, LifetimeSyntax, ModuleDecl,
        ModuleKind, Param, Pattern, PatternKind, PatternRest, Program, QuantitySyntax, Stmt,
        StructDecl, StructFieldPattern, TraitDecl, TraitMethod, TraitRefSyntax, TypeAliasDecl,
        TypePathSegment, TypeSyntax, TypeSyntaxKind, UnaryOp, UseDecl, VariantDecl, Visibility,
        WhereClause, WhereGoal,
    },
    diagnostic::Diagnostic,
    lexer::{Kw, Token, TokenKind},
    span::Span,
};

/// Parses a complete program, stopping at the first diagnostic.
pub fn parse(tokens: Vec<Token>) -> Result<Program, Diagnostic> {
    let (program, mut diagnostics) = parse_recovering(tokens);
    if diagnostics.is_empty() {
        Ok(program)
    } else {
        Err(diagnostics.remove(0))
    }
}

/// Parses a complete program, recovering at declaration boundaries so every
/// malformed declaration produces its own structured diagnostic. Recovered
/// declarations are excluded from the returned [`Program`] and never enter
/// interface tables. Recovery always advances, so parsing terminates on every
/// token stream.
pub fn parse_recovering(tokens: Vec<Token>) -> (Program, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();
    let fixities = collect_fixities(&tokens, &mut diagnostics);
    Parser {
        tokens,
        cursor: 0,
        fixities,
        fixity_regions: Vec::new(),
        effect_paths: Vec::new(),
        type_const_arguments: Vec::new(),
        fixed_array_types: Vec::new(),
        numeric_literals: Vec::new(),
        handling_scrutinee: false,
        in_whitespace_argument: false,
    }
    .program(diagnostics)
}

#[derive(Clone, Copy, Debug)]
pub struct ScopedFixity {
    pub kind: FixityKind,
    pub precedence: u8,
    pub declaration: Option<Span>,
}

#[derive(Clone, Debug)]
pub struct FixityRegion {
    pub span: Span,
    pub fixities: HashMap<String, ScopedFixity>,
}

pub fn parse_recovering_with_fixity_regions(
    tokens: Vec<Token>,
    fixity_regions: Vec<FixityRegion>,
) -> (Program, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();
    let fixities = collect_fixities(&tokens, &mut diagnostics);
    Parser {
        tokens,
        cursor: 0,
        fixities,
        fixity_regions,
        effect_paths: Vec::new(),
        type_const_arguments: Vec::new(),
        fixed_array_types: Vec::new(),
        numeric_literals: Vec::new(),
        handling_scrutinee: false,
        in_whitespace_argument: false,
    }
    .program(diagnostics)
}

/// One operator's authority: its fixity, precedence, and the declaration that
/// introduced it.
#[derive(Clone, Copy, Debug)]
struct FixityEntry {
    kind: FixityKind,
    precedence: u8,
    declaration: Option<Span>,
}

/// The spellings the current lowering recognizes as its comparison and
/// arithmetic contract. This is a representation choice for downstream
/// consumers, not operator policy: grouping authority always comes from the
/// fixity table.
fn lowered_binary(spelling: &str) -> Option<BinaryOp> {
    Some(match spelling {
        "==" => BinaryOp::Eq,
        "!=" => BinaryOp::NotEq,
        "<" => BinaryOp::Lt,
        "<=" => BinaryOp::LtEq,
        ">" => BinaryOp::Gt,
        ">=" => BinaryOp::GtEq,
        "+" => BinaryOp::Add,
        "-" => BinaryOp::Sub,
        "*" => BinaryOp::Mul,
        "/" => BinaryOp::Div,
        "%" => BinaryOp::Rem,
        _ => return None,
    })
}

/// The spelling a token contributes to a flat operator run in operator
/// position. Structural punctuation that never participates in an operator
/// spelling (`.` projection, `..`, `->`, `=>`, `::`) is absent.
fn operator_token_spelling(kind: &TokenKind) -> Option<&str> {
    Some(match kind {
        TokenKind::Plus => "+",
        TokenKind::Minus => "-",
        TokenKind::Star => "*",
        TokenKind::Slash => "/",
        TokenKind::Percent => "%",
        TokenKind::EqEq => "==",
        TokenKind::BangEq => "!=",
        TokenKind::Lt => "<",
        TokenKind::LtEq => "<=",
        TokenKind::Gt => ">",
        TokenKind::GtEq => ">=",
        TokenKind::Amp => "&",
        TokenKind::Bang => "!",
        TokenKind::Pipe => "|",
        TokenKind::Eq => "=",
        TokenKind::Operator(spelling) => spelling,
        _ => return None,
    })
}

/// One infix operator occurrence inside a flat operator sequence: prefix
/// tokens, first operand, then ordered (infix, operand) pairs. Grouping is
/// performed against the complete declared-fixity table after collection.
#[derive(Clone, Debug)]
struct InfixOccurrence {
    spelling: String,
    span: Span,
    token_count: usize,
    is_word: bool,
    associativity: Associativity,
    precedence: u8,
    declaration: Option<Span>,
}

/// Joins the maximal sequence of span-adjacent operator tokens starting at
/// `start` into one flat operator spelling. A word operator is a single
/// identifier token. Returns the spelling, its complete span, and the number
/// of tokens consumed.
fn joined_operator_name(tokens: &[Token], start: usize) -> Option<(String, Span, usize)> {
    match tokens.get(start).map(|token| &token.kind) {
        Some(TokenKind::Ident(name)) => {
            let name = name.clone();
            Some((name, tokens[start].span, 1))
        }
        _ => {
            let mut spelling = String::new();
            let mut span: Option<Span> = None;
            let mut count = 0usize;
            while let Some(token) = tokens.get(start + count) {
                let Some(part) = operator_token_spelling(&token.kind) else {
                    break;
                };
                if let Some(current) = span
                    && current.end != token.span.start
                {
                    break;
                }
                spelling.push_str(part);
                span = Some(span.map_or(token.span, |current| current.join(token.span)));
                count += 1;
            }
            span.map(|span| (spelling, span, count))
        }
    }
}

/// The program declarations accumulated so far. A declaration is pushed only
/// after it parses completely, so parse recovery cannot leak partial
/// declarations into these interface tables.
#[derive(Default)]
struct ProgramDraft {
    modules: Vec<ModuleDecl>,
    imports: Vec<ImportDecl>,
    item_visibilities: Vec<ItemVisibility>,
    type_aliases: Vec<TypeAliasDecl>,
    effect_row_aliases: Vec<EffectRowAliasDecl>,
    globals: Vec<GlobalBinding>,
    fixities: Vec<FixityDecl>,
    structs: Vec<StructDecl>,
    enums: Vec<EnumDecl>,
    traits: Vec<TraitDecl>,
    impls: Vec<ImplDecl>,
    uses: Vec<UseDecl>,
    effects: Vec<EffectDecl>,
    drops: Vec<DropDecl>,
    functions: Vec<Function>,
}

struct Parser {
    tokens: Vec<Token>,
    cursor: usize,
    fixities: HashMap<String, FixityEntry>,
    fixity_regions: Vec<FixityRegion>,
    effect_paths: Vec<EffectPathSyntax>,
    type_const_arguments: Vec<crate::ast::TypeConstApplicationSyntax>,
    fixed_array_types: Vec<crate::ast::FixedArrayTypeSyntax>,
    numeric_literals: Vec<crate::ast::NumericLiteralSyntax>,
    handling_scrutinee: bool,
    /// Whitespace application may not recursively consume another whitespace
    /// application. Nested calls use the explicit `callee(...)` form.
    in_whitespace_argument: bool,
}

impl Parser {
    fn fixity(&self, name: &str, span: Span) -> Option<FixityEntry> {
        let region = self
            .fixity_regions
            .iter()
            .filter(|region| region.span.start <= span.start && span.end <= region.span.end)
            .min_by_key(|region| region.span.end.saturating_sub(region.span.start));
        if let Some(region) = region {
            return region
                .fixities
                .get(name)
                .map(|entry| FixityEntry {
                    kind: entry.kind,
                    precedence: entry.precedence,
                    declaration: entry.declaration,
                })
                .or_else(|| {
                    self.fixities
                        .get(name)
                        .copied()
                        .filter(|entry| entry.declaration.is_none())
                });
        }
        self.fixities.get(name).copied()
    }
    fn program(mut self, mut diagnostics: Vec<Diagnostic>) -> (Program, Vec<Diagnostic>) {
        let mut draft = ProgramDraft::default();
        while !self.at(&TokenKind::Eof) {
            let declaration_start = self.cursor;
            if let Err(diagnostic) = self.declaration(&mut draft) {
                diagnostics.push(diagnostic);
                self.recover(declaration_start);
            }
        }
        let mut program = Program {
            modules: draft.modules,
            imports: draft.imports,
            item_visibilities: draft.item_visibilities,
            type_aliases: draft.type_aliases,
            effect_row_aliases: draft.effect_row_aliases,
            globals: draft.globals,
            fixities: draft.fixities,
            structs: draft.structs,
            enums: draft.enums,
            traits: draft.traits,
            impls: draft.impls,
            uses: draft.uses,
            effects: draft.effects,
            drops: draft.drops,
            functions: draft.functions,
            effect_paths: self.effect_paths,
            type_const_arguments: self.type_const_arguments,
            fixed_array_types: self.fixed_array_types,
            numeric_literals: self.numeric_literals,
        };
        diagnostics.extend(normalize_effect_surface(&mut program));
        (program, diagnostics)
    }

    fn declaration(&mut self, draft: &mut ProgramDraft) -> Result<(), Diagnostic> {
        let visibility = if self.at_ident("pub") {
            self.bump();
            Visibility::Public
        } else {
            Visibility::Private
        };
        let declaration_span = if self.at_ident("mod") {
            self.module_decl(draft, visibility)?
        } else if self.at_import_decl() {
            let declaration = self.import_decl(visibility)?;
            let span = declaration.span;
            draft.imports.push(declaration);
            span
        } else if self.at_kw(Kw::Type) {
            let declaration = self.type_alias()?;
            let span = declaration.span;
            draft.type_aliases.push(declaration);
            span
        } else if self.at_ident("cases") {
            let declaration = self.effect_row_alias()?;
            let span = declaration.span;
            draft.effect_row_aliases.push(declaration);
            span
        } else if self.at_kw(Kw::Let) {
            let declaration = self.global_binding()?;
            let span = declaration.span;
            draft.globals.push(declaration);
            span
        } else if self.at_fixity_decl() {
            let declaration = self.fixity_decl()?;
            let span = declaration.span;
            draft.fixities.push(declaration);
            span
        } else if self.at_kw(Kw::Effect) {
            let declaration = self.effect()?;
            let span = declaration.span;
            draft.effects.push(declaration);
            span
        } else if self.at_kw(Kw::Struct) {
            let declaration = self.struct_decl()?;
            let span = declaration.span;
            draft.structs.push(declaration);
            span
        } else if self.at_kw(Kw::Enum) {
            let declaration = self.enum_decl()?;
            let span = declaration.span;
            draft.enums.push(declaration);
            span
        } else if self.at_kw(Kw::Trait) {
            let declaration = self.trait_decl()?;
            let span = declaration.span;
            draft.traits.push(declaration);
            span
        } else if self.at_kw(Kw::Impl) {
            if self.at_drop_impl() {
                let declaration = self.drop_impl()?;
                let span = declaration.span;
                draft.drops.push(declaration);
                span
            } else if self.at_use_impl() {
                let declaration = self.use_impl()?;
                let span = declaration.span;
                draft.uses.push(declaration);
                span
            } else {
                let declaration = self.impl_decl()?;
                let span = declaration.span;
                draft.impls.push(declaration);
                span
            }
        } else {
            let declaration = self.function()?;
            let span = declaration.span;
            draft.functions.push(declaration);
            span
        };
        draft.item_visibilities.push(ItemVisibility {
            declaration: declaration_span,
            visibility,
        });
        Ok(())
    }

    fn at_import_decl(&self) -> bool {
        self.at_ident("use")
            && !matches!(
                self.peek_n(1).map(|token| &token.kind),
                Some(TokenKind::LParen | TokenKind::Lt)
            )
    }

    fn module_decl(
        &mut self,
        draft: &mut ProgramDraft,
        visibility: Visibility,
    ) -> Result<Span, Diagnostic> {
        let start = self.expect_ident("mod", "expected `mod`")?.span;
        let (name, name_span) = self.ident("expected a module name")?;
        if self.eat(&TokenKind::Semicolon) {
            let end = self.tokens[self.cursor - 1].span;
            let span = start.join(end);
            draft.modules.push(ModuleDecl {
                name,
                name_span,
                visibility,
                kind: ModuleKind::External,
                span,
            });
            return Ok(span);
        }
        let open = self
            .expect(
                TokenKind::LBrace,
                "expected `;` or `{` after the module name",
            )?
            .span;
        let module_index = draft.modules.len();
        draft.modules.push(ModuleDecl {
            name,
            name_span,
            visibility,
            kind: ModuleKind::Inline {
                body: Span::new(open.end, open.end),
            },
            span: start,
        });
        while !self.at(&TokenKind::RBrace) && !self.at(&TokenKind::Eof) {
            self.declaration(draft)?;
        }
        let close = self
            .expect(TokenKind::RBrace, "expected `}` after the inline module")?
            .span;
        let span = start.join(close);
        draft.modules[module_index].kind = ModuleKind::Inline {
            body: Span::new(open.end, close.start),
        };
        draft.modules[module_index].span = span;
        Ok(span)
    }

    fn import_decl(&mut self, visibility: Visibility) -> Result<ImportDecl, Diagnostic> {
        let start = self.expect_ident("use", "expected `use`")?.span;
        let tree = self.import_tree()?;
        let end = self
            .expect(
                TokenKind::Semicolon,
                "expected `;` after the use declaration",
            )?
            .span;
        Ok(ImportDecl {
            tree,
            visibility,
            span: start.join(end),
        })
    }

    fn import_tree(&mut self) -> Result<ImportTree, Diagnostic> {
        if self.at(&TokenKind::LBrace) {
            let open = self.bump().span;
            let (items, close) = self.collect_comma_delimited(
                TokenKind::RBrace,
                "expected `}` after grouped imports",
                Self::import_tree,
            )?;
            return Ok(ImportTree::Group {
                items,
                span: open.join(close),
            });
        }
        if self.at(&TokenKind::Star) {
            return Ok(ImportTree::Glob {
                span: self.bump().span,
            });
        }
        let (name, span) = self.ident("expected an import path, `self`, or `*`")?;
        let segment = TypePathSegment { name, span };
        if self.eat(&TokenKind::DoubleColon) {
            return Ok(ImportTree::Path {
                segment,
                tree: Box::new(self.import_tree()?),
            });
        }
        let alias = if self.at_ident("as") {
            self.bump();
            let (name, span) = self.ident("expected an import alias after `as`")?;
            Some(TypePathSegment { name, span })
        } else {
            None
        };
        if segment.name == "self" {
            Ok(ImportTree::SelfValue {
                span: segment.span,
                alias,
            })
        } else {
            Ok(ImportTree::Name {
                name: segment,
                alias,
            })
        }
    }

    /// The fixity words stay contextual so ordinary bindings may be named
    /// `prefix` or `infix`: a fixity declaration is the word followed by its
    /// integer precedence.
    fn at_fixity_decl(&self) -> bool {
        (self.at_ident("infixl")
            || self.at_ident("infixr")
            || self.at_ident("infix")
            || self.at_ident("prefix"))
            && matches!(
                self.peek_n(1).map(|token| &token.kind),
                Some(TokenKind::Number(_))
            )
    }

    fn at_declaration_start(&self) -> bool {
        matches!(
            self.peek().kind,
            TokenKind::Keyword(
                Kw::Type | Kw::Let | Kw::Effect | Kw::Struct | Kw::Enum | Kw::Trait | Kw::Impl
            )
        ) || self.at_ident("cases")
            || self.at_ident("mod")
            || self.at_import_decl()
            || self.at_ident("pub")
            || (matches!(self.peek().kind, TokenKind::Ident(_))
                && matches!(
                    self.peek_n(1).map(|token| &token.kind),
                    Some(TokenKind::LParen | TokenKind::Lt)
                ))
            || self.at_fixity_decl()
    }

    /// Skips past a malformed declaration. The cursor tracks bracket depth and
    /// stops after a top-level `;`, after the `}` that closes the declaration
    /// body, or before the next declaration keyword. At least one token is
    /// always consumed, so recovery cannot loop.
    fn recover(&mut self, declaration_start: usize) {
        if self.cursor <= declaration_start && !self.at(&TokenKind::Eof) {
            self.cursor += 1;
        }
        let mut depth = 0usize;
        while !self.at(&TokenKind::Eof) {
            match &self.peek().kind {
                TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket => {
                    depth += 1;
                    self.cursor += 1;
                }
                TokenKind::RBrace if depth <= 1 => {
                    self.cursor += 1;
                    return;
                }
                TokenKind::RBrace | TokenKind::RParen | TokenKind::RBracket => {
                    depth = depth.saturating_sub(1);
                    self.cursor += 1;
                }
                TokenKind::Semicolon if depth == 0 => {
                    self.cursor += 1;
                    return;
                }
                _ if depth == 0 && self.at_declaration_start() => return,
                _ => self.cursor += 1,
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
        let mut methods = Vec::new();
        let mut names = std::collections::HashSet::new();
        while !self.at(&TokenKind::RBrace) {
            if !self.at_kw(Kw::Type) {
                let method = self.trait_method(false)?;
                if !names.insert(method.name.clone()) {
                    return Err(Diagnostic::error(
                        "duplicate trait item",
                        format!("trait item `{}` is declared more than once", method.name),
                        method.span,
                    ));
                }
                methods.push(method);
                continue;
            }
            let item_start = self
                .expect_kw(Kw::Type, "traits may declare only associated types")?
                .span;
            let (item_name, name_span) = self.ident("expected an associated type name")?;
            let generics = self.generic_params()?;
            if self.at(&TokenKind::Eq) {
                return Err(self.error(
                    "associated type default",
                    "associated type defaults are not supported",
                ));
            }
            let kind = if self.eat(&TokenKind::Colon) {
                self.expect_ident(
                    "EffectRow",
                    "expected `EffectRow` after `:` in an associated item declaration",
                )?;
                AssociatedItemSyntaxKind::EffectRow
            } else {
                AssociatedItemSyntaxKind::Type
            };
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
                kind,
                span: item_start.join(end),
            });
        }
        let end = self.bump().span;
        Ok(TraitDecl {
            name,
            generics,
            supertraits,
            associated_types,
            methods,
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
        let mut methods = Vec::new();
        let mut names = std::collections::HashSet::new();
        while !self.at(&TokenKind::RBrace) {
            if !self.at_kw(Kw::Type) {
                let method = self.trait_method(true)?;
                if !names.insert(method.name.clone()) {
                    return Err(Diagnostic::error(
                        "duplicate implementation item",
                        format!(
                            "implementation item `{}` is defined more than once",
                            method.name
                        ),
                        method.span,
                    ));
                }
                methods.push(method);
                continue;
            }
            let item_start = self
                .expect_kw(
                    Kw::Type,
                    "trait implementations may define only associated types",
                )?
                .span;
            let (item_name, name_span) = self.ident("expected an associated type name")?;
            let generics = self.generic_params()?;
            self.expect(
                TokenKind::Eq,
                "expected `=` in the associated type definition",
            )?;
            let value = if self.at(&TokenKind::LBrace) {
                AssociatedBindingValue::EffectRow(self.effect_row()?)
            } else {
                AssociatedBindingValue::Type(self.type_syntax()?)
            };
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
            methods,
            span: start.join(end),
        })
    }

    fn trait_method(&mut self, with_body: bool) -> Result<TraitMethod, Diagnostic> {
        let (name, start) = self.method_name("expected a trait method name")?;
        let generics = self.generic_params()?;
        self.expect(TokenKind::LParen, "expected `(` after the method name")?;
        let (params, _) = self.collect_comma_delimited(
            TokenKind::RParen,
            "expected `)` after method parameters",
            |parser| parser.typed_parameter("expected a method parameter name"),
        )?;
        let has_arrow = self.eat(&TokenKind::Arrow);
        let return_type = if !has_arrow
            || self.at(&TokenKind::LBrace)
            || self.at(&TokenKind::Slash)
            || self.at(&TokenKind::Semicolon)
        {
            None
        } else {
            Some(self.type_syntax()?)
        };
        let outward_effects = self
            .eat(&TokenKind::Slash)
            .then(|| self.effect_row())
            .transpose()?;
        let where_clause = self.where_clause()?;
        let (body, end) = if with_body {
            let body = self.block()?;
            let end = body.span;
            (Some(body), end)
        } else {
            let end = self
                .expect(
                    TokenKind::Semicolon,
                    "expected `;` after the trait method signature",
                )?
                .span;
            (None, end)
        };
        Ok(TraitMethod {
            name,
            generics,
            params,
            return_type,
            outward_effects,
            where_clause,
            body,
            span: start.join(end),
        })
    }

    fn use_impl(&mut self) -> Result<UseDecl, Diagnostic> {
        let start = self.bump().span;
        let generics = self.generic_params()?;
        self.reject_const_params(&generics, "dedicated Use implementations")?;
        let trait_ref = self.trait_ref()?;
        let [crate::ast::GoalArgument::Quantity(quantity)] = trait_ref.arguments.as_slice() else {
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
            TokenKind::Ident(name) if name == "infix" => FixityKind::Infix(Associativity::None),
            TokenKind::Ident(name) if name == "prefix" => FixityKind::Prefix,
            _ => unreachable!(),
        };
        let precedence_token = self.bump().clone();
        let TokenKind::Number(precedence) = &precedence_token.kind else {
            return Err(Diagnostic::error(
                "expected operator precedence",
                "fixity declarations use an integer from 0 through 255",
                precedence_token.span,
            ));
        };
        let precedence = u8::try_from(precedence.as_i64(precedence_token.span)?).map_err(|_| {
            Diagnostic::error(
                "invalid operator precedence",
                "operator precedence must be from 0 through 255",
                precedence_token.span,
            )
        })?;
        let Some((name, _, count)) = joined_operator_name(&self.tokens, self.cursor) else {
            return Err(self.error("expected an operator", "expected an operator name"));
        };
        self.cursor += count;
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
        let generic_span = generics.as_ref().map(|generics| generics.span);
        self.expect(TokenKind::LBrace, "expected `{` after the enum name")?;
        let mut variants = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            let (variant, variant_span) = self.ident("expected a variant name")?;
            let fields = if self.eat(&TokenKind::LParen) {
                self.collect_comma_delimited(
                    TokenKind::RParen,
                    "expected `)` after variant fields",
                    Self::type_syntax,
                )?
                .0
            } else {
                Vec::new()
            };
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
        let generic_span = generics.as_ref().map(|generics| generics.span);
        let where_clause = self.where_clause()?;
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
                            kind: TokenKind::Number(literal),
                            span,
                        } if !literal.is_float() => literal.as_i64(span)? as usize,
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
                            kind: TokenKind::Number(literal),
                            span,
                        } if !literal.is_float() => Some(literal.as_i64(span)? as usize),
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
            let operation_generics = self.generic_params()?;
            self.expect(TokenKind::LParen, "expected `(` after the operation name")?;
            let (params, _) = self.collect_comma_delimited(
                TokenKind::RParen,
                "expected `)` after operation parameters",
                |parser| parser.typed_parameter("expected an operation parameter name"),
            )?;
            let has_arrow = self.eat(&TokenKind::Arrow);
            let terminal = has_arrow && self.at(&TokenKind::Bang);
            let return_type =
                if !has_arrow || self.at(&TokenKind::Semicolon) || self.at(&TokenKind::RBrace) {
                    None
                } else {
                    Some(self.type_syntax()?)
                };
            let operation_where_clause = self.where_clause()?;
            operations.push(EffectOperationDecl {
                name: operation,
                generics: operation_generics,
                where_clause: operation_where_clause,
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
            where_clause,
            operations,
            span: start.join(end),
        })
    }

    fn function(&mut self) -> Result<Function, Diagnostic> {
        let (name, name_span) = self.ident("expected a callable declaration")?;
        let generics = self.generic_params()?;
        self.expect(TokenKind::LParen, "expected `(` after the callable name")?;
        let (params, _) = self.collect_comma_delimited(
            TokenKind::RParen,
            "expected `)` after parameters",
            |parser| parser.typed_parameter("expected a parameter name"),
        )?;
        let has_arrow = self.eat(&TokenKind::Arrow);
        let return_type = if !has_arrow || self.at(&TokenKind::LBrace) || self.at(&TokenKind::Slash)
        {
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
            let (name, mut span, kind) = if let TokenKind::Lifetime(name) = &self.peek().kind {
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
            let const_default = if self.eat(&TokenKind::Eq) {
                if !matches!(kind, GenericParamKind::Const(_)) {
                    return Err(Diagnostic::error(
                        "unsupported generic default",
                        "only const generic parameters may currently declare defaults",
                        self.previous().span,
                    ));
                }
                let default = self.const_expression()?;
                span = span.join(default.span);
                Some(default)
            } else {
                None
            };
            if !names.insert(name.clone()) {
                return Err(Diagnostic::error(
                    "duplicate generic parameter",
                    format!("`{name}` is bound more than once"),
                    span,
                ));
            }
            params.push(GenericParam {
                name,
                kind,
                const_default,
                span,
            });
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
        if !self.at(&TokenKind::LBrace) {
            let effect = self.type_syntax()?;
            return Ok(EffectRowSyntax {
                span: effect.span,
                effects: vec![effect],
                tail: None,
            });
        }
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
        if !self.at_kw(Kw::Where) {
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
                parameters.params
            } else {
                vec![]
            };
            if let TokenKind::Lifetime(name) = &self.peek().kind {
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
                    higher_ranked_lifetimes,
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
        let mut binding_keys = Vec::<(
            String,
            Vec<AssociatedArgumentSyntax>,
            Vec<ConstAssociatedArgumentSyntax>,
        )>::new();
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
                    let (arguments, const_arguments) = self.type_argument_list()?;
                    self.expect(TokenKind::Eq, "expected `=` in associated binding")?;
                    if binding_keys
                        .iter()
                        .any(|(name, existing, existing_consts)| {
                            name == &binding
                                && existing == &arguments
                                && existing_consts == &const_arguments
                        })
                    {
                        return Err(Diagnostic::error(
                            "duplicate associated binding",
                            format!(
                                "`{binding}` with the same arguments is assigned more than once"
                            ),
                            binding_span,
                        ));
                    }
                    binding_keys.push((
                        binding.clone(),
                        arguments.clone(),
                        const_arguments.clone(),
                    ));
                    let value = if self.at(&TokenKind::LBrace) {
                        AssociatedBindingValue::EffectRow(self.effect_row()?)
                    } else {
                        AssociatedBindingValue::Type(self.type_syntax()?)
                    };
                    let value_span = value.span();
                    bindings.push(AssociatedBinding {
                        name: binding,
                        arguments,
                        const_arguments,
                        span: binding_span.join(value_span),
                        value,
                    });
                } else if let TokenKind::Lifetime(name) = &self.peek().kind {
                    let name = name.clone();
                    let span = self.bump().span;
                    arguments.push(GoalArgument::Lifetime { name, span });
                } else if self.at(&TokenKind::LBracket) {
                    arguments.push(GoalArgument::Quantity(self.quantity()?));
                } else if let TokenKind::Number(literal) = &self.peek().kind
                    && !literal.is_float()
                {
                    let literal = literal.clone();
                    let span = self.bump().span;
                    arguments.push(GoalArgument::U32 {
                        value: literal.as_u64(span)?,
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
                kind: TokenKind::Number(literal),
                span,
            } if !literal.is_float() => literal.as_u64(span)?,
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
                kind: TokenKind::Number(literal),
                span,
            } if !literal.is_float() => Some(literal.as_u64(span)?),
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
            if self.at_kw(Kw::Let) {
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
                let destination_or_expression = self.expression(0)?;
                if self.eat(&TokenKind::Eq) {
                    let destination = Self::assignment_place(destination_or_expression)?;
                    let value = self.expression(0)?;
                    let semicolon = self.expect(
                        TokenKind::Semicolon,
                        "expected `;` after assignment statement",
                    )?;
                    let span = destination.span.join(semicolon.span);
                    statements.push(Stmt::Assign {
                        destination,
                        value,
                        span,
                    });
                    continue;
                }
                statements.push(Stmt::Expr(destination_or_expression));
            }
            self.eat(&TokenKind::Semicolon);
        }
        let end = self.bump().span;
        Ok(Expr {
            kind: ExprKind::Block(Rc::new(statements)),
            span: start.join(end),
        })
    }

    fn assignment_place(expression: Expr) -> Result<AssignmentPlace, Diagnostic> {
        let span = expression.span;
        let mut fields = Vec::new();
        let mut base = expression;
        while let ExprKind::Field(subject, name) = base.kind {
            let field_span = Span::new(subject.span.end, base.span.end);
            fields.push(AssignmentField {
                name,
                span: field_span,
            });
            base = Rc::unwrap_or_clone(subject);
        }
        fields.reverse();
        let kind = match base.kind {
            ExprKind::Variable(path) if path.len() == 1 => AssignmentPlaceKind::Local {
                name: path[0].clone(),
                fields,
            },
            ExprKind::Unary {
                op: UnaryOp::Dereference,
                operand,
            } => AssignmentPlaceKind::Dereference {
                reference: operand,
                fields,
            },
            _ => {
                return Err(Diagnostic::error(
                    "invalid assignment destination",
                    "the left side of `=` must be a local, a static field of a local, or a static field reached through `*`",
                    span,
                ));
            }
        };
        Ok(AssignmentPlace { kind, span })
    }

    /// Parses one flat operator sequence — prefix operators and postfix forms
    /// are consumed inside [`Self::primary`]; this level retains the first
    /// operand and the ordered (infix, operand) pairs, then groups them by the
    /// declared fixity table. `min_precedence` bounds which infix operators are
    /// collected so prefix-operator operands keep their declared binding.
    fn expression(&mut self, min_precedence: u8) -> Result<Expr, Diagnostic> {
        let first = self.primary()?;
        let mut operands = vec![first];
        let mut operators = Vec::new();
        while let Some(operator) = self.peek_infix() {
            if operator.precedence < min_precedence {
                break;
            }
            if !operator.is_word {
                let left = operands.last().expect("an infix has a left operand");
                let right = self.tokens.get(self.cursor + operator.token_count);
                if left.span.end == operator.span.start
                    || right.is_none_or(|token| operator.span.end == token.span.start)
                {
                    break;
                }
            }
            for _ in 0..operator.token_count {
                self.bump();
            }
            operands.push(self.operand()?);
            operators.push(operator);
        }
        let mut expression = Self::group_operator_sequence(operands, operators)?;
        if min_precedence == 0 && self.at_kw(Kw::Is) {
            self.bump();
            let pattern = self.pattern()?;
            Self::reject_duplicate_binders(std::slice::from_ref(&pattern))?;
            let span = expression.span.join(pattern.span);
            expression = Expr {
                kind: ExprKind::Is {
                    subject: Rc::new(expression),
                    pattern: Rc::new(pattern),
                },
                span,
            };
            if self.at_kw(Kw::Is) {
                return Err(self.error(
                    "chained pattern test",
                    "`is` does not chain; parenthesize the inner test",
                ));
            }
        }
        Ok(expression)
    }

    /// An operand in operator position. A brace block here is contextual: the
    /// expected-type pass decides between an eager block and a fresh anonymous
    /// callable, so the parser records a [`ExprKind::ContextBlock`].
    fn operand(&mut self) -> Result<Expr, Diagnostic> {
        if self.at(&TokenKind::LBrace) {
            let start = self.bump().span;
            let mut expression = self.braced_expression(start)?;
            if let ExprKind::Block(statements) = &expression.kind {
                expression.kind = ExprKind::ContextBlock(statements.clone());
            }
            return Ok(expression);
        }
        self.primary()
    }

    /// The next infix operator occurrence, if any. A word operator is one
    /// identifier with declared infix fixity. A symbolic operator is an
    /// atomic maximal run of span-adjacent punctuation tokens — operators are
    /// ordinary library names, so `==-` is one spelling and needs whitespace
    /// to read as `== -`. An undeclared spelling is simply not an infix
    /// operator; the surrounding context reports the leftover tokens.
    fn peek_infix(&self) -> Option<InfixOccurrence> {
        if let TokenKind::Ident(name) = &self.peek().kind {
            let entry = self.fixity(name, self.peek().span)?;
            let FixityKind::Infix(associativity) = entry.kind else {
                return None;
            };
            return Some(InfixOccurrence {
                spelling: name.clone(),
                span: self.peek().span,
                token_count: 1,
                is_word: true,
                associativity,
                precedence: entry.precedence,
                declaration: entry.declaration,
            });
        }
        let (spelling, span, token_count) = joined_operator_name(&self.tokens, self.cursor)?;
        let entry = self.fixity(&spelling, span)?;
        let FixityKind::Infix(associativity) = entry.kind else {
            return None;
        };
        Some(InfixOccurrence {
            spelling,
            span,
            token_count,
            is_word: false,
            associativity,
            precedence: entry.precedence,
            declaration: entry.declaration,
        })
    }

    /// The next prefix operator occurrence: a word with declared prefix
    /// fixity, or an atomic span-adjacent punctuation spelling declared
    /// prefix. The structural `-`, `&`, `&mut`, and `*` operand forms are
    /// consumed before this is consulted.
    fn peek_prefix_operator(&self) -> Option<(String, Span, usize, u8)> {
        if let TokenKind::Ident(name) = &self.peek().kind {
            let entry = self.fixity(name, self.peek().span)?;
            if entry.kind != FixityKind::Prefix {
                return None;
            }
            return Some((name.clone(), self.peek().span, 1, entry.precedence));
        }
        let (spelling, span, count) = joined_operator_name(&self.tokens, self.cursor)?;
        let entry = self.fixity(&spelling, span)?;
        (entry.kind == FixityKind::Prefix).then_some((spelling, span, count, entry.precedence))
    }

    /// Groups a flat operator sequence with the declared fixity table. Equal
    /// precedence with mixed associativity and chained nonassociative
    /// operators are diagnosed with both declaration sites.
    fn group_operator_sequence(
        operands: Vec<Expr>,
        operators: Vec<InfixOccurrence>,
    ) -> Result<Expr, Diagnostic> {
        fn reduce(output: &mut Vec<Expr>, operator: &InfixOccurrence) {
            let rhs = output
                .pop()
                .expect("grouping keeps one operand per operator");
            let lhs = output
                .pop()
                .expect("grouping keeps one operand per operator");
            let span = lhs.span.join(rhs.span);
            let kind = match operator.spelling.as_str() {
                "+" | "==" | "<" | ">" => ExprKind::Call(
                    Rc::new(Expr {
                        kind: ExprKind::Variable(Rc::from([
                            Rc::from(match operator.spelling.as_str() {
                                "+" => "Add",
                                "==" => "Equal",
                                "<" => "Less",
                                ">" => "Greater",
                                _ => unreachable!(),
                            }),
                            Rc::from(operator.spelling.as_str()),
                        ])),
                        span: operator.span,
                    }),
                    Rc::new(vec![lhs, rhs]),
                ),
                _ => match lowered_binary(&operator.spelling) {
                    Some(op) if !operator.is_word => ExprKind::Binary {
                        op,
                        lhs: Rc::new(lhs),
                        rhs: Rc::new(rhs),
                    },
                    _ => ExprKind::Call(
                        Rc::new(Expr {
                            kind: ExprKind::Variable(Rc::from([Rc::from(
                                operator.spelling.as_str(),
                            )])),
                            span: operator.span,
                        }),
                        Rc::new(vec![lhs, rhs]),
                    ),
                },
            };
            output.push(Expr { kind, span });
        }

        fn conflict(
            title: &str,
            message: String,
            left: &InfixOccurrence,
            right: &InfixOccurrence,
        ) -> Diagnostic {
            let mut diagnostic = Diagnostic::error(title, message, right.span);
            for operator in [left, right] {
                if let Some(declaration) = operator.declaration {
                    diagnostic = diagnostic.with_related(
                        declaration,
                        format!("`{}` is declared here", operator.spelling),
                    );
                } else {
                    diagnostic = diagnostic
                        .with_note(format!("`{}` is a built-in operator", operator.spelling));
                }
            }
            diagnostic
        }

        let mut operands = operands.into_iter();
        let mut output = vec![operands.next().expect("a sequence has a first operand")];
        let mut pending: Vec<InfixOccurrence> = Vec::new();
        for operator in operators {
            let operand = operands.next().expect("one operand per operator");
            while let Some(top) = pending.last() {
                if top.precedence > operator.precedence {
                    reduce(&mut output, top);
                    pending.pop();
                    continue;
                }
                if top.precedence == operator.precedence {
                    if top.associativity != operator.associativity {
                        return Err(conflict(
                            "mixed operator associativity",
                            format!(
                                "`{}` and `{}` share precedence {} but disagree on associativity; parenthesize the expression",
                                top.spelling, operator.spelling, operator.precedence
                            ),
                            top,
                            &operator,
                        ));
                    }
                    match operator.associativity {
                        Associativity::Left => {
                            reduce(&mut output, top);
                            pending.pop();
                            continue;
                        }
                        Associativity::Right => {}
                        Associativity::None => {
                            return Err(conflict(
                                "chained nonassociative operators",
                                format!(
                                    "`{}` is nonassociative and cannot chain with `{}`; parenthesize the expression",
                                    operator.spelling, top.spelling
                                ),
                                top,
                                &operator,
                            ));
                        }
                    }
                }
                break;
            }
            pending.push(operator);
            output.push(operand);
        }
        while let Some(top) = pending.pop() {
            reduce(&mut output, &top);
        }
        let expression = output.pop().expect("grouping yields one expression");
        debug_assert!(output.is_empty());
        Ok(expression)
    }

    /// True when the tokens ahead read `( params ) ->`, distinguishing an
    /// explicit typed anonymous callable from tuple and group expressions.
    fn typed_closure_ahead(&self) -> bool {
        let mut cursor = self.cursor + 1;
        let mut depth = 1usize;
        while depth > 0 {
            match self.tokens.get(cursor).map(|token| &token.kind) {
                Some(TokenKind::LParen) => depth += 1,
                Some(TokenKind::RParen) => depth -= 1,
                Some(TokenKind::Eof) | None => return false,
                _ => {}
            }
            cursor += 1;
        }
        matches!(
            self.tokens.get(cursor).map(|token| &token.kind),
            Some(TokenKind::Arrow)
        )
    }

    /// `(x: i32, y: i32) -> i32 { x + y }` — the same signature form as a
    /// named callable declaration, as an anonymous expression.
    fn typed_closure(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.bump().span;
        let (params, _) = self.collect_comma_delimited(
            TokenKind::RParen,
            "expected `)` after closure parameters",
            |parser| parser.typed_parameter("expected a typed closure parameter name"),
        )?;
        self.expect(TokenKind::Arrow, "expected `->` in the closure signature")?;
        let return_type = if self.at(&TokenKind::LBrace) || self.at(&TokenKind::Slash) {
            None
        } else {
            Some(Rc::new(self.type_syntax()?))
        };
        let outward_effects = if self.eat(&TokenKind::Slash) {
            Some(Rc::new(self.effect_row()?))
        } else {
            None
        };
        let body = self.block()?;
        let span = start.join(body.span);
        Ok(Expr {
            kind: ExprKind::TypedClosure {
                params: Rc::new(params),
                return_type,
                effectful: outward_effects.is_some(),
                outward_effects,
                body: Rc::new(body),
            },
            span,
        })
    }

    /// `resume(k, value)`, `cancel(k)`, and `tail(k, value)` are structural
    /// operations on a resumption, not ordinary calls.
    fn resumption_operation(&mut self, keyword: Kw, start: Span) -> Result<Expr, Diagnostic> {
        self.expect(
            TokenKind::LParen,
            "expected `(` after the resumption operation",
        )?;
        let (mut args, end) = self.collect_comma_delimited(
            TokenKind::RParen,
            "expected `)` after the resumption",
            |parser| parser.expression(0),
        )?;
        let span = start.join(end);
        let kind = match (keyword, args.len()) {
            (Kw::Resume, 1 | 2) => {
                let value = (args.len() == 2).then(|| Rc::new(args.pop().unwrap()));
                ExprKind::Resume {
                    resumption: Rc::new(args.pop().unwrap()),
                    value,
                }
            }
            (Kw::Tail, 1 | 2) => {
                let value = (args.len() == 2).then(|| Rc::new(args.pop().unwrap()));
                ExprKind::TailResume {
                    resumption: Rc::new(args.pop().unwrap()),
                    value,
                }
            }
            (Kw::Cancel, 1) => ExprKind::Cancel {
                resumption: Rc::new(args.pop().unwrap()),
            },
            (Kw::Cancel, count) => {
                return Err(Diagnostic::error(
                    "invalid resumption operation",
                    format!("`cancel` requires exactly 1 argument, found {count}"),
                    span,
                ));
            }
            (Kw::Resume | Kw::Tail, count) => {
                return Err(Diagnostic::error(
                    "invalid resumption operation",
                    format!(
                        "`{}` requires 1 or 2 arguments, found {count}",
                        keyword.as_str()
                    ),
                    span,
                ));
            }
            _ => unreachable!("resumption_operation is called only for resumption keywords"),
        };
        Ok(Expr { kind, span })
    }

    fn primary(&mut self) -> Result<Expr, Diagnostic> {
        if self.at_kw(Kw::Perform) {
            return self.perform();
        }
        if self.at_kw(Kw::Handle) {
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
        if self.at(&TokenKind::Star)
            && self
                .peek_n(1)
                .is_some_and(|operand| self.peek().span.end == operand.span.start)
        {
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
        if let Some((name, span, token_count, precedence)) = self.peek_prefix_operator() {
            for _ in 0..token_count {
                self.bump();
            }
            let operand = if self.at(&TokenKind::LBrace) {
                self.operand()?
            } else {
                self.expression(precedence)?
            };
            let full = span.join(operand.span);
            return Ok(Expr {
                kind: ExprKind::Call(
                    Rc::new(Expr {
                        kind: ExprKind::Variable(Rc::from([Rc::from(name.as_str())])),
                        span,
                    }),
                    Rc::new(vec![operand]),
                ),
                span: full,
            });
        }
        if self.at(&TokenKind::LParen) && self.typed_closure_ahead() {
            return self.typed_closure();
        }
        let token = self.bump().clone();
        let mut expr = match token.kind {
            TokenKind::Number(literal) => {
                self.numeric_literals
                    .push(crate::ast::NumericLiteralSyntax {
                        span: token.span,
                        literal: literal.clone(),
                    });
                if literal.is_float() {
                    Expr {
                        kind: ExprKind::Float(0.0),
                        span: token.span,
                    }
                } else {
                    Expr {
                        // This payload exists only for normalized AST consumers.
                        // Semantic consumers select a width from the exact
                        // `numeric_literals` spelling recorded above.
                        kind: ExprKind::Int(literal.as_i64(token.span).unwrap_or(0)),
                        span: token.span,
                    }
                }
            }
            TokenKind::String(value) => Expr {
                kind: ExprKind::String(value.into()),
                span: token.span,
            },
            TokenKind::Char(value) => Expr {
                kind: ExprKind::Char(value),
                span: token.span,
            },
            TokenKind::Byte(value) => Expr {
                kind: ExprKind::Byte(value),
                span: token.span,
            },
            TokenKind::ByteString(value) => Expr {
                kind: ExprKind::ByteString(Rc::from(value.as_slice())),
                span: token.span,
            },
            TokenKind::Keyword(keyword @ (Kw::Resume | Kw::Cancel | Kw::Tail)) => {
                return self.resumption_operation(keyword, token.span);
            }
            TokenKind::Label(name) => {
                let label = LabelSyntax {
                    name: Rc::from(name.as_str()),
                    span: token.span,
                };
                if self.at(&TokenKind::Colon) {
                    self.bump();
                    let ty = if self.at(&TokenKind::LBrace) {
                        None
                    } else {
                        Some(Rc::new(self.type_syntax()?))
                    };
                    let body = self.block()?;
                    let span = token.span.join(body.span);
                    return Ok(Expr {
                        kind: ExprKind::LabelDestination {
                            label,
                            ty,
                            body: Rc::new(body),
                        },
                        span,
                    });
                }
                Expr {
                    kind: ExprKind::LabelReference(label),
                    span: token.span,
                }
            }
            TokenKind::Ident(name) => {
                if name == "label" && matches!(self.peek().kind, TokenKind::Label(_)) {
                    return Err(Diagnostic::error(
                        "removed label syntax",
                        "`label @name: T { ... }` is no longer part of the grammar",
                        token.span,
                    )
                    .with_help("write `@name: T { ... }`"));
                }
                if name == "leave" && matches!(self.peek().kind, TokenKind::Label(_)) {
                    return Err(Diagnostic::error(
                        "removed label syntax",
                        "`leave@name(value)` is no longer part of the grammar",
                        token.span,
                    )
                    .with_help("write `@name(value)`"));
                }
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
            TokenKind::Dollar => {
                let (name, name_span) =
                    self.ident("expected a callable name immediately after `$`")?;
                if token.span.end != name_span.start {
                    return Err(Diagnostic::error(
                        "separated callable reference",
                        "`$` must be directly adjacent to the callable name",
                        token.span.join(name_span),
                    ));
                }
                let mut path: Vec<Rc<str>> = vec![Rc::from(name.as_str())];
                let mut end = name_span;
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
                        let (mut remaining, end) = self.collect_comma_delimited(
                            TokenKind::RParen,
                            "expected `)`",
                            |parser| parser.expression(0),
                        )?;
                        elements.append(&mut remaining);
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
                let (values, end) = self.collect_comma_delimited(
                    TokenKind::RBracket,
                    "expected `]` after list elements",
                    |parser| parser.expression(0),
                )?;
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
            if self.handling_scrutinee && self.looks_like_handler_clause_block() {
                break;
            } else if self.at(&TokenKind::LBrace)
                && matches!(&expr.kind, ExprKind::Call(callee, args)
                    if matches!(&callee.kind, ExprKind::Variable(path)
                        if path.len() == 1 && path[0].as_ref() == "match")
                    && args.len() == 1)
            {
                expr = self.match_expression(expr)?;
            } else if self.at(&TokenKind::LBrace)
                && matches!(&expr.kind, ExprKind::Call(_, _))
                && !self.looks_like_handler_clause_block()
            {
                let mut block = if self.compact_closure_ahead() {
                    self.primary()?
                } else {
                    self.block()?
                };
                if let ExprKind::Block(statements) = &block.kind {
                    block.kind = ExprKind::ContextBlock(statements.clone());
                }
                let span = expr.span.join(block.span);
                let ExprKind::Call(callee, args) = expr.kind else {
                    unreachable!()
                };
                let mut args = Rc::try_unwrap(args).unwrap_or_else(|shared| (*shared).clone());
                args.push(block);
                if args.len() == 2
                    && let ExprKind::Variable(path) = &callee.kind
                    && let [name] = path.as_ref()
                    && matches!(name.as_ref(), "while" | "until")
                    && matches!(args[0].kind, ExprKind::ContextBlock(_))
                    && matches!(args[1].kind, ExprKind::ContextBlock(_))
                {
                    let condition = args.remove(0);
                    let body = args.remove(0);
                    let ExprKind::ContextBlock(body_statements) = body.kind else {
                        unreachable!()
                    };
                    let mut body_statements =
                        Rc::try_unwrap(body_statements).unwrap_or_else(|shared| (*shared).clone());
                    body_statements.push(Stmt::Expr(Expr {
                        kind: ExprKind::Call(
                            Rc::new(Expr {
                                kind: ExprKind::Variable(Rc::from([Rc::<str>::from(
                                    "__g1_loop_continue_flag",
                                )])),
                                span: body.span,
                            }),
                            Rc::new(vec![]),
                        ),
                        span: body.span,
                    }));
                    let mut positive = Expr {
                        kind: ExprKind::ContextBlock(Rc::new(body_statements)),
                        span: body.span,
                    };
                    let mut negative = Expr {
                        kind: ExprKind::ContextBlock(Rc::new(vec![Stmt::Expr(Expr {
                            kind: ExprKind::Call(
                                Rc::new(Expr {
                                    kind: ExprKind::Variable(Rc::from([Rc::<str>::from(
                                        "__g1_loop_stop_flag",
                                    )])),
                                    span: condition.span,
                                }),
                                Rc::new(vec![]),
                            ),
                            span: condition.span,
                        })])),
                        span: condition.span,
                    };
                    if name.as_ref() == "until" {
                        std::mem::swap(&mut positive, &mut negative);
                    }
                    let conditional = Expr {
                        kind: ExprKind::Call(
                            Rc::new(Expr {
                                kind: ExprKind::Variable(Rc::from([Rc::<str>::from("if")])),
                                span: condition.span,
                            }),
                            Rc::new(vec![condition, positive]),
                        ),
                        span,
                    };
                    let step = Expr {
                        kind: ExprKind::Call(
                            Rc::new(Expr {
                                kind: ExprKind::Variable(Rc::from([Rc::<str>::from("else")])),
                                span,
                            }),
                            Rc::new(vec![conditional, negative]),
                        ),
                        span,
                    };
                    args.push(Expr {
                        kind: ExprKind::ContextBlock(Rc::new(vec![Stmt::Expr(step)])),
                        span,
                    });
                }
                expr = Expr {
                    kind: ExprKind::Call(callee, Rc::new(args)),
                    span,
                };
            } else if matches!(&self.peek().kind, TokenKind::Label(_))
                && matches!(
                    self.peek_n(1).map(|token| &token.kind),
                    Some(TokenKind::Colon)
                )
            {
                return Err(Diagnostic::error(
                    "removed labeled trailing application",
                    "a label binder may no longer trail a callable application",
                    self.peek().span,
                )
                .with_help("introduce `@name: { ... }` as an ordinary enclosing binder"));
            } else if self.at(&TokenKind::LBrace)
                && matches!(&expr.kind, ExprKind::Variable(path)
                    if path.len() == 1
                        && matches!(path[0].as_ref(), "loop" | "while" | "until"))
            {
                // Library control callables may take their first contextual
                // argument without an empty `()`: `loop { ... }` and
                // `while { condition } { body }` remain ordinary calls after
                // this grammar-only elaboration.
                let mut block = if self.compact_closure_ahead() {
                    self.primary()?
                } else {
                    self.block()?
                };
                if let ExprKind::Block(statements) = &block.kind {
                    block.kind = ExprKind::ContextBlock(statements.clone());
                }
                let span = expr.span.join(block.span);
                expr = Expr {
                    kind: ExprKind::Call(Rc::new(expr), Rc::new(vec![block])),
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
                let (fields, end) = self.collect_comma_delimited(
                    TokenKind::RBrace,
                    "expected `}` after struct fields",
                    |parser| {
                        let (field, _) = parser.ident("expected a struct field name")?;
                        parser.expect(TokenKind::Colon, "expected `:` after the field name")?;
                        Ok((field, parser.expression(0)?))
                    },
                )?;
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
                        kind: TokenKind::Number(literal),
                        span,
                    } if !literal.is_float() => (literal.as_u64(span)?.to_string(), span),
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
                let (args, end) = self.collect_comma_delimited(
                    TokenKind::RParen,
                    "expected `)` after arguments",
                    |parser| parser.expression(0),
                )?;
                let span = expr.span.join(end);
                expr = Expr {
                    kind: ExprKind::Call(Rc::new(expr), Rc::new(args)),
                    span,
                };
            } else if !self.in_whitespace_argument
                && self.starts_whitespace_argument()
                && expr.span.end < self.peek().span.start
            {
                let callee = expr;
                let mut args = Vec::new();
                loop {
                    let previous = self.in_whitespace_argument;
                    self.in_whitespace_argument = true;
                    let argument = self.expression(0);
                    self.in_whitespace_argument = previous;
                    args.push(argument?);
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                    if !self.starts_expression() {
                        return Err(self.error(
                            "expected a call argument",
                            "expected an expression after `,`",
                        ));
                    }
                }
                let span = callee.span.join(args.last().expect("one argument").span);
                expr = Expr {
                    kind: ExprKind::Call(Rc::new(callee), Rc::new(args)),
                    span,
                };
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn starts_expression(&self) -> bool {
        matches!(
            self.peek().kind,
            TokenKind::Number(_)
                | TokenKind::String(_)
                | TokenKind::Char(_)
                | TokenKind::Byte(_)
                | TokenKind::ByteString(_)
                | TokenKind::Ident(_)
                | TokenKind::Label(_)
                | TokenKind::Keyword(_)
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::LBrace
                | TokenKind::Minus
                | TokenKind::Amp
                | TokenKind::Star
                | TokenKind::Dollar
        )
    }

    fn starts_whitespace_argument(&self) -> bool {
        self.starts_expression()
            && self.peek_infix().is_none()
            && !matches!(
                self.peek().kind,
                TokenKind::LBrace
                    | TokenKind::Keyword(Kw::Is)
                    | TokenKind::Keyword(Kw::Where)
                    | TokenKind::Keyword(Kw::Impl)
            )
    }

    /// Elaborate library `match(value) { pattern => body, ... }` into the
    /// already-existing source-defined refinement calls.  A synthetic local
    /// evaluates the subject exactly once; every arm becomes
    /// `if(subject is pattern) { body } else { next }`.
    fn match_expression(&mut self, call: Expr) -> Result<Expr, Diagnostic> {
        let ExprKind::Call(_, arguments) = call.kind else {
            unreachable!()
        };
        let [subject] = arguments.as_slice() else {
            unreachable!()
        };
        self.bump(); // `{`
        let mut arms = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            let pattern = self.pattern()?;
            Self::reject_duplicate_binders(std::slice::from_ref(&pattern))?;
            self.expect(TokenKind::FatArrow, "expected `=>` after the match pattern")?;
            let body = self.expression(0)?;
            arms.push((pattern, body));
            self.eat(&TokenKind::Comma);
            self.eat(&TokenKind::Semicolon);
        }
        let end = self
            .expect(TokenKind::RBrace, "expected `}` after match arms")?
            .span;
        if arms.is_empty() {
            return Err(Diagnostic::error(
                "empty match",
                "a match block requires at least one pattern arm",
                call.span.join(end),
            ));
        }
        let binding = format!("$match${}", call.span.start);
        let variable = || Expr {
            kind: ExprKind::Variable(Rc::from([Rc::<str>::from(binding.as_str())])),
            span: subject.span,
        };
        let abort = Expr {
            kind: ExprKind::Call(
                Rc::new(Expr {
                    kind: ExprKind::Variable(Rc::from([Rc::<str>::from("unreachable")])),
                    span: end,
                }),
                Rc::new(vec![]),
            ),
            span: end,
        };
        let mut next = abort;
        for (pattern, body) in arms.into_iter().rev() {
            let arm_span = pattern.span.join(body.span);
            let condition = Expr {
                kind: ExprKind::Is {
                    subject: Rc::new(variable()),
                    pattern: Rc::new(pattern),
                },
                span: arm_span,
            };
            let positive = Expr {
                kind: ExprKind::ContextBlock(Rc::new(vec![Stmt::Expr(body)])),
                span: arm_span,
            };
            let if_call = Expr {
                kind: ExprKind::Call(
                    Rc::new(Expr {
                        kind: ExprKind::Variable(Rc::from([Rc::<str>::from("if")])),
                        span: arm_span,
                    }),
                    Rc::new(vec![condition, positive]),
                ),
                span: arm_span,
            };
            let negative = Expr {
                kind: ExprKind::ContextBlock(Rc::new(vec![Stmt::Expr(next)])),
                span: arm_span,
            };
            next = Expr {
                kind: ExprKind::Call(
                    Rc::new(Expr {
                        kind: ExprKind::Variable(Rc::from([Rc::<str>::from("else")])),
                        span: arm_span,
                    }),
                    Rc::new(vec![if_call, negative]),
                ),
                span: arm_span,
            };
        }
        Ok(Expr {
            kind: ExprKind::Block(Rc::new(vec![
                Stmt::Let {
                    name: binding,
                    value: subject.clone(),
                    span: subject.span,
                },
                Stmt::Expr(next),
            ])),
            span: call.span.join(end),
        })
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
        let mut delimiters = Vec::new();
        while let Some(token) = self.tokens.get(cursor) {
            match token.kind {
                TokenKind::FatArrow if delimiters.is_empty() => return true,
                TokenKind::LParen => delimiters.push(TokenKind::RParen),
                TokenKind::LBracket => delimiters.push(TokenKind::RBracket),
                TokenKind::LBrace => delimiters.push(TokenKind::RBrace),
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                    if delimiters.is_empty() {
                        return false;
                    }
                    delimiters.pop();
                }
                TokenKind::Eof => return false,
                _ => {}
            }
            cursor += 1;
        }
        false
    }

    fn compact_closure_ahead(&self) -> bool {
        if !self.at(&TokenKind::LBrace) {
            return false;
        }
        let first = self.tokens.get(self.cursor + 1).map(|token| &token.kind);
        if matches!(first, Some(TokenKind::FatArrow))
            || matches!(first, Some(TokenKind::Ident(_)))
                && matches!(
                    self.tokens.get(self.cursor + 2).map(|token| &token.kind),
                    Some(TokenKind::FatArrow | TokenKind::Comma)
                )
        {
            return true;
        }
        if !matches!(first, Some(TokenKind::LParen)) {
            return false;
        }
        let mut cursor = self.cursor + 2;
        let mut expect_name = true;
        loop {
            match self.tokens.get(cursor).map(|token| &token.kind) {
                Some(TokenKind::RParen) if !expect_name || cursor == self.cursor + 2 => {
                    return matches!(
                        self.tokens.get(cursor + 1).map(|token| &token.kind),
                        Some(TokenKind::FatArrow)
                    );
                }
                Some(TokenKind::Ident(_)) if expect_name => expect_name = false,
                Some(TokenKind::Comma) if !expect_name => expect_name = true,
                _ => return false,
            }
            cursor += 1;
        }
    }

    fn braced_expression(&mut self, start: Span) -> Result<Expr, Diagnostic> {
        let parenthesized_closure = self.at(&TokenKind::LParen) && {
            let mut cursor = self.cursor + 1;
            let mut expect_name = true;
            loop {
                match self.tokens.get(cursor).map(|token| &token.kind) {
                    Some(TokenKind::RParen) if !expect_name || cursor == self.cursor + 1 => {
                        break matches!(
                            self.tokens.get(cursor + 1).map(|token| &token.kind),
                            Some(TokenKind::FatArrow)
                        );
                    }
                    Some(TokenKind::Ident(_)) if expect_name => expect_name = false,
                    Some(TokenKind::Comma) if !expect_name => expect_name = true,
                    _ => break false,
                }
                cursor += 1;
            }
        };
        let closure = parenthesized_closure
            || self.at(&TokenKind::FatArrow)
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
        if parenthesized_closure {
            self.bump();
        }
        while !self.at(if parenthesized_closure {
            &TokenKind::RParen
        } else {
            &TokenKind::FatArrow
        }) {
            let (param, _) = self.ident("expected a closure parameter")?;
            params.push(Rc::from(param.as_str()));
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        if parenthesized_closure {
            self.expect(TokenKind::RParen, "expected `)` after closure parameters")?;
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
        let was_handling_scrutinee = self.handling_scrutinee;
        self.handling_scrutinee = true;
        let computation = self.expression(0);
        self.handling_scrutinee = was_handling_scrutinee;
        let computation = computation?;
        // A direct perform names the only operation this handler can possibly
        // be spelling.  Keep that head around so clauses may write just the
        // payload pattern (`Result::Ok(value) => ...`).  The compatibility AST
        // remains fully explicit: elision is parser sugar only.
        let elided_head = match &computation.kind {
            ExprKind::Perform {
                effect, operation, ..
            } => Some((effect.to_string(), operation.to_string())),
            _ => None,
        };
        let elided_effect_path = elided_head.as_ref().and_then(|_| {
            self.effect_paths
                .iter()
                .find(|path| path.site == computation.span)
                .map(|path| path.effect.clone())
        });
        self.expect(TokenKind::LBrace, "expected `{` and handler clauses")?;
        let mut clauses = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            let clause_start = self.peek().span;
            let saved_cursor = self.cursor;
            let saved_type_const_arguments = self.type_const_arguments.len();
            let explicit = (|| {
                let (effect, effect_path) = self
                    .effect_path_syntax("expected an effect name in this handler clause")
                    .ok()?;
                self.eat(&TokenKind::DoubleColon).then_some(())?;
                let (operation, _) = self.ident("expected an operation name").ok()?;
                self.eat(&TokenKind::LParen).then_some(())?;
                let (patterns, _) = self
                    .collect_comma_delimited(
                        TokenKind::RParen,
                        "expected `)` after handler patterns",
                        Self::pattern,
                    )
                    .ok()?;
                Some((effect, effect_path, operation, patterns))
            })();
            let (effect, effect_path, operation, patterns) = match (explicit, &elided_head) {
                (Some((effect, effect_path, operation, patterns)), _)
                    if Some((&effect, &operation))
                        == elided_head
                            .as_ref()
                            .map(|(effect, operation)| (effect, operation)) =>
                {
                    (effect, effect_path, operation, patterns)
                }
                (Some((effect, effect_path, operation, patterns)), Some(_))
                    if operation.chars().next().is_some_and(char::is_lowercase) =>
                {
                    // A different lower-case operation head is an ordinary
                    // additional handled effect, not an enum variant pattern
                    // with its operation wrapper elided.
                    (effect, effect_path, operation, patterns)
                }
                (_, Some((effect, operation))) => {
                    self.cursor = saved_cursor;
                    self.type_const_arguments
                        .truncate(saved_type_const_arguments);
                    let pattern = self.pattern()?;
                    (
                        effect.clone(),
                        elided_effect_path
                            .clone()
                            .expect("a parsed perform always records its complete effect path"),
                        operation.clone(),
                        vec![pattern],
                    )
                }
                (Some((effect, effect_path, operation, patterns)), None) => {
                    (effect, effect_path, operation, patterns)
                }
                (None, None) => {
                    self.cursor = saved_cursor;
                    self.type_const_arguments
                        .truncate(saved_type_const_arguments);
                    let pattern = self.pattern()?;
                    let pattern_span = pattern.span;
                    (
                        String::new(),
                        TypeSyntax {
                            kind: TypeSyntaxKind::Path(Vec::new()),
                            span: pattern_span,
                        },
                        String::new(),
                        vec![pattern],
                    )
                }
            };
            Self::reject_duplicate_binders(&patterns)?;
            let resumption = if self.at_ident("with") {
                self.bump();
                Some(self.ident("expected a resumption binding after `with`")?.0)
            } else {
                None
            };
            self.expect(TokenKind::FatArrow, "expected `=>` before the handler body")?;
            let body = self.expression(0)?;
            let span = clause_start.join(body.span);
            if !effect.is_empty() {
                self.effect_paths.push(EffectPathSyntax {
                    site: span,
                    effect: effect_path,
                });
            }
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
                if path.len() == 1 && self.at(&TokenKind::LBrace) {
                    return self.struct_pattern(path.remove(0), token.span);
                }
                if path.len() == 1 {
                    Pattern {
                        kind: PatternKind::Binding(path.remove(0)),
                        span: token.span,
                    }
                } else {
                    Pattern {
                        kind: PatternKind::Variant {
                            path: crate::ast::PatternPath {
                                segments: path,
                                span: token.span.join(end),
                            },
                            fields: Vec::new(),
                            rest: None,
                        },
                        span: token.span.join(end),
                    }
                }
            }
            TokenKind::Number(literal) => {
                self.numeric_literals
                    .push(crate::ast::NumericLiteralSyntax {
                        span: token.span,
                        literal: literal.clone(),
                    });
                if literal.is_float() {
                    Pattern {
                        kind: PatternKind::Float(0.0),
                        span: token.span,
                    }
                } else {
                    Pattern {
                        // Pattern typing likewise consumes the exact side-table
                        // entry; never make this compatibility shadow the
                        // source-range authority.
                        kind: PatternKind::Int(literal.as_i64(token.span).unwrap_or(0)),
                        span: token.span,
                    }
                }
            }
            TokenKind::String(value) => Pattern {
                kind: PatternKind::String(value),
                span: token.span,
            },
            TokenKind::Char(value) => Pattern {
                kind: PatternKind::Char(value),
                span: token.span,
            },
            TokenKind::Byte(value) => Pattern {
                kind: PatternKind::Byte(value),
                span: token.span,
            },
            TokenKind::LParen if self.eat(&TokenKind::RParen) => Pattern {
                kind: PatternKind::Unit,
                span: token.span.join(self.previous().span),
            },
            TokenKind::LParen => return self.tuple_or_grouped_pattern(token.span),
            _ => {
                return Err(Diagnostic::error(
                    "expected a pattern",
                    "patterns are literals, bindings, `_`, tuples, structs, and enum variants",
                    token.span,
                ));
            }
        };
        if matches!(pattern.kind, PatternKind::Variant { .. }) && self.eat(&TokenKind::LParen) {
            let mut fields = Vec::new();
            let mut rest: Option<PatternRest> = None;
            while !self.at(&TokenKind::RParen) {
                if self.at(&TokenKind::DotDot) {
                    let span = self.bump().span;
                    if let Some(existing) = rest {
                        return Err(Diagnostic::error(
                            "duplicate pattern remainder",
                            "a variant payload pattern may contain only one `..` remainder",
                            span,
                        )
                        .with_related(existing.span, "the first remainder is here"));
                    }
                    rest = Some(PatternRest {
                        before: fields.len(),
                        span,
                    });
                } else {
                    fields.push(self.pattern()?);
                }
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
                kind: PatternKind::Variant { path, fields, rest },
                span: pattern.span.join(end),
            };
        }
        Ok(pattern)
    }

    /// `(a, b, ..)` tuple patterns and `(pattern)` grouping. A singleton with
    /// no comma and no remainder is grouping and keeps the inner pattern.
    fn tuple_or_grouped_pattern(&mut self, start: Span) -> Result<Pattern, Diagnostic> {
        let mut elements = Vec::new();
        let mut rest: Option<PatternRest> = None;
        let mut saw_comma = false;
        while !self.at(&TokenKind::RParen) {
            if self.at(&TokenKind::DotDot) {
                let span = self.bump().span;
                if let Some(existing) = rest {
                    return Err(Diagnostic::error(
                        "duplicate pattern remainder",
                        "a tuple pattern may contain only one `..` remainder",
                        span,
                    )
                    .with_related(existing.span, "the first remainder is here"));
                }
                rest = Some(PatternRest {
                    before: elements.len(),
                    span,
                });
            } else {
                elements.push(self.pattern()?);
            }
            if !self.eat(&TokenKind::Comma) {
                break;
            }
            saw_comma = true;
        }
        let end = self
            .expect(TokenKind::RParen, "expected `)` after the tuple pattern")?
            .span;
        if rest.is_none() && elements.len() == 1 && !saw_comma {
            let mut inner = elements.remove(0);
            inner.span = start.join(end);
            return Ok(inner);
        }
        Ok(Pattern {
            kind: PatternKind::Tuple { elements, rest },
            span: start.join(end),
        })
    }

    /// `Name { field: pattern, shorthand, .. }` — the remainder must be last.
    fn struct_pattern(&mut self, name: String, start: Span) -> Result<Pattern, Diagnostic> {
        self.bump();
        let mut fields: Vec<StructFieldPattern> = Vec::new();
        let mut rest: Option<PatternRest> = None;
        while !self.at(&TokenKind::RBrace) {
            if self.at(&TokenKind::DotDot) {
                let span = self.bump().span;
                if let Some(existing) = rest {
                    return Err(Diagnostic::error(
                        "duplicate pattern remainder",
                        "a struct pattern may contain only one `..` remainder",
                        span,
                    )
                    .with_related(existing.span, "the first remainder is here"));
                }
                rest = Some(PatternRest {
                    before: fields.len(),
                    span,
                });
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
                continue;
            }
            if let Some(rest) = rest {
                return Err(Diagnostic::error(
                    "misplaced pattern remainder",
                    "`..` must be the final entry of a struct pattern",
                    rest.span,
                ));
            }
            let (field, field_span) = self.ident("expected a struct field name")?;
            if let Some(existing) = fields.iter().find(|entry| entry.field == field) {
                return Err(Diagnostic::error(
                    "duplicate struct pattern field",
                    format!("field `{field}` appears more than once"),
                    field_span,
                )
                .with_related(existing.span, "the first use is here"));
            }
            let (pattern, span) = if self.eat(&TokenKind::Colon) {
                let pattern = self.pattern()?;
                let span = field_span.join(pattern.span);
                (pattern, span)
            } else {
                (
                    Pattern {
                        kind: PatternKind::Binding(field.clone()),
                        span: field_span,
                    },
                    field_span,
                )
            };
            fields.push(StructFieldPattern {
                field,
                pattern,
                span,
            });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        let end = self
            .expect(TokenKind::RBrace, "expected `}` after the struct pattern")?
            .span;
        let pattern = Pattern {
            kind: PatternKind::Struct {
                name,
                name_span: start,
                fields,
                rest,
            },
            span: start.join(end),
        };
        Ok(pattern)
    }

    /// Rejects one binder name owning two places anywhere across `patterns`
    /// (a handler clause's complete pattern list, or one `is` pattern).
    fn reject_duplicate_binders(patterns: &[Pattern]) -> Result<(), Diagnostic> {
        fn walk<'a>(
            pattern: &'a Pattern,
            seen: &mut HashMap<&'a str, Span>,
        ) -> Result<(), Diagnostic> {
            match &pattern.kind {
                PatternKind::Binding(name) => {
                    if let Some(first) = seen.insert(name.as_str(), pattern.span)
                        && name != "_"
                    {
                        return Err(Diagnostic::error(
                            "duplicate pattern binder",
                            format!("binding `{name}` appears more than once in this pattern"),
                            pattern.span,
                        )
                        .with_related(first, "the first binding is here"));
                    }
                    Ok(())
                }
                PatternKind::Variant { fields, .. } => {
                    fields.iter().try_for_each(|field| walk(field, seen))
                }
                PatternKind::Tuple { elements, .. } => {
                    elements.iter().try_for_each(|element| walk(element, seen))
                }
                PatternKind::Struct { fields, .. } => fields
                    .iter()
                    .try_for_each(|field| walk(&field.pattern, seen)),
                PatternKind::Wildcard
                | PatternKind::Unit
                | PatternKind::Int(_)
                | PatternKind::Float(_)
                | PatternKind::String(_)
                | PatternKind::Char(_)
                | PatternKind::Byte(_) => Ok(()),
            }
        }
        let mut seen = HashMap::new();
        patterns
            .iter()
            .try_for_each(|pattern| walk(pattern, &mut seen))
    }

    fn perform(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.bump().span;
        let (effect, effect_path) =
            self.effect_path_syntax("expected an effect name after `perform`")?;
        self.expect(
            TokenKind::DoubleColon,
            "expected `::` between the effect and operation",
        )?;
        let (operation, _) = self.ident("expected an operation name")?;
        self.expect(TokenKind::LParen, "expected `(` after the operation")?;
        let (args, end) = self.collect_comma_delimited(
            TokenKind::RParen,
            "expected `)` after operation arguments",
            |parser| parser.expression(0),
        )?;
        let expression = Expr {
            kind: ExprKind::Perform {
                effect: effect.into(),
                operation: operation.into(),
                args: Rc::new(args),
            },
            span: start.join(end),
        };
        self.effect_paths.push(EffectPathSyntax {
            site: expression.span,
            effect: effect_path,
        });
        Ok(expression)
    }

    fn effect_path_syntax(&mut self, message: &str) -> Result<(String, TypeSyntax), Diagnostic> {
        let (first, first_span) = self.ident(message)?;
        let mut segments = vec![TypePathSegment {
            name: first,
            span: first_span,
        }];
        while self.at(&TokenKind::DoubleColon)
            && matches!(
                (
                    self.peek_n(1).map(|token| &token.kind),
                    self.peek_n(2).map(|token| &token.kind)
                ),
                (Some(TokenKind::Ident(_)), Some(TokenKind::DoubleColon))
            )
        {
            self.bump();
            let (name, span) = self.ident("expected an effect path segment")?;
            segments.push(TypePathSegment { name, span });
        }
        let name = segments.last().unwrap().name.clone();
        let span = first_span.join(segments.last().unwrap().span);
        let base = TypeSyntax {
            kind: TypeSyntaxKind::Path(segments),
            span,
        };
        if !self.eat(&TokenKind::Lt) {
            return Ok((name, base));
        }
        if self.at(&TokenKind::Gt) {
            return Err(self.error(
                "empty generic application",
                "expected at least one effect type argument between `<` and `>`",
            ));
        }
        let mut arguments = Vec::new();
        let mut lifetime_arguments = Vec::new();
        let mut const_arguments = Vec::new();
        let mut position = 0usize;
        loop {
            if let TokenKind::Lifetime(lifetime) = &self.peek().kind {
                let name = lifetime.clone();
                let span = self.bump().span;
                lifetime_arguments.push(crate::ast::GenericLifetimeArgumentSyntax {
                    position,
                    lifetime: LifetimeSyntax { name, span },
                });
            } else if self.starts_const_expression_argument() {
                const_arguments.push(ConstAssociatedArgumentSyntax {
                    position,
                    value: self.const_argument_value()?,
                });
            } else {
                arguments.push(self.type_syntax()?);
            }
            position += 1;
            if !self.eat(&TokenKind::Comma) || self.at(&TokenKind::Gt) {
                break;
            }
        }
        let end = self
            .expect(TokenKind::Gt, "expected `>` after effect type arguments")?
            .span;
        let application = TypeSyntax {
            span: span.join(end),
            kind: TypeSyntaxKind::Application {
                constructor: Box::new(base),
                arguments,
                lifetime_arguments,
            },
        };
        if !const_arguments.is_empty() {
            self.type_const_arguments
                .push(crate::ast::TypeConstApplicationSyntax {
                    application: application.span,
                    arguments: const_arguments,
                });
        }
        Ok((name, application))
    }

    fn const_argument_value(&mut self) -> Result<ConstArgumentValueSyntax, Diagnostic> {
        if matches!(&self.peek().kind, TokenKind::Number(literal) if literal.is_float()) {
            return Err(Diagnostic::error(
                "invalid const argument",
                "a const argument must be an integer, quantity, parameter, or arithmetic expression",
                self.peek().span,
            ));
        }
        let expression = self.const_expression()?;
        Ok(match expression.kind {
            ConstExprSyntaxKind::U32(value) => ConstArgumentValueSyntax::U32 {
                value,
                span: expression.span,
            },
            ConstExprSyntaxKind::Quantity(quantity) => ConstArgumentValueSyntax::Quantity(quantity),
            _ => ConstArgumentValueSyntax::Expression(expression),
        })
    }

    fn const_expression(&mut self) -> Result<ConstExprSyntax, Diagnostic> {
        self.const_expression_bp(0)
    }

    fn const_expression_bp(
        &mut self,
        minimum_precedence: u8,
    ) -> Result<ConstExprSyntax, Diagnostic> {
        let mut lhs = if self.eat(&TokenKind::Minus) {
            let start = self.previous().span;
            let operand = self.const_expression_bp(3)?;
            ConstExprSyntax {
                span: start.join(operand.span),
                kind: ConstExprSyntaxKind::Neg(Box::new(operand)),
            }
        } else if self.eat(&TokenKind::LParen) {
            let start = self.previous().span;
            let mut expression = self.const_expression()?;
            let end = self
                .expect(TokenKind::RParen, "expected `)` after the const expression")?
                .span;
            expression.span = start.join(end);
            expression
        } else if self.at(&TokenKind::LBracket) {
            let quantity = self.quantity()?;
            ConstExprSyntax {
                span: quantity.span,
                kind: ConstExprSyntaxKind::Quantity(quantity),
            }
        } else if let TokenKind::Number(literal) = &self.peek().kind {
            if literal.is_float() {
                return Err(self.error(
                    "invalid const expression",
                    "const expressions require integer or quantity values",
                ));
            }
            let literal = literal.clone();
            let span = self.bump().span;
            ConstExprSyntax {
                kind: ConstExprSyntaxKind::U32(literal.as_u64(span)?),
                span,
            }
        } else {
            let (name, span) =
                self.ident("expected a const literal, parameter, or parenthesized expression")?;
            let mut path = vec![TypePathSegment { name, span }];
            while self.eat(&TokenKind::DoubleColon) {
                let (name, span) = self.ident("expected a const path segment after `::`")?;
                path.push(TypePathSegment { name, span });
            }
            ConstExprSyntax {
                span: path.first().unwrap().span.join(path.last().unwrap().span),
                kind: ConstExprSyntaxKind::Path(path),
            }
        };

        loop {
            let (op, precedence) = if self.at(&TokenKind::Plus) {
                (ConstBinaryOp::Add, 1)
            } else if self.at(&TokenKind::Minus) {
                (ConstBinaryOp::Subtract, 1)
            } else if self.at(&TokenKind::Star) {
                (ConstBinaryOp::Multiply, 2)
            } else if self.at(&TokenKind::Slash) {
                (ConstBinaryOp::Divide, 2)
            } else if self.at(&TokenKind::Percent) {
                (ConstBinaryOp::Remainder, 2)
            } else {
                break;
            };
            if precedence < minimum_precedence {
                break;
            }
            self.bump();
            let rhs = self.const_expression_bp(precedence + 1)?;
            let span = lhs.span.join(rhs.span);
            lhs = ConstExprSyntax {
                kind: ConstExprSyntaxKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
        }
        Ok(lhs)
    }

    fn starts_const_expression_argument(&self) -> bool {
        if matches!(self.peek().kind, TokenKind::Number(_) | TokenKind::Minus) {
            return true;
        }
        if self.at(&TokenKind::LBracket) {
            return true;
        }
        if matches!(self.peek().kind, TokenKind::Ident(_)) {
            return self.peek_n(1).is_some_and(|token| {
                matches!(
                    token.kind,
                    TokenKind::Plus
                        | TokenKind::Minus
                        | TokenKind::Star
                        | TokenKind::Slash
                        | TokenKind::Percent
                )
            });
        }
        if !self.at(&TokenKind::LParen) {
            return false;
        }
        let mut depth = 0usize;
        for token in &self.tokens[self.cursor..] {
            match token.kind {
                TokenKind::LParen => depth += 1,
                TokenKind::RParen => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        break;
                    }
                }
                TokenKind::Plus
                | TokenKind::Minus
                | TokenKind::Star
                | TokenKind::Slash
                | TokenKind::Percent
                    if depth > 0 =>
                {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    fn type_syntax(&mut self) -> Result<TypeSyntax, Diagnostic> {
        let mut ty = if self.at(&TokenKind::LBracket) {
            let start = self.bump().span;
            let element = self.type_syntax()?;
            self.expect(
                TokenKind::Semicolon,
                "expected `;` between the array element type and length",
            )?;
            let length = self.const_expression()?;
            let end = self
                .expect(
                    TokenKind::RBracket,
                    "expected `]` after the fixed-array length",
                )?
                .span;
            let span = start.join(end);
            self.fixed_array_types
                .push(crate::ast::FixedArrayTypeSyntax {
                    array: span,
                    element: element.clone(),
                    length,
                });
            TypeSyntax {
                kind: TypeSyntaxKind::Tuple(vec![element]),
                span,
            }
        } else if self.at(&TokenKind::Lt) {
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
            let (arguments, const_arguments) = self.type_argument_list()?;
            let arguments_end = arguments
                .last()
                .map(AssociatedArgumentSyntax::span)
                .into_iter()
                .chain(const_arguments.last().map(|argument| argument.value.span()))
                .max_by_key(|span| span.end)
                .unwrap_or(span);
            TypeSyntax {
                span: start.join(arguments_end),
                kind: TypeSyntaxKind::Projection {
                    subject: Box::new(subject),
                    trait_ref,
                    item: TypePathSegment { name, span },
                    arguments,
                    const_arguments,
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
                    TypeSyntaxKind::UniqueReference {
                        lifetime,
                        referent: Box::new(referent),
                    }
                } else {
                    TypeSyntaxKind::SharedReference {
                        lifetime,
                        referent: Box::new(referent),
                    }
                },
            };
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
            let (mut remaining, end) = self.collect_comma_delimited(
                TokenKind::RParen,
                "expected `)` to close the tuple type",
                Self::type_syntax,
            )?;
            elements.append(&mut remaining);
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
            let mut lifetime_arguments = Vec::new();
            let mut const_arguments = Vec::new();
            let mut position = 0usize;
            if self.at(&TokenKind::Gt) {
                return Err(self.error(
                    "empty generic application",
                    "expected at least one type argument between `<` and `>`",
                ));
            }
            loop {
                if let TokenKind::Lifetime(name) = &self.peek().kind {
                    let name = name.clone();
                    let span = self.bump().span;
                    lifetime_arguments.push(crate::ast::GenericLifetimeArgumentSyntax {
                        position,
                        lifetime: LifetimeSyntax { name, span },
                    });
                } else if self.starts_const_expression_argument() {
                    const_arguments.push(ConstAssociatedArgumentSyntax {
                        position,
                        value: self.const_argument_value()?,
                    });
                } else {
                    arguments.push(self.type_syntax()?);
                }
                position += 1;
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
                    lifetime_arguments,
                },
            };
            if !const_arguments.is_empty() {
                self.type_const_arguments
                    .push(crate::ast::TypeConstApplicationSyntax {
                        application: ty.span,
                        arguments: const_arguments,
                    });
            }
        }
        Ok(ty)
    }

    /// Parses an associated-type argument list. Type and lifetime arguments
    /// fill the ordinary list; structural const arguments (`[l, u]` quantity
    /// intervals and bare integers) are recorded beside it with their exact
    /// source positions and spans. Named const binders parse as type paths
    /// and are reclassified against the declared parameter kinds during trait
    /// lowering.
    fn type_argument_list(
        &mut self,
    ) -> Result<
        (
            Vec<AssociatedArgumentSyntax>,
            Vec<ConstAssociatedArgumentSyntax>,
        ),
        Diagnostic,
    > {
        if !self.eat(&TokenKind::Lt) {
            return Ok((vec![], vec![]));
        }
        if self.at(&TokenKind::Gt) {
            return Err(self.error(
                "empty associated type arguments",
                "expected at least one associated type argument",
            ));
        }
        let mut arguments = Vec::new();
        let mut const_arguments = Vec::new();
        let mut position = 0usize;
        loop {
            if self.starts_const_expression_argument() {
                const_arguments.push(ConstAssociatedArgumentSyntax {
                    position,
                    value: self.const_argument_value()?,
                });
            } else if let TokenKind::Lifetime(name) = &self.peek().kind {
                let name = name.clone();
                let span = self.bump().span;
                arguments.push(AssociatedArgumentSyntax::Lifetime { name, span });
            } else {
                arguments.push(AssociatedArgumentSyntax::Type(self.type_syntax()?));
            }
            position += 1;
            if !self.eat(&TokenKind::Comma) || self.at(&TokenKind::Gt) {
                break;
            }
        }
        self.expect(
            TokenKind::Gt,
            "expected `>` after associated type arguments",
        )?;
        Ok((arguments, const_arguments))
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
            TokenKind::Keyword(keyword) => Err(Diagnostic::error(
                "expected a name",
                format!("`{}` is a reserved word", keyword.as_str()),
                token.span,
            )),
            _ => Err(Diagnostic::error("expected a name", message, token.span)),
        }
    }

    fn method_name(&mut self, message: &str) -> Result<(String, Span), Diagnostic> {
        if matches!(self.peek().kind, TokenKind::Ident(_)) {
            return self.ident(message);
        }
        let Some((name, span, count)) = joined_operator_name(&self.tokens, self.cursor) else {
            return Err(Diagnostic::error(
                "expected a name",
                message,
                self.peek().span,
            ));
        };
        for _ in 0..count {
            self.bump();
        }
        Ok((name, span))
    }

    /// Collect a comma-separated sequence after its opening delimiter and
    /// consume the closing delimiter. This deliberately retains the parser's
    /// established recovery behavior: a missing comma stops the sequence so
    /// the closing-delimiter diagnostic points at the unexpected token, and a
    /// trailing comma is accepted.
    fn collect_comma_delimited<T>(
        &mut self,
        close: TokenKind,
        close_message: &str,
        mut parse_element: impl FnMut(&mut Self) -> Result<T, Diagnostic>,
    ) -> Result<(Vec<T>, Span), Diagnostic> {
        let mut elements = Vec::new();
        while !self.at(&close) {
            elements.push(parse_element(self)?);
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        let end = self.expect(close, close_message)?.span;
        Ok((elements, end))
    }

    fn typed_parameter(&mut self, name_message: &str) -> Result<Param, Diagnostic> {
        let (name, start) = self.ident(name_message)?;
        self.expect(TokenKind::Colon, "expected `:` and a parameter type")?;
        let ty = self.type_syntax()?;
        Ok(Param {
            name,
            span: start.join(ty.span),
            ty,
        })
    }

    fn at_kw(&self, keyword: Kw) -> bool {
        matches!(&self.peek().kind, TokenKind::Keyword(found) if *found == keyword)
    }
    fn expect_kw(&mut self, keyword: Kw, message: &str) -> Result<Token, Diagnostic> {
        if self.at_kw(keyword) {
            Ok(self.bump().clone())
        } else {
            Err(self.error("unexpected syntax", message))
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

#[derive(Clone, Copy)]
struct SurfaceOperation {
    payloads: usize,
    terminal: bool,
}

/// Resolves the redesigned effect surface into the structural nodes consumed
/// by the existing semantic and MIR pipeline. This deliberately happens only
/// after the whole program has parsed, so operation calls and handler-pattern
/// heads are declaration-directed rather than guessed from capitalization.
fn normalize_effect_surface(program: &mut Program) -> Vec<Diagnostic> {
    let mut operations = program
        .effects
        .iter()
        .flat_map(|effect| {
            effect.operations.iter().map(move |operation| {
                (
                    (effect.name.clone(), operation.name.clone()),
                    SurfaceOperation {
                        payloads: operation.params.len(),
                        terminal: operation.terminal,
                    },
                )
            })
        })
        .collect::<BTreeMap<_, _>>();
    // Associated value bindings occupy the callable namespace at an ordinary
    // `Owner::name(...)` call site. They must not be reinterpreted merely
    // because an effect happens to use the same qualified spelling.
    for binding in &program.globals {
        if let Some(owner) = &binding.owner {
            operations.remove(&(owner.clone(), binding.name.clone()));
        }
    }
    fn variable(name: &str, span: Span) -> Expr {
        Expr {
            kind: ExprKind::Variable(Rc::from([Rc::<str>::from(name)])),
            span,
        }
    }

    fn completion_pattern(mut clause: HandlerClause) -> Option<(Pattern, Expr)> {
        if clause.effect.is_empty() {
            let [pattern] = clause.patterns.as_slice() else {
                return None;
            };
            return Some((pattern.clone(), clause.body));
        }
        Some((
            Pattern {
                kind: PatternKind::Variant {
                    path: crate::ast::PatternPath {
                        segments: vec![clause.effect, clause.operation],
                        span: clause.span,
                    },
                    fields: std::mem::take(&mut clause.patterns),
                    rest: None,
                },
                span: clause.span,
            },
            clause.body,
        ))
    }

    fn completion_match(subject: Expr, arms: Vec<(Pattern, Expr)>, span: Span) -> Expr {
        let binding = format!("$handle$result${}", span.start);
        let subject_span = subject.span;
        let value = || variable(&binding, subject_span);
        let abort = Expr {
            kind: ExprKind::Call(Rc::new(variable("unreachable", span)), Rc::new(Vec::new())),
            span,
        };
        let mut next = abort;
        for (pattern, body) in arms.into_iter().rev() {
            let arm_span = pattern.span.join(body.span);
            let condition = Expr {
                kind: ExprKind::Is {
                    subject: Rc::new(value()),
                    pattern: Rc::new(pattern),
                },
                span: arm_span,
            };
            let positive = Expr {
                kind: ExprKind::ContextBlock(Rc::new(vec![Stmt::Expr(body)])),
                span: arm_span,
            };
            let conditional = Expr {
                kind: ExprKind::Call(
                    Rc::new(variable("if", arm_span)),
                    Rc::new(vec![condition, positive]),
                ),
                span: arm_span,
            };
            let negative = Expr {
                kind: ExprKind::ContextBlock(Rc::new(vec![Stmt::Expr(next)])),
                span: arm_span,
            };
            next = Expr {
                kind: ExprKind::Call(
                    Rc::new(variable("else", arm_span)),
                    Rc::new(vec![conditional, negative]),
                ),
                span: arm_span,
            };
        }
        Expr {
            kind: ExprKind::Block(Rc::new(vec![
                Stmt::Let {
                    name: binding,
                    value: subject,
                    span: subject_span,
                },
                Stmt::Expr(next),
            ])),
            span,
        }
    }

    fn normalize(
        expression: &mut Expr,
        operations: &BTreeMap<(String, String), SurfaceOperation>,
        resumptions: &BTreeSet<String>,
        effect_paths: &mut Vec<EffectPathSyntax>,
        completion_sites: &mut BTreeSet<(usize, usize)>,
        errors: &mut Vec<Diagnostic>,
    ) {
        match &mut expression.kind {
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                normalize(
                    Rc::make_mut(computation),
                    operations,
                    resumptions,
                    effect_paths,
                    completion_sites,
                    errors,
                );
                let mut operation_clauses = Vec::new();
                let mut completion_arms = Vec::new();
                for mut clause in std::mem::take(Rc::make_mut(clauses)) {
                    let Some(operation) = operations
                        .get(&(clause.effect.clone(), clause.operation.clone()))
                        .copied()
                    else {
                        completion_sites.insert((clause.span.start, clause.span.end));
                        normalize(
                            &mut clause.body,
                            operations,
                            resumptions,
                            effect_paths,
                            completion_sites,
                            errors,
                        );
                        if let Some(arm) = completion_pattern(clause) {
                            completion_arms.push(arm);
                        }
                        continue;
                    };

                    if operation.terminal {
                        if clause.resumption.is_some() {
                            // Preserve the legacy shape so validation emits its
                            // established terminal-resumption diagnostic.
                        } else if clause.patterns.len() != operation.payloads {
                            errors.push(
                                Diagnostic::error(
                                    "wrong number of handler patterns",
                                    format!(
                                        "`{}::{}` declares {} payload(s), but this arm has {} pattern(s)",
                                        clause.effect,
                                        clause.operation,
                                        operation.payloads,
                                        clause.patterns.len()
                                    ),
                                    clause.span,
                                )
                                .with_code("G0140"),
                            );
                        }
                    } else if clause.resumption.is_none() {
                        match clause.patterns.len() {
                            count if count == operation.payloads => {
                                let binder = format!("$resume${}", clause.span.start);
                                let body = clause.body;
                                clause.body = Expr {
                                    kind: ExprKind::TailResume {
                                        resumption: Rc::new(variable(&binder, clause.span)),
                                        value: Some(Rc::new(body)),
                                    },
                                    span: clause.span,
                                };
                                clause.resumption = Some(binder);
                            }
                            count if count == operation.payloads + 1 => {
                                let continuation = clause.patterns.pop().unwrap();
                                match continuation.kind {
                                    PatternKind::Binding(name) => {
                                        clause.resumption = Some(name);
                                    }
                                    PatternKind::Wildcard => {
                                        let binder =
                                            format!("$discarded$resume${}", clause.span.start);
                                        let body = clause.body;
                                        clause.body = Expr {
                                            kind: ExprKind::Block(Rc::new(vec![
                                                Stmt::Expr(Expr {
                                                    kind: ExprKind::Cancel {
                                                        resumption: Rc::new(variable(
                                                            &binder,
                                                            continuation.span,
                                                        )),
                                                    },
                                                    span: continuation.span,
                                                }),
                                                Stmt::Expr(body),
                                            ])),
                                            span: clause.span,
                                        };
                                        clause.resumption = Some(binder);
                                    }
                                    _ => errors.push(
                                        Diagnostic::error(
                                            "invalid continuation pattern",
                                            "the final operation pattern must bind the continuation or discard it with `_`",
                                            continuation.span,
                                        )
                                        .with_code("G0141"),
                                    ),
                                }
                            }
                            count => errors.push(
                                Diagnostic::error(
                                    "wrong number of handler patterns",
                                    format!(
                                        "`{}::{}` accepts {} payload pattern(s), optionally followed by one continuation pattern; found {count}",
                                        clause.effect, clause.operation, operation.payloads
                                    ),
                                    clause.span,
                                )
                                .with_code("G0140"),
                            ),
                        }
                    }

                    let mut nested = resumptions.clone();
                    if let Some(resumption) = &clause.resumption {
                        nested.insert(resumption.clone());
                    }
                    normalize(
                        &mut clause.body,
                        operations,
                        &nested,
                        effect_paths,
                        completion_sites,
                        errors,
                    );
                    operation_clauses.push(clause);
                }

                if completion_arms.is_empty() {
                    *clauses = Rc::new(operation_clauses);
                    return;
                }
                let subject = if operation_clauses.is_empty() {
                    computation.as_ref().clone()
                } else {
                    Expr {
                        kind: ExprKind::Handle {
                            computation: computation.clone(),
                            clauses: Rc::new(operation_clauses),
                        },
                        span: expression.span,
                    }
                };
                *expression = completion_match(subject, completion_arms, expression.span);
            }
            ExprKind::Call(callee, arguments) => {
                normalize(
                    Rc::make_mut(callee),
                    operations,
                    resumptions,
                    effect_paths,
                    completion_sites,
                    errors,
                );
                for argument in Rc::make_mut(arguments).iter_mut() {
                    normalize(
                        argument,
                        operations,
                        resumptions,
                        effect_paths,
                        completion_sites,
                        errors,
                    );
                }
                if matches!(callee.kind, ExprKind::LabelReference(_)) && arguments.len() > 1 {
                    errors.push(
                        Diagnostic::error(
                            "invalid label invocation",
                            "a label is invoked with zero or one destination value",
                            expression.span,
                        )
                        .with_code("G0143"),
                    );
                    return;
                }
                let path = match &callee.kind {
                    ExprKind::Variable(path) => Some(path.clone()),
                    _ => None,
                };
                if let Some(path) = &path
                    && let [name] = path.as_ref()
                    && resumptions.contains(name.as_ref())
                {
                    if arguments.len() == 1 {
                        let value = Rc::new(arguments[0].clone());
                        expression.kind = ExprKind::Resume {
                            resumption: Rc::new(callee.as_ref().clone()),
                            value: Some(value),
                        };
                    } else {
                        errors.push(
                            Diagnostic::error(
                                "invalid continuation call",
                                "a continuation is called with exactly one operation-result value",
                                expression.span,
                            )
                            .with_code("G0142"),
                        );
                    }
                    return;
                }
                if let Some(path) = &path
                    && let [name] = path.as_ref()
                    && name.as_ref() == "discard"
                    && let [argument] = arguments.as_slice()
                    && matches!(&argument.kind, ExprKind::Variable(path)
                        if path.len() == 1 && resumptions.contains(path[0].as_ref()))
                {
                    expression.kind = ExprKind::Cancel {
                        resumption: Rc::new(argument.clone()),
                    };
                    return;
                }
                if let Some(path) = path
                    && path.len() == 2
                    && operations.contains_key(&(path[0].to_string(), path[1].to_string()))
                {
                    let effect = path[0].to_string();
                    let operation = path[1].to_string();
                    let args = arguments.clone();
                    effect_paths.push(EffectPathSyntax {
                        site: expression.span,
                        effect: TypeSyntax {
                            kind: TypeSyntaxKind::Path(vec![TypePathSegment {
                                name: effect.clone(),
                                span: callee.span,
                            }]),
                            span: callee.span,
                        },
                    });
                    expression.kind = ExprKind::Perform {
                        effect: Rc::from(effect),
                        operation: Rc::from(operation),
                        args,
                    };
                }
            }
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                for statement in Rc::make_mut(statements) {
                    let (value, reference) = match statement {
                        Stmt::Let { value, .. }
                        | Stmt::Deconstruct { value, .. }
                        | Stmt::Expr(value) => (value, None),
                        Stmt::Assign {
                            destination, value, ..
                        } => (
                            value,
                            match &mut destination.kind {
                                AssignmentPlaceKind::Dereference { reference, .. } => {
                                    Some(Rc::make_mut(reference))
                                }
                                AssignmentPlaceKind::Local { .. } => None,
                            },
                        ),
                    };
                    normalize(
                        value,
                        operations,
                        resumptions,
                        effect_paths,
                        completion_sites,
                        errors,
                    );
                    if let Some(reference) = reference {
                        normalize(
                            reference,
                            operations,
                            resumptions,
                            effect_paths,
                            completion_sites,
                            errors,
                        );
                    }
                }
            }
            ExprKind::Closure { params, body } => {
                let mut nested = resumptions.clone();
                for param in params.iter() {
                    nested.remove(param.as_ref());
                }
                normalize(
                    Rc::make_mut(body),
                    operations,
                    &nested,
                    effect_paths,
                    completion_sites,
                    errors,
                );
            }
            ExprKind::TypedClosure { params, body, .. } => {
                let mut nested = resumptions.clone();
                for param in params.iter() {
                    nested.remove(&param.name);
                }
                normalize(
                    Rc::make_mut(body),
                    operations,
                    &nested,
                    effect_paths,
                    completion_sites,
                    errors,
                );
            }
            ExprKind::Move(value)
            | ExprKind::Field(value, _)
            | ExprKind::LabelDestination { body: value, .. }
            | ExprKind::Unary { operand: value, .. } => normalize(
                Rc::make_mut(value),
                operations,
                resumptions,
                effect_paths,
                completion_sites,
                errors,
            ),
            ExprKind::List(values) | ExprKind::Tuple(values) => {
                for value in Rc::make_mut(values) {
                    normalize(
                        value,
                        operations,
                        resumptions,
                        effect_paths,
                        completion_sites,
                        errors,
                    );
                }
            }
            ExprKind::Struct { fields, .. } => {
                for (_, value) in Rc::make_mut(fields) {
                    normalize(
                        value,
                        operations,
                        resumptions,
                        effect_paths,
                        completion_sites,
                        errors,
                    );
                }
            }
            ExprKind::Perform { args, .. } => {
                for value in Rc::make_mut(args) {
                    normalize(
                        value,
                        operations,
                        resumptions,
                        effect_paths,
                        completion_sites,
                        errors,
                    );
                }
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                normalize(
                    Rc::make_mut(lhs),
                    operations,
                    resumptions,
                    effect_paths,
                    completion_sites,
                    errors,
                );
                normalize(
                    Rc::make_mut(rhs),
                    operations,
                    resumptions,
                    effect_paths,
                    completion_sites,
                    errors,
                );
            }
            ExprKind::Is { subject, .. } => normalize(
                Rc::make_mut(subject),
                operations,
                resumptions,
                effect_paths,
                completion_sites,
                errors,
            ),
            ExprKind::Resume { resumption, value } | ExprKind::TailResume { resumption, value } => {
                normalize(
                    Rc::make_mut(resumption),
                    operations,
                    resumptions,
                    effect_paths,
                    completion_sites,
                    errors,
                );
                if let Some(value) = value {
                    normalize(
                        Rc::make_mut(value),
                        operations,
                        resumptions,
                        effect_paths,
                        completion_sites,
                        errors,
                    );
                }
            }
            ExprKind::Cancel { resumption } => normalize(
                Rc::make_mut(resumption),
                operations,
                resumptions,
                effect_paths,
                completion_sites,
                errors,
            ),
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::Variable(_)
            | ExprKind::LabelReference(_) => {}
        }
    }

    let mut errors = Vec::new();
    let mut completion_sites = BTreeSet::new();
    let empty = BTreeSet::new();
    for global in &mut program.globals {
        normalize(
            &mut global.value,
            &operations,
            &empty,
            &mut program.effect_paths,
            &mut completion_sites,
            &mut errors,
        );
    }
    for function in &mut program.functions {
        normalize(
            &mut function.body,
            &operations,
            &empty,
            &mut program.effect_paths,
            &mut completion_sites,
            &mut errors,
        );
    }
    for implementation in &mut program.impls {
        for method in &mut implementation.methods {
            if let Some(body) = &mut method.body {
                normalize(
                    body,
                    &operations,
                    &empty,
                    &mut program.effect_paths,
                    &mut completion_sites,
                    &mut errors,
                );
            }
        }
    }
    for declaration in &mut program.traits {
        for method in &mut declaration.methods {
            if let Some(body) = &mut method.body {
                normalize(
                    body,
                    &operations,
                    &empty,
                    &mut program.effect_paths,
                    &mut completion_sites,
                    &mut errors,
                );
            }
        }
    }
    for drop in &mut program.drops {
        normalize(
            &mut drop.body,
            &operations,
            &empty,
            &mut program.effect_paths,
            &mut completion_sites,
            &mut errors,
        );
    }
    program
        .effect_paths
        .retain(|path| !completion_sites.contains(&(path.site.start, path.site.end)));
    errors
}

fn same_kind(lhs: &TokenKind, rhs: &TokenKind) -> bool {
    discriminant(lhs) == discriminant(rhs)
}

fn collect_fixities(
    tokens: &[Token],
    diagnostics: &mut Vec<Diagnostic>,
) -> HashMap<String, FixityEntry> {
    let module_source = tokens.windows(3).any(|window| {
        matches!(&window[0].kind, TokenKind::Ident(name) if name == "mod")
            && matches!(window[1].kind, TokenKind::Ident(_))
            && matches!(window[2].kind, TokenKind::Semicolon | TokenKind::LBrace)
    });
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
            "infix" => FixityKind::Infix(Associativity::None),
            "prefix" => FixityKind::Prefix,
            _ => {
                cursor += 1;
                continue;
            }
        };
        let Some(Token {
            kind: TokenKind::Number(precedence),
            span: precedence_span,
        }) = tokens.get(cursor + 1)
        else {
            cursor += 1;
            continue;
        };
        let Some((name, name_span, name_tokens)) = joined_operator_name(tokens, cursor + 2) else {
            cursor += 1;
            continue;
        };
        let (name, name_span) = (&name, &name_span);
        let terminator = cursor + 2 + name_tokens;
        if !tokens
            .get(terminator)
            .is_some_and(|token| matches!(token.kind, TokenKind::Semicolon))
        {
            cursor += 1;
            continue;
        }
        let precedence = precedence
            .as_i64(*precedence_span)
            .ok()
            .and_then(|value| u8::try_from(value).ok());
        let Some(precedence) = precedence else {
            diagnostics.push(Diagnostic::error(
                "invalid operator precedence",
                "operator precedence must be from 0 through 255",
                *precedence_span,
            ));
            cursor = terminator + 1;
            continue;
        };
        let entry = FixityEntry {
            kind,
            precedence,
            declaration: Some(*name_span),
        };
        if let Some(existing) = fixities.insert(name.clone(), entry)
            && let Some(original) = existing.declaration
            && !module_source
        {
            diagnostics.push(
                Diagnostic::error(
                    "operator fixity declared more than once",
                    format!("`{name}` has multiple fixity declarations"),
                    *name_span,
                )
                .with_related(original, "the first declaration is here"),
            );
        }
        cursor = terminator + 1;
    }
    fixities
}
