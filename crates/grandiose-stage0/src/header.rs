//! Parsed declaration headers shared by interfaces and body elaboration.
//!
//! The scanner owns declaration boundaries; this parser consumes only a
//! shell's header range. Function bodies therefore remain demand-driven while
//! type spelling, generic binders, and callable contracts have one syntax.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    quantity::Quantity,
    scanner::{DeclarationKind, DeclarationShell, TokenRange, Visibility},
    source::{LexedFile, Span, TokenKind},
    types::{ConstKind, GenericKind, PointerMutability, Safety},
};

/// A declaration's generic binders, including the small but semantically
/// important distinction between ordinary type parameters and effect-row
/// parameters.  Keeping the names in source order preserves the existing
/// generic-slot ABI while `effect_rows` prevents a row binder from being
/// silently elaborated as `Type::Generic`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct GenericParameters {
    pub names: Vec<String>,
    pub effect_rows: BTreeSet<String>,
    pub lifetimes: BTreeSet<String>,
    pub consts: BTreeSet<(String, ConstKind)>,
    /// Trailing structural defaults are declaration-interface facts.  They
    /// remain source-shaped until the receiving application's earlier
    /// arguments are known, so `m: u32 = n + 1` folds at specialization.
    pub const_defaults: BTreeMap<String, HeaderStructuralConst>,
    /// Kind-preserving source defaults; names are resolved in the declaring
    /// module, never in the module that omits an argument.
    pub defaults: BTreeMap<String, HeaderGenericArgument>,
}

impl GenericParameters {
    pub fn is_effect_row(&self, name: &str) -> bool {
        self.effect_rows.contains(name)
    }

    pub fn is_lifetime(&self, name: &str) -> bool {
        self.lifetimes.contains(name)
    }

    pub fn const_kind(&self, name: &str) -> Option<ConstKind> {
        self.consts
            .iter()
            .find_map(|(candidate, kind)| (candidate == name).then_some(*kind))
    }

    pub fn kind(&self, name: &str) -> GenericKind {
        if self.is_effect_row(name) {
            GenericKind::EffectRow
        } else if self.is_lifetime(name) {
            GenericKind::Lifetime
        } else if let Some(kind) = self.const_kind(name) {
            GenericKind::Const(kind)
        } else {
            GenericKind::Type
        }
    }

    pub fn kinds(&self) -> Vec<GenericKind> {
        self.names.iter().map(|name| self.kind(name)).collect()
    }
}

impl std::ops::Deref for GenericParameters {
    type Target = [String];

    fn deref(&self) -> &Self::Target {
        &self.names
    }
}

impl<const N: usize> PartialEq<[&str; N]> for GenericParameters {
    fn eq(&self, other: &[&str; N]) -> bool {
        self.names
            .iter()
            .map(String::as_str)
            .eq(other.iter().copied())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HeaderType {
    Path(Vec<String>),
    Application(Box<HeaderType>, Vec<HeaderGenericArgument>),
    /// An associated type selected through an explicit trait relation.  The
    /// angle-bracket form avoids treating a qualified path as either a module
    /// path or an associated item before its receiver has been elaborated.
    ///
    /// Canonical spelling: `<Subject as Trait<Args>>::Item`.
    Projection {
        subject: Box<HeaderType>,
        trait_path: Vec<String>,
        trait_arguments: Vec<HeaderGenericArgument>,
        name: String,
        /// Arguments applied to the selected associated item.  These remain
        /// distinct from trait arguments so `<S as Trait<T>>::Item<U>`
        /// preserves the complete projection identity through elaboration.
        item_arguments: Vec<HeaderGenericArgument>,
    },
    Tuple(Vec<HeaderType>),
    FixedArray {
        element: Box<HeaderType>,
        length: Box<HeaderStructuralConst>,
    },
    Callable {
        safety: Safety,
        /// Lifetimes quantified by this callable type.  These bind only the
        /// parameter/result tree of this type, not its surrounding declaration.
        /// Keeping the binder on the syntax node gives `for<'a> (&'a T) -> ...`
        /// a real lexical scope instead of accidentally reusing an outer
        /// declaration lifetime.
        lifetime_binders: Vec<String>,
        parameters: Vec<HeaderType>,
        result: Box<HeaderType>,
        /// The callable contract's outward effect row.  Callable types are
        /// semantic contracts, not merely parameter/result arrows: leaving
        /// this at the implicit empty row would let a transparent alias erase
        /// authority required by an indirect call.
        effects: EffectRowHeader,
    },
    Reference {
        unique: bool,
        /// The source lifetime attached to this reference, when one was
        /// written.  Elision stays explicit as `None` until elaboration gives
        /// it the canonical `Lifetime::Elided` identity.
        lifetime: Option<String>,
        referent: Box<HeaderType>,
    },
    RawPointer {
        mutability: PointerMutability,
        pointee: Box<HeaderType>,
    },
    Never,
    Recovered,
}

/// An explicitly supplied nominal generic argument.  Structural constants are
/// kept distinct from source types before elaboration, preventing value syntax
/// from entering the type namespace by accident.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HeaderGenericArgument {
    Type(HeaderType),
    /// An associated-item equality attached to a trait reference, such as
    /// `Fn<(), Output = Result>`.  This is deliberately not represented as a
    /// positional type argument: the item name and its own generic arguments
    /// are part of the projection identity that a later signature phase must
    /// retain.
    AssociatedTypeBinding {
        name: String,
        item_arguments: Vec<HeaderGenericArgument>,
        value: Box<HeaderType>,
    },
    /// The row-kinded sibling of an associated type equality, for example
    /// `Fn<(), Effects = {| io}>`.  It uses the same named-item grammar but
    /// must not be coerced through `HeaderType`.
    AssociatedEffectBinding {
        name: String,
        item_arguments: Vec<HeaderGenericArgument>,
        value: EffectRowHeader,
    },
    /// A source lifetime supplied to a region generic slot. It stays distinct
    /// from a path-shaped type until the referenced declaration establishes
    /// the slot kind.
    Lifetime(String),
    /// An explicit effect-row term supplied to an `EffectRow` slot. The row
    /// retains source paths and its optional tail until signature elaboration
    /// resolves named effects and declaration binders.
    EffectRow(EffectRowHeader),
    /// An integer token awaiting the referenced declaration's const kind.
    /// Retaining the token avoids checking a wide or signed value as u32.
    Integer(String),
    /// An integer const expression whose operands may include declared const
    /// binders. It remains source-shaped until the target generic slot has
    /// established the required integer kind.
    StructuralConst(HeaderStructuralConst),
    /// A structural quantity interval supplied to a `Quantity` const slot.
    /// Keeping this distinct from `HeaderType` makes the source kind boundary
    /// explicit before signature elaboration.
    Quantity(Quantity),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderParameter {
    pub name: String,
    pub ty: HeaderType,
    pub span: Span,
}

/// A field in a nominal layout retains its source visibility. Elaboration
/// resolves private/restricted scopes to declaring-module capabilities.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NominalFieldHeader {
    pub name: String,
    pub ty: HeaderType,
    pub visibility: Visibility,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallableHeader {
    pub safety: Safety,
    pub generics: GenericParameters,
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
    /// Row-polymorphic tails are resolved only against a binder explicitly
    /// declared with the `EffectRow` kind; ordinary generic binders never
    /// enter this namespace.
    pub tails: Vec<String>,
}

/// A trait reference retains source-shaped generic arguments until interface
/// elaboration resolves the trait path to its stable declaration identity.
/// This includes structural constant arguments: `Sized<7>` must not be
/// coerced through the type namespace before its binder kind is known.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitRefHeader {
    pub path: Vec<String>,
    pub arguments: Vec<HeaderGenericArgument>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhereBoundHeader {
    /// A universal binder belongs to the entire predicate, including the
    /// relation's arguments and associated equalities, not just its subject.
    /// It is distinct from declaration generics and callable-type binders.
    pub universal: Option<GenericParameters>,
    pub predicate: PredicateHeader,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PredicateHeader {
    Trait { subject: HeaderType, relation: TraitRefHeader },
    TypeOutlives { subject: HeaderType, lifetime: String },
    RegionOutlives { longer: String, shorter: String },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedTypeHeader {
    pub name: String,
    pub generics: GenericParameters,
    /// `type Output: EffectRow;` declares an associated effect row rather
    /// than an ordinary associated type.
    pub effect_row: bool,
    pub bounds: Vec<TraitRefHeader>,
    pub where_bounds: Vec<WhereBoundHeader>,
    /// A value-type fallback used when a positive implementation omits this
    /// associated item.  The parser retains it in the trait declaration so
    /// signature elaboration can resolve its outer and item binders before
    /// any implementation is selected.
    pub default: Option<HeaderType>,
    /// The row-kinded counterpart of [`Self::default`].  It is separate from
    /// `HeaderType` so an effect row can never accidentally enter a value-type
    /// projection or layout boundary.
    pub effect_row_default: Option<EffectRowHeader>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedTypeDefinitionHeader {
    pub name: String,
    pub generics: GenericParameters,
    pub where_bounds: Vec<WhereBoundHeader>,
    pub value: HeaderType,
    /// An implementation-side associated effect row uses a row literal, for
    /// example `type Effects = {Ask, Trace};`, rather than a value type.
    pub effect_row_value: Option<EffectRowHeader>,
    pub span: Span,
}

/// A structural constant selected from a trait implementation. Associated
/// constants deliberately carry their closed value kind in the interface:
/// unlike ordinary constants, they participate in trait evidence and generic
/// identity without becoming value-level declarations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedConstHeader {
    pub name: String,
    pub kind: ConstKind,
    /// A declaration default is selected only when the chosen implementation
    /// leaves this item absent. Keeping it source-shaped preserves generic
    /// occurrences until the trait header's binders have been elaborated.
    pub default: Option<HeaderStructuralConst>,
    pub span: Span,
}

/// The intentionally closed source language for associated structural
/// constants. A path is accepted only for a declared const binder; interface
/// elaboration rejects ordinary paths rather than accidentally treating them
/// as runtime constant references.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HeaderStructuralConst {
    Integer(String),
    Quantity(Quantity),
    Generic(String),
    IntegerExpression(HeaderIntegerExpr),
    /// A delayed associated structural-constant selection. This is kept in
    /// the header rather than parsed as a runtime expression so interface
    /// elaboration can retain its mixed-kind trait evidence for later
    /// concrete normalization.
    Projection(HeaderType),
}

/// Source-shaped structural arithmetic.  Names are intentionally preserved
/// until elaboration maps them to owner-local generic slots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HeaderIntegerExpr {
    Literal(String),
    Param(String),
    Neg(Box<Self>),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Div(Box<Self>, Box<Self>),
    Rem(Box<Self>, Box<Self>),
}

impl HeaderIntegerExpr {
    /// Select the declared scalar before literal range checks or arithmetic.
    /// Lookup is owned by the lexical elaborator; this syntax helper cannot
    /// resolve runtime values or manufacture generic-slot identities.
    pub(crate) fn elaborate(
        &self,
        scalar: crate::types::ScalarType,
        lookup: &mut dyn FnMut(&str) -> Result<crate::types::IntegerConstExpr, crate::types::StructuralConstError>,
    ) -> Result<crate::types::IntegerConstExpr, crate::types::StructuralConstError> {
        use crate::types::{IntegerConst, IntegerConstExpr as Expr, StructuralConstError as Error};
        use crate::types::integer_const::IntegerConstOp as Op;
        fn walk(
            source: &HeaderIntegerExpr,
            scalar: crate::types::ScalarType,
            lookup: &mut dyn FnMut(&str) -> Result<Expr, Error>,
            budget: &mut u32,
            depth: u32,
        ) -> Result<Expr, Error> {
            if *budget == 0 || depth >= 128 { return Err(Error::ResourceLimit); }
            *budget -= 1;
            let (op, left, right) = match source {
                HeaderIntegerExpr::Literal(token) => return IntegerConst::from_literal(scalar, token, false, 64).map(Expr::Literal),
                HeaderIntegerExpr::Param(name) => {
                    let value = lookup(name)?;
                    if value.scalar()? != scalar { return Err(Error::KindMismatch); }
                    return Ok(value);
                }
                HeaderIntegerExpr::Neg(value) => {
                    if let HeaderIntegerExpr::Literal(token) = value.as_ref() {
                        return IntegerConst::from_literal(scalar, token, true, 64).map(Expr::Literal);
                    }
                    return Ok(Expr::Neg(Box::new(walk(value, scalar, lookup, budget, depth + 1)?)));
                }
                HeaderIntegerExpr::Add(left, right) => (Op::Add, left, right),
                HeaderIntegerExpr::Sub(left, right) => (Op::Sub, left, right),
                HeaderIntegerExpr::Mul(left, right) => (Op::Mul, left, right),
                HeaderIntegerExpr::Div(left, right) => (Op::Div, left, right),
                HeaderIntegerExpr::Rem(left, right) => (Op::Rem, left, right),
            };
            Ok(Expr::Binary {
                op,
                left: Box::new(walk(left, scalar, lookup, budget, depth + 1)?),
                right: Box::new(walk(right, scalar, lookup, budget, depth + 1)?),
            })
        }
        walk(self, scalar, lookup, &mut 1024, 0)?.normalized()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedConstDefinitionHeader {
    pub name: String,
    pub value: HeaderStructuralConst,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplementationMethodHeader {
    pub name: String,
    pub visibility: Visibility,
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
    pub safety: Safety,
    /// Auto traits use structural, coinductive selection when no explicit
    /// implementation decides the goal.
    pub auto_trait: bool,
    pub generics: GenericParameters,
    pub supertraits: Vec<TraitRefHeader>,
    pub associated_types: Vec<AssociatedTypeHeader>,
    pub associated_consts: Vec<AssociatedConstHeader>,
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
    pub safety: Safety,
    pub generics: GenericParameters,
    pub negative: bool,
    pub relation: TraitRefHeader,
    pub self_ty: HeaderType,
    pub where_bounds: Vec<WhereBoundHeader>,
    pub associated_types: Vec<AssociatedTypeDefinitionHeader>,
    pub associated_consts: Vec<AssociatedConstDefinitionHeader>,
    pub methods: Vec<ImplementationMethodHeader>,
}

/// Inherent members are direct associated functions, not trait evidence or
/// value aliases. Interface collection gives each member its own definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InherentImplementationHeader {
    pub generics: GenericParameters,
    pub self_ty: HeaderType,
    pub where_bounds: Vec<WhereBoundHeader>,
    pub methods: Vec<ImplementationMethodHeader>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InherentMethodHeader {
    pub self_ty: HeaderType,
    pub impl_generics: u32,
    /// Block binders precede method binders in the ordinary callable ABI.
    pub signature: CallableHeader,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectOperationHeader {
    pub name: String,
    pub generics: GenericParameters,
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
    pub generics: GenericParameters,
    pub operations: Vec<EffectOperationHeader>,
}

/// Field declarations are interface facts for records and record-like enum
/// payloads. They use the same type grammar and source spans as callable
/// parameters, but are deliberately separate from body-local expressions.
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
    TupleStruct(Vec<NominalFieldHeader>),
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
    /// Explicit ordinary value path, resolved in the declaring module.
    /// Absence retains the same-named binding shorthand.
    pub target: Option<Vec<String>>,
}

/// A single explicit import binding.  Imports are declaration-header facts:
/// they are available to all body resolution without loading any body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportHeader {
    pub bindings: Vec<ImportBindingHeader>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportBindingHeader {
    /// The module path for a glob binding and the full declaration path for
    /// an explicit binding.  A glob is deliberately a first-class header
    /// fact, rather than an early parser expansion: only the package-wide
    /// definition index knows which names are visible at the import edge.
    pub path: Vec<String>,
    pub alias: Option<String>,
    pub glob: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParsedHeader {
    Function(CallableHeader),
    TypeAlias {
        generics: GenericParameters,
        target: HeaderType,
    },
    Constant {
        ty: Option<HeaderType>,
    },
    /// A source-level value forwarding contract. Paths are retained until the
    /// complete package index can resolve visibility and alias cycles.
    ValueAlias {
        name: Vec<String>,
        target: Vec<String>,
    },
    /// A frozen top-level value initializer. Unlike a forwarding alias, the
    /// expression after `=` is evaluated exactly once by the generated VM
    /// initializer function; its type is inferred and frozen before ordinary
    /// callable bodies are elaborated.
    ValueInitializer {
        name: Vec<String>,
    },
    Import(ImportHeader),
    Fixity(FixityHeader),
    Trait(TraitHeader),
    Implementation(ImplementationHeader),
    InherentImplementation(InherentImplementationHeader),
    InherentMethod(InherentMethodHeader),
    Effect(EffectHeader),
    Nominal {
        generics: GenericParameters,
        layout: NominalLayoutHeader,
        where_bounds: Vec<WhereBoundHeader>,
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
            operator_offset: 0,
            diagnostics: vec![],
            recovered: false,
        };
        parser.visibility();
        if shell.safety == Safety::Unsafe {
            parser.position += 1;
        }
        if shell.kind == DeclarationKind::HostImport {
            // Scanner froze `host CAP fn`; only `fn` and its ABI remain for
            // the ordinary callable parser.
            parser.position += 2;
        }
        if shell.auto_trait {
            parser.position += 1;
        }
        let keyword = parser.word().map(str::to_owned);
        // Explicit declarations consume their keyword here. Canonical bare
        // callables instead begin with the callable's own name, which the
        // shared callable parser must retain and consume itself.
        if shell.kind != DeclarationKind::Function || keyword.as_deref() == Some("fn") {
            parser.position += 1;
        }
        let header = match shell.kind {
            DeclarationKind::Function | DeclarationKind::HostImport => {
                let mut callable = parser.callable();
                callable.safety = shell.safety;
                ParsedHeader::Function(callable)
            }
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
            DeclarationKind::ValueAlias => {
                let name = parser.path();
                if !parser.operator("=") {
                    parser.error("G3220", "expected `=` in value alias");
                }
                // The scanner owns the initializer range so expression
                // parsing remains demand-driven. A range consisting of one
                // complete path is the established callable-forwarding form;
                // every other expression is an evaluated top-level value.
                let mut initializer = Parser {
                    lexed,
                    source,
                    tokens: shell
                        .body
                        .map(|range| significant(lexed, range))
                        .unwrap_or_default(),
                    position: 0,
                    operator_offset: 0,
                    diagnostics: vec![],
                    recovered: false,
                };
                let target = initializer.path();
                if !target.is_empty() && initializer.current().is_none() {
                    ParsedHeader::ValueAlias { name, target }
                } else {
                    // The expression is deliberately not parsed as header
                    // syntax. Its scanner-owned range is parsed once by the
                    // ordinary body frontend, where calls, constructors, and
                    // their argument contracts are retained in Typed Core.
                    ParsedHeader::ValueInitializer { name }
                }
            }
            DeclarationKind::Import => ParsedHeader::Import(parser.import()),
            DeclarationKind::Fixity => ParsedHeader::Fixity(parser.fixity(keyword.as_deref())),
            DeclarationKind::Struct | DeclarationKind::Enum => {
                parser.identifier();
                let generics = parser.generics();
                let where_bounds = parser.where_bounds();
                let mut layout_parser = Parser {
                    lexed,
                    source,
                    tokens: shell
                        .body
                        .map(|range| significant(lexed, range))
                        .unwrap_or_default(),
                    position: 0,
                    operator_offset: 0,
                    diagnostics: vec![],
                    recovered: false,
                };
                let layout = layout_parser.nominal_layout(shell.kind);
                parser.diagnostics.extend(layout_parser.diagnostics);
                parser.recovered |= layout_parser.recovered;
                ParsedHeader::Nominal { generics, layout, where_bounds }
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
                    operator_offset: 0,
                    diagnostics: vec![],
                    recovered: false,
                };
                let value = body_parser.trait_header(generics, supertraits, shell.auto_trait, shell.safety);
                parser.diagnostics.extend(body_parser.diagnostics);
                parser.recovered |= body_parser.recovered;
                ParsedHeader::Trait(value)
            }
            DeclarationKind::Implementation => {
                parser.implementation(shell.body, shell.safety, shell.visibility != Visibility::Private)
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
                    operator_offset: 0,
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
    // Header grammar can split adjacent type delimiters without changing
    // maximal-munch operator tokens used by body/fixity parsing.
    operator_offset: usize,
    diagnostics: Vec<HeaderDiagnostic>,
    recovered: bool,
}
impl Parser<'_> {
    fn visibility(&mut self) -> Visibility {
        crate::scanner::parse_visibility(self.lexed, self.source, &self.tokens, &mut self.position)
            .unwrap_or_else(|span| {
                self.recovered = true;
                self.diagnostics.push(HeaderDiagnostic { code: "G3280", span,
                    message: "expected `pub`, `pub(crate)`, or `pub(super)` visibility" });
                Visibility::Private
            })
    }
    fn trait_header(
        &mut self,
        generics: GenericParameters,
        supertraits: Vec<TraitRefHeader>,
        auto_trait: bool,
        safety: Safety,
    ) -> TraitHeader {
        let mut associated_types = vec![];
        let mut associated_consts = vec![];
        let mut methods = vec![];
        let mut names = BTreeSet::new();
        if !self.punctuation('{') {
            self.error("G3232", "expected `{` after trait declaration");
            return TraitHeader {
                safety,
                auto_trait,
                generics,
                supertraits,
                associated_types,
                associated_consts,
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
                let mut bounds = vec![];
                let effect_row = if self.punctuation(':') {
                    if self.word() == Some("EffectRow") {
                        self.position += 1;
                        true
                    } else {
                        loop {
                            bounds.push(self.trait_ref());
                            if !self.operator("+") { break; }
                        }
                        false
                    }
                } else {
                    false
                };
                let mut where_bounds = self.where_bounds();
                let (default, effect_row_default) = if self.operator("=") {
                    if effect_row {
                        let row = if self.at_punctuation('{') {
                            self.effect_row_literal()
                        } else {
                            EffectRowHeader { effects: vec![self.ty()], tails: Default::default() }
                        };
                        (None, Some(row))
                    } else {
                        (Some(self.ty()), None)
                    }
                } else {
                    (None, None)
                };
                where_bounds.extend(self.where_bounds());
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
                    bounds,
                    where_bounds,
                    default,
                    effect_row_default,
                    span: self.span(start, end),
                });
                continue;
            }
            if self.word() == Some("const") {
                self.position += 1;
                let name = self.identifier().unwrap_or_else(|| {
                    self.error("G3255", "expected associated constant name");
                    "<error>".into()
                });
                if !self.punctuation(':') {
                    self.error("G3256", "expected `:` after associated constant name");
                }
                let kind = match self.word() {
                    Some(name) if ConstKind::from_integer_name(name).is_some() => {
                        let kind = ConstKind::from_integer_name(name).unwrap();
                        self.position += 1;
                        kind
                    }
                    Some("Quantity") => {
                        self.position += 1;
                        ConstKind::Quantity
                    }
                    _ => {
                        self.error(
                            "G3257",
                            "associated constants must have an integer scalar or `Quantity` kind",
                        );
                        ConstKind::U32
                    }
                };
                let default = self.operator("=").then(|| self.structural_const_value());
                if !self.punctuation(';') {
                    self.error(
                        "G3258",
                        "expected `;` after associated constant declaration",
                    );
                    self.skip_to_item_end();
                }
                if !names.insert(name.clone()) {
                    self.error("G3237", "duplicate trait item name");
                }
                let end = self.previous().unwrap_or(start);
                associated_consts.push(AssociatedConstHeader {
                    name,
                    kind,
                    default,
                    span: self.span(start, end),
                });
                continue;
            }
            let safety = if self.word() == Some("unsafe") {
                self.position += 1;
                Safety::Unsafe
            } else {
                Safety::Safe
            };
            if self.word() == Some("fn") {
                self.position += 1;
            }
            let method_start = self.current().unwrap_or(start);
            let name = self.callable_member_name().unwrap_or_else(|| {
                self.error("G3233", "expected trait method name");
                "<error>".into()
            });
            let method_generics = self.generics();
            let parameters = self.callable_parameters();
            let result = self.callable_result();
            let method = CallableHeader {
                safety,
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
            safety,
            auto_trait,
            generics,
            supertraits,
            associated_types,
            associated_consts,
            methods,
        }
    }
    fn implementation(
        &mut self,
        body: Option<TokenRange>,
        safety: Safety,
        public: bool,
    ) -> ParsedHeader {
        let generics = self.generics();
        let negative = self.operator("!");
        let head_start = self.position;
        let head_operator_offset = self.operator_offset;
        let relation = self.trait_ref();
        let inherent = self.word() != Some("for");
        if inherent {
            self.position = head_start;
            self.operator_offset = head_operator_offset;
            if negative || safety == Safety::Unsafe || public {
                self.error("G3270", "inherent impl blocks cannot be negative, unsafe, or public; put visibility and safety on their functions");
            }
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
            operator_offset: 0,
            diagnostics: vec![],
            recovered: false,
        };
        let mut associated_types = vec![];
        let mut associated_consts = vec![];
        let mut methods = vec![];
        if body_parser.punctuation('{') {
            let mut names = BTreeSet::new();
            while body_parser.current().is_some() && !body_parser.at_punctuation('}') {
                let visibility = body_parser.visibility();
                if visibility != Visibility::Private && !inherent {
                    body_parser.error(
                        "G3271",
                        "trait implementation members inherit trait visibility",
                    );
                }
                if body_parser.word() != Some("type")
                    && body_parser.word() != Some("const")
                    && body_parser.word() != Some("fn")
                    && body_parser.word() != Some("unsafe")
                    && !body_parser.callable_member_ahead()
                {
                    body_parser.error("G3272", "expected an implementation member");
                    body_parser.skip_item_body();
                    continue;
                }
                if body_parser.word() == Some("const") {
                    let start = body_parser.current().unwrap();
                    body_parser.position += 1;
                    let name = body_parser.identifier().unwrap_or_else(|| {
                        body_parser.error("G3259", "expected associated constant definition name");
                        "<error>".into()
                    });
                    if !body_parser.operator("=") {
                        body_parser
                            .error("G3260", "expected `=` in associated constant definition");
                    }
                    let value = body_parser.structural_const_value();
                    if !body_parser.punctuation(';') {
                        body_parser
                            .error("G3261", "expected `;` after associated constant definition");
                        body_parser.skip_to_item_end();
                    }
                    if !names.insert(name.clone()) {
                        body_parser.error("G3245", "duplicate implementation item name");
                    }
                    let end = body_parser.previous().unwrap_or(start);
                    associated_consts.push(AssociatedConstDefinitionHeader {
                        name,
                        value,
                        span: body_parser.span(start, end),
                    });
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
                    let mut where_bounds = body_parser.where_bounds();
                    if !body_parser.operator("=") {
                        body_parser.error("G3243", "expected `=` in associated type definition");
                    }
                    let (value, effect_row_value) = if body_parser.at_punctuation('{') {
                        (
                            HeaderType::Recovered,
                            Some(body_parser.effect_row_literal()),
                        )
                    } else {
                        (body_parser.ty(), None)
                    };
                    where_bounds.extend(body_parser.where_bounds());
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
                        where_bounds,
                        value,
                        effect_row_value,
                        span: body_parser.span(start, end),
                    });
                    continue;
                }
                if matches!(body_parser.word(), Some("fn" | "unsafe")) || body_parser.callable_member_ahead() {
                    let start = body_parser.current().unwrap();
                    let safety = if body_parser.word() == Some("unsafe") {
                        body_parser.position += 1;
                        Safety::Unsafe
                    } else {
                        Safety::Safe
                    };
                    if body_parser.word() == Some("fn") {
                        body_parser.position += 1;
                    }
                    let name = body_parser.callable_member_name().unwrap_or_else(|| {
                        body_parser.error("G3242", "expected implementation method name");
                        "<error>".into()
                    });
                    let generics = body_parser.generics();
                    let parameters = body_parser.callable_parameters();
                    let result = body_parser.callable_result();
                    let signature = CallableHeader {
                        safety,
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
                        visibility,
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
        if inherent {
            if !associated_types.is_empty() || !associated_consts.is_empty() {
                self.error(
                    "G3273",
                    "inherent impl blocks currently contain functions only",
                );
            }
            return ParsedHeader::InherentImplementation(InherentImplementationHeader {
                generics,
                self_ty,
                where_bounds,
                methods,
            });
        }
        ParsedHeader::Implementation(ImplementationHeader {
            safety,
            generics,
            negative,
            relation,
            self_ty,
            where_bounds,
            associated_types,
            associated_consts,
            methods,
        })
    }
    fn effect_header(&mut self, generics: GenericParameters) -> EffectHeader {
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
            let resumption = self.quantity();
            let has_quantity = resumption.is_some();
            let resumption = resumption.unwrap_or(Quantity::ONCE);
            let name = self.identifier().unwrap_or_else(|| {
                self.error("G3249", "expected effect operation name");
                "<error>".into()
            });
            let operation_generics = self.generics();
            let parameters = self.operation_payloads();
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
            // The G1 source surface deliberately exposes only affine and
            // exact finite continuations.  The interval algebra remains more
            // general for inferred/derived use facts, but accepting a
            // deferred source interval would promise branch-sensitive
            // resumption semantics that this language version does not yet
            // specify or lower.
            if has_quantity
                && resumption != Quantity::AFFINE
                && resumption.upper != Some(resumption.lower)
            {
                self.error(
                    "G3254",
                    "source resumption quantity must be `[0,1]` or exact `[n,n]`",
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
    /// Operation payloads are positional types, not callable body binders.
    /// Keep their ordinal in the shared header representation; handler arms
    /// introduce their own names independently of these slots.
    fn operation_payloads(&mut self) -> Vec<HeaderParameter> {
        if !self.punctuation('(') {
            self.error("G3202", "expected operation payload list");
        }
        let mut parameters = Vec::new();
        while self.current().is_some() && !self.at_punctuation(')') {
            let start = self.current().unwrap();
            // Existing named operation headers use the same type grammar.
            // A qualified type path (`module::Type`) is not a named slot.
            let named = self.word().is_some()
                && self.tokens.get(self.position + 1).is_some_and(|index| {
                    self.lexed.tokens[*index].kind == TokenKind::Punctuation(':')
                })
                && !self.tokens.get(self.position + 2).is_some_and(|index| {
                    self.lexed.tokens[*index].kind == TokenKind::Punctuation(':')
                });
            let name = if named {
                let name = self.identifier().unwrap();
                self.punctuation(':');
                name
            } else {
                parameters.len().to_string()
            };
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
            self.error("G3204", "expected `)` after operation payloads");
        }
        parameters
    }

    fn callable_parameters(&mut self) -> Vec<HeaderParameter> {
        if !self.punctuation('(') {
            self.error("G3202", "expected callable parameter list");
        }
        let mut parameters = vec![];
        while self.current().is_some() && !self.at_punctuation(')') {
            let start = self.current().unwrap();
            // Canonical trait and implementation members permit the concise
            // borrowed receiver spelling `&self` / `&mut self`. It is still
            // frozen as an explicit `Self` reference in the interface, so
            // later trait instantiation never has to recover a receiver from
            // a parameter name.
            let (name, ty) = if self.operator("&") {
                let unique = self.word() == Some("mut");
                if unique {
                    self.position += 1;
                }
                let name = self.identifier().unwrap_or_else(|| {
                    self.error("G3203", "expected `self` after borrowed receiver");
                    "<error>".into()
                });
                if name != "self" {
                    self.error("G3203", "borrowed receiver must name `self`");
                }
                (
                    name,
                    HeaderType::Reference {
                        unique,
                        lifetime: None,
                        referent: Box::new(HeaderType::Path(vec!["Self".into()])),
                    },
                )
            } else {
                let name = self.identifier().unwrap_or_else(|| "<error>".into());
                if !self.punctuation(':') {
                    self.error("G3203", "expected `:` after parameter name");
                }
                let ty = self.ty();
                (name, ty)
            };
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
        let arguments = self.generic_arguments();
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
            let universal = if self.word() == Some("for") {
                self.position += 1;
                if !self.at_operator("<") {
                    self.error("G3334", "expected `<` after higher-ranked bound `for`");
                }
                let binders = self.generics();
                if binders.names.is_empty() {
                    self.error("G3334", "a higher-ranked bound requires at least one binder");
                }
                if !binders.defaults.is_empty() || !binders.const_defaults.is_empty() {
                    self.error("G3334", "universal binders cannot have defaults");
                }
                let mut seen = BTreeSet::new();
                if binders.names.iter().any(|name| !seen.insert(name)) {
                    self.error("G3334", "duplicate higher-ranked bound binder");
                }
                Some(binders)
            } else {
                None
            };
            let region_subject = self.word().filter(|word| word.starts_with('\'')).map(str::to_owned);
            let subject = if region_subject.is_some() {
                self.position += 1;
                HeaderType::Recovered
            } else { self.ty() };
            if !self.punctuation(':') {
                self.error("G3256", "expected `:` in where bound");
                break;
            }
            let predicate = if self.word().is_some_and(|word| word.starts_with('\'')) {
                let lifetime = self.identifier().unwrap();
                if let Some(longer) = region_subject {
                    PredicateHeader::RegionOutlives { longer, shorter: lifetime }
                } else {
                    PredicateHeader::TypeOutlives { subject, lifetime }
                }
            } else {
                if region_subject.is_some() {
                    self.error("G3335", "a region predicate requires an outlives lifetime");
                }
                PredicateHeader::Trait { subject, relation: self.trait_ref() }
            };
            let end = self.previous().unwrap_or(start);
            bounds.push(WhereBoundHeader {
                universal,
                predicate,
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
        let lower = self.structural_integer_expression(
            "G3257",
            "resumption quantity lower bound must be a non-negative integer",
            "G3265",
            "resumption quantity arithmetic overflowed or divided by zero",
        );
        if !self.punctuation(',') {
            self.error("G3258", "expected `,` between resumption quantity bounds");
        }
        let upper = if self.at_operator("*") || self.word() == Some("infinity") {
            self.position += 1;
            None
        } else {
            Some(self.structural_integer_expression(
                "G3259",
                "resumption quantity upper bound must be a non-negative integer or `*`",
                "G3265",
                "resumption quantity arithmetic overflowed or divided by zero",
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
                // Keep the existing u64 arithmetic domain for quantities and
                // closed structural expressions, but accept every integer
                // token spelling accepted by the lexer. The literal reader
                // itself retains u128 magnitudes for width-aware elaboration.
                crate::types::integer_const::IntegerConst::from_literal(
                    crate::types::ScalarType::U64,
                    self.text(index),
                    false,
                    64, // U64 is target-independent, not a host usize.
                )
                .map(|value| value.magnitude() as u64)
                .unwrap_or_else(|_| {
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
        if kind == DeclarationKind::Struct && self.punctuation('(') {
            let mut fields = vec![];
            while self.current().is_some() && !self.at_punctuation(')') {
                let start = self.current().unwrap();
                let visibility = self.visibility();
                let ty = self.ty();
                fields.push(NominalFieldHeader {
                    name: fields.len().to_string(), ty, visibility,
                    span: self.span(start, self.previous().unwrap_or(start)),
                });
                if !self.punctuation(',') { break; }
            }
            if !self.punctuation(')') { self.error("G3281", "expected `)` after tuple-struct fields"); }
            if self.current().is_some() { self.error("G3222", "unexpected trailing token in tuple-struct declaration"); }
            return NominalLayoutHeader::TupleStruct(fields);
        }
        if !self.punctuation('{') {
            self.error("G3220", "expected nominal declaration body");
            return NominalLayoutHeader::Opaque;
        }
        let layout = match kind {
            DeclarationKind::Struct => NominalLayoutHeader::Struct(self.nominal_fields('}', Visibility::Private)),
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
    fn nominal_fields(&mut self, closing: char, default_visibility: Visibility) -> Vec<NominalFieldHeader> {
        let mut fields = vec![];
        let mut names = BTreeSet::new();
        while self.current().is_some() && !self.at_punctuation(closing) {
            let start = self.current().unwrap();
            // `private` records authority on the frozen nominal layout. Its
            // policy is enforced later at each structural access boundary.
            // `public` and `private` remain legal field names. They are a
            // visibility modifier only when another field identifier follows;
            // `public: Bool` is a field named `public`, not a modifier plus a
            // malformed `Bool` field.
            let modifier = !self.tokens.get(self.position + 1).is_some_and(|next|
                self.lexed.tokens[*next].kind == TokenKind::Punctuation(':'));
            let visibility = match (modifier, self.word()) {
                (true, Some("pub")) => self.visibility(),
                (true, Some("private")) => { self.position += 1; Visibility::Private }
                (true, Some("public")) => { self.position += 1; Visibility::Public }
                _ => default_visibility,
            };
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
            fields.push(NominalFieldHeader {
                name,
                ty,
                visibility,
                span: Span {
                    file: self.lexed.file,
                    start: self.lexed.tokens[start].span.start,
                    end: self.lexed.tokens[end].span.end,
                },
            });
            if !self.punctuation(',')
                && !self.at_punctuation(closing)
                && !self.line_break_before_current()
            {
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
                // Enum payloads are exposed by their closed variants; unlike
                // nominal record representation they inherit that surface.
                let fields = self.nominal_fields('}', Visibility::Public);
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
            if !self.punctuation(',')
                && !self.at_punctuation('}')
                && !self.line_break_before_current()
            {
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
        let result = self.callable_result();
        let effects = self.effect_row_annotation();
        let where_bounds = self.where_bounds();
        CallableHeader {
            safety: Safety::Safe,
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
        if !self.at_punctuation('{') {
            return EffectRowHeader {
                effects: vec![self.ty()],
                tails: Default::default(),
            };
        }
        self.effect_row_literal()
    }
    /// A canonical callable may spell its unit result as `-> { body }`.
    /// The brace is the already-scanned body delimiter, not a malformed type;
    /// retain the same `None => Unit` interface representation as an omitted
    /// result annotation.
    fn callable_result(&mut self) -> Option<HeaderType> {
        if !self.operator("->") {
            return None;
        }
        if self.current().is_none()
            || self.at_punctuation('{')
            || self.word() == Some("where")
            || self.at_operator("/")
            || self.at_punctuation(';')
        {
            None
        } else {
            Some(self.ty())
        }
    }
    fn effect_row_literal(&mut self) -> EffectRowHeader {
        if !self.punctuation('{') {
            self.error("G3264", "expected `{` before effect row");
            return EffectRowHeader::default();
        }
        let mut effects = vec![];
        let mut tails = vec![];
        let mut in_union = false;
        while self.current().is_some() && !self.at_punctuation('}') {
            if self.operator("|") {
                if in_union {
                    self.error("G3262", "only one `|` is permitted in an effect row");
                }
                in_union = true;
                if self.at_punctuation('}') {
                    self.error("G3262", "expected effect-row term after `|`");
                    break;
                }
            }
            if in_union && !self.at_operator("<") {
                let next = self.identifier();
                if next.is_none() {
                    self.error("G3262", "expected row parameter or associated effect-row projection");
                    break;
                }
                tails.extend(next);
            } else {
                effects.push(self.ty());
            }
            if !self.punctuation(',') {
                if !self.at_punctuation('}') && !self.at_operator("|") {
                    self.error("G3263", "expected `,` between effect-row members");
                    break;
                }
                continue;
            }
        }
        if !self.punctuation('}') {
            self.error("G3264", "expected `}` after effect row");
        }
        tails.sort();
        tails.dedup();
        EffectRowHeader { effects, tails }
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
        let target = if self.operator("=") {
            let mut path = vec![];
            loop {
                let Some(name) = self.identifier() else {
                    self.error("G3214", "expected an ordinary declaration path after fixity `=`");
                    break;
                };
                path.push(name);
                if !self.path_separator() { break; }
            }
            Some(path)
        } else { None };
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
            target,
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
        // `use path::{*, name}` is useful at facade boundaries.  The star is
        // a selector in its own right, not an identifier, so recognize it
        // before requiring the first path segment for this recursive group.
        if self.at_operator("*") {
            self.position += 1;
            if prefix.is_empty() {
                self.error("G3216", "expected an imported module before `::*`");
                return vec![];
            }
            return vec![ImportBindingHeader {
                path: prefix,
                alias: None,
                glob: true,
            }];
        }
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
                return vec![ImportBindingHeader {
                    path,
                    alias: None,
                    glob: true,
                }];
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
        vec![ImportBindingHeader {
            path,
            alias,
            glob: false,
        }]
    }
    fn generics(&mut self) -> GenericParameters {
        if !self.operator("<") {
            return GenericParameters::default();
        }
        let mut generics = GenericParameters::default();
        let mut saw_default = false;
        while self.current().is_some() && !self.at_operator(">") {
            let explicit_const = self.word() == Some("const");
            if explicit_const { self.position += 1; }
            if let Some(name) = self.identifier() {
                let is_lifetime = name.starts_with('\'');
                let kind = if self.punctuation(':') {
                    if is_lifetime {
                        self.error("G3205", "lifetime binders cannot declare a kind");
                        None
                    } else {
                        match self.word() {
                            Some("EffectRow") => {
                                self.position += 1;
                                Some(GenericKind::EffectRow)
                            }
                            Some(name) if ConstKind::from_integer_name(name).is_some() => {
                                let kind = ConstKind::from_integer_name(name).unwrap();
                                self.position += 1;
                                Some(GenericKind::Const(kind))
                            }
                            Some("Quantity") => {
                                self.position += 1;
                                Some(GenericKind::Const(ConstKind::Quantity))
                            }
                            _ => {
                                self.error(
                                    "G3205",
                                    "expected `EffectRow`, an integer scalar, or `Quantity` after generic kind `:`",
                                );
                                None
                            }
                        }
                    }
                } else {
                    None
                };
                if explicit_const && !matches!(kind, Some(GenericKind::Const(_))) {
                    self.error("G3205", "an explicit const binder requires a const kind");
                }
                if kind == Some(GenericKind::EffectRow) {
                    generics.effect_rows.insert(name.clone());
                }
                if let Some(GenericKind::Const(kind)) = kind {
                    generics.consts.insert((name.clone(), kind));
                }
                let has_default = self.operator("=");
                if !has_default && saw_default {
                    self.error(
                        "G3205",
                        "generic defaults must be trailing declaration binders",
                    );
                }
                if has_default {
                    saw_default = true;
                    if matches!(kind, Some(GenericKind::Const(_))) {
                        let default = self.structural_const_value();
                        generics.const_defaults.insert(name.clone(), default);
                    } else {
                        let default = if is_lifetime {
                            HeaderGenericArgument::Lifetime(self.identifier().unwrap_or_else(|| {
                                self.error("G3205", "expected lifetime default");
                                "'_".into()
                            }))
                        } else if kind == Some(GenericKind::EffectRow) && self.at_punctuation('{') {
                            HeaderGenericArgument::EffectRow(self.effect_row_literal())
                        } else {
                            HeaderGenericArgument::Type(self.ty())
                        };
                        generics.defaults.insert(name.clone(), default);
                    }
                }
                if is_lifetime {
                    generics.lifetimes.insert(name.clone());
                }
                generics.names.push(name);
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
        generics
    }
    fn ty(&mut self) -> HeaderType {
        if self.word() == Some("unsafe") {
            self.position += 1;
            if self.word() == Some("fn") {
                self.position += 1;
            }
            return match self.ty() {
                HeaderType::Callable {
                    lifetime_binders,
                    parameters,
                    result,
                    effects,
                    ..
                } => HeaderType::Callable {
                    safety: Safety::Unsafe,
                    lifetime_binders,
                    parameters,
                    result,
                    effects,
                },
                _ => {
                    self.error("G3330", "`unsafe` must qualify a callable type");
                    HeaderType::Recovered
                }
            };
        }
        // Higher-ranked callable types use an explicit lifetime-only binder
        // prefix: `for<'a, 'b> (&'a T, &'b U) -> R`.  This is deliberately
        // parsed here rather than as declaration generics: the binders are
        // lexical to this one type occurrence.
        if self.word() == Some("for") {
            self.position += 1;
            let binders = self.generics();
            let mut lifetime_binders = vec![];
            for name in &binders.names {
                if binders.is_lifetime(name) {
                    lifetime_binders.push(name.clone());
                } else {
                    self.error("G3323", "higher-ranked binders must be lifetimes");
                }
            }
            let body = self.ty();
            return match body {
                HeaderType::Callable {
                    safety,
                    lifetime_binders: nested,
                    parameters,
                    result,
                    effects,
                } => HeaderType::Callable {
                    safety,
                    lifetime_binders: lifetime_binders.into_iter().chain(nested).collect(),
                    parameters,
                    result,
                    effects,
                },
                _ => {
                    self.error(
                        "G3325",
                        "a higher-ranked binder must qualify a callable type",
                    );
                    HeaderType::Recovered
                }
            };
        }
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
            let trait_arguments = self.generic_arguments();
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
            let item_arguments = self.generic_arguments();
            return HeaderType::Projection {
                subject: Box::new(subject),
                trait_path,
                trait_arguments,
                name,
                item_arguments,
            };
        }
        if self.operator("!") {
            return HeaderType::Never;
        }
        if self.operator("*") {
            let mutability = match self.word() {
                Some("const") => PointerMutability::Const,
                Some("mut") => PointerMutability::Mut,
                _ => {
                    self.error("G3327", "raw pointer types require `*const T` or `*mut T`");
                    return HeaderType::Recovered;
                }
            };
            self.position += 1;
            return HeaderType::RawPointer {
                mutability,
                pointee: Box::new(self.ty()),
            };
        }
        if self.operator("&") {
            let lifetime = if self.word().is_some_and(|name| name.starts_with('\'')) {
                self.identifier()
            } else {
                None
            };
            let unique = self.word() == Some("mut");
            if unique {
                self.position += 1;
            }
            return HeaderType::Reference {
                unique,
                lifetime,
                referent: Box::new(self.ty()),
            };
        }
        if self.punctuation('[') {
            let element = self.ty();
            if !self.punctuation(';') {
                self.error("G3330", "expected `;` between fixed array element and length");
            }
            let length = if self.at_operator("<") { self.structural_const_value() }
                else { self.structural_const_expression("G3330", "expected a usize array length") };
            if !self.punctuation(']') {
                self.error("G3330", "expected `]` after fixed array length");
            }
            return HeaderType::FixedArray { element: Box::new(element), length: Box::new(length) };
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
                let result = self.ty();
                return HeaderType::Callable {
                    safety: Safety::Safe,
                    lifetime_binders: vec![],
                    parameters: values,
                    result: Box::new(result),
                    effects: self.effect_row_annotation(),
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
            let arguments = self.generic_arguments();
            value = HeaderType::Application(Box::new(value), arguments);
        }
        value
    }
    fn generic_arguments(&mut self) -> Vec<HeaderGenericArgument> {
        if !self.operator("<") {
            return vec![];
        }
        let mut arguments = vec![];
        while self.current().is_some() && !self.at_operator(">") {
            if self.associated_type_binding_ahead() {
                let name = self
                    .identifier()
                    .expect("binding lookahead requires an identifier");
                let item_arguments = self.generic_arguments();
                if !self.operator("=") {
                    self.error("G3229", "expected `=` after associated type binding name");
                }
                if self.at_punctuation('{') {
                    arguments.push(HeaderGenericArgument::AssociatedEffectBinding {
                        name,
                        item_arguments,
                        value: self.effect_row_literal(),
                    });
                } else {
                    arguments.push(HeaderGenericArgument::AssociatedTypeBinding {
                        name,
                        item_arguments,
                        value: Box::new(self.ty()),
                    });
                }
            } else if self.at_punctuation('{') {
                arguments.push(HeaderGenericArgument::EffectRow(self.effect_row_literal()));
            } else if self.word().is_some_and(|name| name.starts_with('\'')) {
                arguments.push(HeaderGenericArgument::Lifetime(
                    self.identifier().expect("checked lifetime token"),
                ));
            } else if self.at_punctuation('[') && !self.fixed_array_ahead() {
                arguments.push(HeaderGenericArgument::Quantity(
                    self.structural_quantity_argument(),
                ));
            } else if self.starts_symbolic_structural_u32_expression() {
                let value = self.structural_const_expression("G3222", "malformed structural integer generic argument");
                arguments.push(match value {
                    HeaderStructuralConst::Integer(token) => HeaderGenericArgument::Integer(token),
                    value => HeaderGenericArgument::StructuralConst(value),
                });
            } else {
                arguments.push(HeaderGenericArgument::Type(self.ty()));
            }
            if !self.punctuation(',') {
                break;
            }
        }
        if !self.operator(">") {
            self.error("G3208", "expected `>` after generic arguments");
        }
        arguments
    }

    /// Distinguish `Output = T` (and the GAT form `Item<A> = T`) from a
    /// positional path argument without speculatively consuming source.  The
    /// scanner has already balanced declaration delimiters, so this small
    /// token walk is deterministic and leaves ordinary nested applications
    /// under `ty()`.
    fn associated_type_binding_ahead(&self) -> bool {
        let Some(current) = self.current() else {
            return false;
        };
        if self.lexed.tokens[current].kind != TokenKind::Identifier {
            return false;
        }
        let mut offset = self.position + 1;
        if self
            .tokens
            .get(offset)
            .is_some_and(|token| self.at_operator_at(*token, "="))
        {
            return true;
        }
        if !self
            .tokens
            .get(offset)
            .is_some_and(|token| self.at_operator_at(*token, "<"))
        {
            return false;
        }
        let mut depth = 0_u32;
        while let Some(token) = self.tokens.get(offset) {
            if self.at_operator_at(*token, "<") {
                depth += 1;
            } else if self.at_operator_at(*token, ">") {
                depth -= 1;
                if depth == 0 {
                    if self.text(*token).strip_prefix('>').is_some_and(|suffix|
                        Self::operator_starts_expected(suffix, "=")) {
                        return true;
                    }
                    return self
                        .tokens
                        .get(offset + 1)
                        .is_some_and(|next| self.at_operator_at(*next, "="));
                }
            }
            offset += 1;
        }
        false
    }
    fn fixed_array_ahead(&self) -> bool {
        let mut depth = 0;
        for &index in &self.tokens[self.position..] {
            match self.lexed.tokens[index].kind {
                TokenKind::Punctuation('[' | '(' | '{') => depth += 1,
                TokenKind::Punctuation(']' | ')' | '}') => {
                    depth -= 1;
                    if depth == 0 { return false; }
                }
                TokenKind::Punctuation(';') if depth == 1 => return true,
                _ => {}
            }
        }
        false
    }
    fn structural_quantity_argument(&mut self) -> Quantity {
        debug_assert!(self.at_punctuation('['));
        self.position += 1;
        let lower = self.structural_integer_expression(
            "G3223",
            "structural quantity lower bound must be a non-negative integer",
            "G3228",
            "structural constant arithmetic overflowed or divided by zero",
        );
        if !self.punctuation(',') {
            self.error("G3224", "expected `,` between structural quantity bounds");
        }
        let upper = if self.at_operator("*") || self.word() == Some("infinity") {
            self.position += 1;
            None
        } else {
            Some(self.structural_integer_expression(
                "G3225",
                "structural quantity upper bound must be a non-negative integer or `*`",
                "G3228",
                "structural constant arithmetic overflowed or divided by zero",
            ))
        };
        if !self.punctuation(']') {
            self.error("G3226", "expected `]` after structural quantity argument");
        }
        match Quantity::new(lower, upper) {
            Ok(value) => value,
            Err(_) => {
                self.error(
                    "G3227",
                    "structural quantity lower bound exceeds upper bound",
                );
                Quantity::ONCE
            }
        }
    }

    fn structural_const_value(&mut self) -> HeaderStructuralConst {
        if self.at_punctuation('[') {
            return HeaderStructuralConst::Quantity(self.structural_quantity_argument());
        }
        if self.at_operator("<") {
            return HeaderStructuralConst::Projection(self.ty());
        }
        if self.starts_symbolic_structural_u32_expression() {
            return self
                .structural_const_expression("G3262", "malformed structural integer constant");
        }
        match self.identifier() {
            Some(name) => HeaderStructuralConst::Generic(name),
            None => {
                self.error("G3264", "expected a structural associated constant value");
                HeaderStructuralConst::Integer("0".into())
            }
        }
    }

    /// A bare path remains syntactically ambiguous between a type and a const
    /// binder until signature elaboration knows the target slot.  An arithmetic
    /// operator removes that ambiguity, letting the header retain a symbolic
    /// const term without pretending it is a type application.
    fn starts_symbolic_structural_u32_expression(&self) -> bool {
        let Some(index) = self.current() else {
            return false;
        };
        let token = &self.lexed.tokens[index];
        if token.kind == TokenKind::Integer || self.at_operator("-") {
            return true;
        }
        if token.kind == TokenKind::Punctuation('(') {
            // A parenthesized arithmetic stream cannot be a source type: a
            // normal tuple/callable type has commas or an arrow, never one of
            // these structural operators.  Keep parenthesized `N + 1` in the
            // const parser while leaving ordinary `(T, U)` syntax untouched.
            let mut depth = 1;
            let mut arithmetic = false;
            for next in &self.tokens[self.position + 1..] {
                let token = &self.lexed.tokens[*next];
                match token.kind {
                    TokenKind::Punctuation('(') => depth += 1,
                    TokenKind::Punctuation(')') => {
                        depth -= 1;
                        if depth == 0 {
                            return arithmetic;
                        }
                    }
                    TokenKind::Punctuation(',') => return false,
                    _ => {}
                }
                arithmetic |= token.kind == TokenKind::Integer || matches!(
                    self.lexed.text(self.source, token),
                    "+" | "-" | "*" | "/" | "%"
                );
            }
            return false;
        }
        token.kind == TokenKind::Identifier
            && self.tokens.get(self.position + 1).is_some_and(|next| {
                matches!(
                    self.lexed.text(self.source, &self.lexed.tokens[*next]),
                    "+" | "-" | "*" | "/" | "%"
                )
            })
    }

    fn at_operator_at(&self, index: usize, value: &str) -> bool {
        self.lexed.tokens[index].kind == TokenKind::Operator
            && Self::operator_starts_expected(self.lexed.text(self.source, &self.lexed.tokens[index]), value)
    }

    fn structural_const_expression(
        &mut self,
        value_code: &'static str,
        value_message: &'static str,
    ) -> HeaderStructuralConst {
        match self.structural_u32_expression(value_code, value_message) {
            Ok(HeaderIntegerExpr::Literal(value)) => HeaderStructuralConst::Integer(value),
            Ok(value) => HeaderStructuralConst::IntegerExpression(value),
            Err(()) => {
                self.error(value_code, value_message);
                HeaderStructuralConst::Integer("0".into())
            }
        }
    }

    fn structural_u32_expression(
        &mut self,
        value_code: &'static str,
        value_message: &'static str,
    ) -> Result<HeaderIntegerExpr, ()> {
        let mut value = self.structural_u32_product(value_code, value_message)?;
        while let Some(operator) = self
            .at_operator("+")
            .then_some('+')
            .or_else(|| self.at_operator("-").then_some('-'))
        {
            self.position += 1;
            let right = self.structural_u32_product(value_code, value_message)?;
            value = match operator {
                '+' => HeaderIntegerExpr::Add(Box::new(value), Box::new(right)),
                '-' => HeaderIntegerExpr::Sub(Box::new(value), Box::new(right)),
                _ => unreachable!(),
            };
        }
        Ok(value)
    }

    fn structural_u32_product(
        &mut self,
        value_code: &'static str,
        value_message: &'static str,
    ) -> Result<HeaderIntegerExpr, ()> {
        let mut value = self.structural_u32_primary(value_code, value_message)?;
        while let Some(operator) = self
            .at_operator("*")
            .then_some('*')
            .or_else(|| self.at_operator("/").then_some('/'))
            .or_else(|| self.at_operator("%").then_some('%'))
        {
            self.position += 1;
            let right = self.structural_u32_primary(value_code, value_message)?;
            value = match operator {
                '*' => HeaderIntegerExpr::Mul(Box::new(value), Box::new(right)),
                '/' => HeaderIntegerExpr::Div(Box::new(value), Box::new(right)),
                '%' => HeaderIntegerExpr::Rem(Box::new(value), Box::new(right)),
                _ => unreachable!(),
            };
        }
        Ok(value)
    }

    fn structural_u32_primary(
        &mut self,
        value_code: &'static str,
        value_message: &'static str,
    ) -> Result<HeaderIntegerExpr, ()> {
        if self.operator("-") {
            return self.structural_u32_primary(value_code, value_message)
                .map(|value| HeaderIntegerExpr::Neg(Box::new(value)));
        }
        if self.punctuation('(') {
            let value = self.structural_u32_expression(value_code, value_message)?;
            if !self.punctuation(')') {
                self.error(value_code, "expected `)` in structural constant expression");
                return Err(());
            }
            return Ok(value);
        }
        if let Some(index) = self.current()
            && self.lexed.tokens[index].kind == TokenKind::Integer
        {
            self.position += 1;
            return Ok(HeaderIntegerExpr::Literal(self.text(index).to_owned()));
        }
        self.identifier()
            .map(HeaderIntegerExpr::Param)
            .ok_or_else(|| {
                self.error(value_code, value_message);
            })
    }
    /// Evaluate the intentionally tiny structural-integer language accepted
    /// inside generic arguments and quantity bounds.  This is not source
    /// execution: all operands are literals and the evaluator is bounded by
    /// the already-scanned declaration tokens.  Keeping normalization here
    /// means every later phase sees a single canonical `u32` or `Quantity`
    /// value suitable for type identity and hashing.
    fn structural_integer_expression(
        &mut self,
        value_code: &'static str,
        value_message: &'static str,
        arithmetic_code: &'static str,
        arithmetic_message: &'static str,
    ) -> u64 {
        let mut value = self.structural_integer_product(
            value_code,
            value_message,
            arithmetic_code,
            arithmetic_message,
        );
        while let Some(operator) = self
            .at_operator("+")
            .then_some('+')
            .or_else(|| self.at_operator("-").then_some('-'))
        {
            self.position += 1;
            let right = self.structural_integer_product(
                value_code,
                value_message,
                arithmetic_code,
                arithmetic_message,
            );
            value = match operator {
                '+' => value.checked_add(right),
                '-' => value.checked_sub(right),
                _ => unreachable!("only additive structural operators are accepted"),
            }
            .unwrap_or_else(|| {
                self.error(arithmetic_code, arithmetic_message);
                0
            });
        }
        value
    }
    fn structural_integer_product(
        &mut self,
        value_code: &'static str,
        value_message: &'static str,
        arithmetic_code: &'static str,
        arithmetic_message: &'static str,
    ) -> u64 {
        let mut value = self.structural_integer_primary(
            value_code,
            value_message,
            arithmetic_code,
            arithmetic_message,
        );
        while let Some(operator) = self
            .at_operator("*")
            .then_some('*')
            .or_else(|| self.at_operator("/").then_some('/'))
            .or_else(|| self.at_operator("%").then_some('%'))
        {
            self.position += 1;
            let right = self.structural_integer_primary(
                value_code,
                value_message,
                arithmetic_code,
                arithmetic_message,
            );
            value = match operator {
                '*' => value.checked_mul(right),
                '/' => value.checked_div(right),
                '%' => value.checked_rem(right),
                _ => unreachable!("only multiplicative structural operators are accepted"),
            }
            .unwrap_or_else(|| {
                self.error(arithmetic_code, arithmetic_message);
                0
            });
        }
        value
    }
    fn structural_integer_primary(
        &mut self,
        value_code: &'static str,
        value_message: &'static str,
        arithmetic_code: &'static str,
        arithmetic_message: &'static str,
    ) -> u64 {
        if self.punctuation('(') {
            let value = self.structural_integer_expression(
                value_code,
                value_message,
                arithmetic_code,
                arithmetic_message,
            );
            if !self.punctuation(')') {
                self.error(value_code, "expected `)` in structural constant expression");
            }
            return value;
        }
        self.integer(value_code, value_message)
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
    /// Declaration members can be delimited either by `,` or by a physical
    /// line break. The latter is significant only between already-tokenized
    /// members; it never changes expression parsing or generic applications.
    fn line_break_before_current(&self) -> bool {
        let Some(previous) = self.previous() else {
            return false;
        };
        let Some(current) = self.current() else {
            return false;
        };
        let start = self.lexed.tokens[previous].span.end as usize;
        let end = self.lexed.tokens[current].span.start as usize;
        self.source
            .get(start..end)
            .is_some_and(|between| between.contains('\n') || between.contains('\r'))
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
    /// Trait and implementation members may be ordinary identifiers or
    /// declared operators.  Retaining the exact operator spelling here makes
    /// the method table, coherence checking, and operator-call lowering share
    /// one stable name instead of inventing a parser-only surrogate.
    fn callable_member_name(&mut self) -> Option<String> {
        if let Some(name) = self.identifier() {
            return Some(name);
        }
        let current = self.current()?;
        (self.lexed.tokens[current].kind == TokenKind::Operator).then(|| {
            self.position += 1;
            self.text(current).to_owned()
        })
    }
    /// An implementation body has no item keyword in canonical source. Only
    /// accept a bare member when its name is immediately followed by a
    /// callable introducer, keeping malformed arbitrary body expressions out
    /// of the interface namespace.
    fn callable_member_ahead(&self) -> bool {
        let Some(current) = self.current() else {
            return false;
        };
        if self.word() == Some("fn") {
            return true;
        }
        if !matches!(
            self.lexed.tokens[current].kind,
            TokenKind::Identifier | TokenKind::Operator
        ) {
            return false;
        }
        let Some(next) = self.tokens.get(self.position + 1).copied() else {
            return false;
        };
        self.lexed.tokens[next].kind == TokenKind::Punctuation('(')
            || (self.lexed.tokens[next].kind == TokenKind::Operator && self.text(next) == "<")
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
                && Self::operator_starts_expected(&self.lexed.text(self.source, &self.lexed.tokens[i])[self.operator_offset..], value)
        })
    }
    fn operator_starts_expected(text: &str, value: &str) -> bool {
        text == value || match value {
            "=" => text.strip_prefix('=').is_some_and(|suffix| suffix.starts_with(['<', '&', '*', '!'])),
            ">" => text.strip_prefix('>').is_some_and(|suffix| suffix.starts_with('=')),
            _ => false,
        }
    }
    fn operator(&mut self, value: &str) -> bool {
        if self.at_operator(value) {
            self.operator_offset += value.len();
            if self.operator_offset == self.text(self.current().expect("matched operator")).len() {
                self.position += 1;
                self.operator_offset = 0;
            }
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
