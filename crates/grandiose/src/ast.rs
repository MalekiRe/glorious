use std::rc::Rc;

use crate::{lexer::NumberLiteral, span::Span};

#[derive(Clone, Debug)]
pub struct Program {
    pub type_aliases: Vec<TypeAliasDecl>,
    pub effect_row_aliases: Vec<EffectRowAliasDecl>,
    pub globals: Vec<GlobalBinding>,
    pub fixities: Vec<FixityDecl>,
    pub structs: Vec<StructDecl>,
    pub enums: Vec<EnumDecl>,
    pub traits: Vec<TraitDecl>,
    pub impls: Vec<ImplDecl>,
    pub uses: Vec<UseDecl>,
    pub effects: Vec<EffectDecl>,
    pub drops: Vec<DropDecl>,
    pub functions: Vec<Function>,
    /// Explicit source lifetimes attached to reference type spans. Elided
    /// references are absent; runtime type identity continues to erase regions.
    pub reference_lifetimes: Vec<ReferenceLifetimeSyntax>,
    /// Full source-level effect applications used by `perform` expressions and
    /// handler clauses. The legacy `ExprKind::Perform::effect` and
    /// `HandlerClause::effect` fields retain their simple declaration name so
    /// existing bootstrap consumers remain source compatible.
    pub effect_paths: Vec<EffectPathSyntax>,
    /// Structural const literals in ordinary type applications, keyed by the
    /// complete application span. Type/lifetime arguments remain in the
    /// legacy `TypeSyntaxKind::Application` vectors.
    pub type_const_arguments: Vec<TypeConstApplicationSyntax>,
    /// Exact numeric token payloads keyed by expression/pattern span. The
    /// legacy scalar enum payloads remain compatibility shadows only.
    pub numeric_literals: Vec<NumericLiteralSyntax>,
}

impl Program {
    pub fn numeric_literal(&self, span: Span) -> Option<&NumberLiteral> {
        self.numeric_literals
            .iter()
            .find(|entry| entry.span == span)
            .map(|entry| &entry.literal)
    }

    pub fn reference_lifetime(&self, reference: Span) -> Option<&LifetimeSyntax> {
        self.reference_lifetimes
            .iter()
            .find(|entry| entry.reference == reference)
            .map(|entry| &entry.lifetime)
    }

    pub fn effect_path(&self, site: Span) -> Option<&TypeSyntax> {
        self.effect_paths
            .iter()
            .find(|entry| entry.site == site)
            .map(|entry| &entry.effect)
    }

    pub fn type_const_arguments(&self, application: Span) -> &[ConstAssociatedArgumentSyntax] {
        self.type_const_arguments
            .iter()
            .find(|entry| entry.application == application)
            .map_or(&[], |entry| entry.arguments.as_slice())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumericLiteralSyntax {
    pub span: Span,
    pub literal: NumberLiteral,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LifetimeSyntax {
    pub name: String,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReferenceLifetimeSyntax {
    pub reference: Span,
    pub lifetime: LifetimeSyntax,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectPathSyntax {
    pub site: Span,
    pub effect: TypeSyntax,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeConstApplicationSyntax {
    pub application: Span,
    pub arguments: Vec<ConstAssociatedArgumentSyntax>,
}

#[derive(Clone, Debug)]
pub struct UseDecl {
    pub generics: Option<GenericParams>,
    pub quantity: QuantitySyntax,
    pub target: TypeSyntax,
    pub where_clause: Option<WhereClause>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct TraitDecl {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub supertraits: Vec<TraitRefSyntax>,
    pub associated_types: Vec<AssociatedTypeDecl>,
    pub methods: Vec<TraitMethod>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedTypeDecl {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub kind: AssociatedItemSyntaxKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssociatedItemSyntaxKind {
    Type,
    EffectRow,
}

#[derive(Clone, Debug)]
pub struct ImplDecl {
    pub generics: Option<GenericParams>,
    pub polarity: GoalPolarity,
    pub trait_ref: TraitRefSyntax,
    pub self_ty: TypeSyntax,
    pub where_clause: Option<WhereClause>,
    pub associated_types: Vec<AssociatedTypeDefinition>,
    pub methods: Vec<TraitMethod>,
    pub span: Span,
}

/// An ordinary trait callable. Trait declarations carry `body: None`; positive
/// implementations carry the checked source body.
#[derive(Clone, Debug)]
pub struct TraitMethod {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeSyntax>,
    pub outward_effects: Option<EffectRowSyntax>,
    pub where_clause: Option<WhereClause>,
    pub body: Option<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedTypeDefinition {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub value: AssociatedBindingValue,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GoalPolarity {
    Positive,
    Negative,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GenericParams {
    pub params: Vec<GenericParam>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GenericParam {
    pub name: String,
    pub kind: GenericParamKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GenericParamKind {
    Type,
    Lifetime,
    EffectRow,
    Const(ConstKind),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ConstKind {
    Quantity,
    U32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhereClause {
    pub goals: Vec<WhereGoal>,
    pub lifetime_outlives: Vec<LifetimeOutlivesSyntax>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LifetimeOutlivesSyntax {
    pub longer: LifetimeSyntax,
    pub shorter: LifetimeSyntax,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhereGoal {
    pub higher_ranked_lifetimes: Vec<GenericParam>,
    pub subject: TypeSyntax,
    pub polarity: GoalPolarity,
    pub relation: TraitRefSyntax,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitRefSyntax {
    pub path: Vec<TypePathSegment>,
    pub arguments: Vec<GoalArgument>,
    pub bindings: Vec<AssociatedBinding>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GoalArgument {
    Type(TypeSyntax),
    Lifetime { name: String, span: Span },
    Quantity(QuantitySyntax),
    U32 { value: u64, span: Span },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssociatedArgumentSyntax {
    Type(TypeSyntax),
    Lifetime { name: String, span: Span },
}

/// A structural const argument in an associated-type argument list, e.g. the
/// `[1, 2]` or `3` in `Assoc<[1, 2], 3, T>`. Named const binders parse as
/// ordinary [`AssociatedArgumentSyntax::Type`] paths and are reclassified by
/// the declared associated-item parameter kinds during trait lowering.
///
/// These live beside the type/lifetime argument list — with their original
/// binder positions — rather than inside it, mirroring how
/// [`TypeSyntaxKind::Application`] records lifetime arguments, so consumers of
/// the legacy two-variant list are unaffected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstAssociatedArgumentSyntax {
    /// The argument's index within the complete source argument list.
    pub position: usize,
    pub value: ConstArgumentValueSyntax,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConstArgumentValueSyntax {
    Quantity(QuantitySyntax),
    U32 { value: u64, span: Span },
}

impl ConstArgumentValueSyntax {
    pub fn span(&self) -> Span {
        match self {
            Self::Quantity(quantity) => quantity.span,
            Self::U32 { span, .. } => *span,
        }
    }
}

impl AssociatedArgumentSyntax {
    pub fn span(&self) -> Span {
        match self {
            Self::Type(ty) => ty.span,
            Self::Lifetime { span, .. } => *span,
        }
    }

    pub fn as_type(&self) -> Option<&TypeSyntax> {
        match self {
            Self::Type(ty) => Some(ty),
            Self::Lifetime { .. } => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedBinding {
    pub name: String,
    pub arguments: Vec<AssociatedArgumentSyntax>,
    /// Structural const arguments with their original binder positions,
    /// interleaved with `arguments` by position to recover source order.
    pub const_arguments: Vec<ConstAssociatedArgumentSyntax>,
    pub value: AssociatedBindingValue,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssociatedBindingValue {
    Type(TypeSyntax),
    EffectRow(EffectRowSyntax),
}

impl AssociatedBindingValue {
    pub fn span(&self) -> Span {
        match self {
            Self::Type(value) => value.span,
            Self::EffectRow(value) => value.span,
        }
    }

    pub fn as_type(&self) -> Option<&TypeSyntax> {
        match self {
            Self::Type(value) => Some(value),
            Self::EffectRow(_) => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuantitySyntax {
    pub lower: u64,
    pub upper: Option<u64>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectRowSyntax {
    pub effects: Vec<TypeSyntax>,
    pub tail: Option<TypePathSegment>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectRowAliasDecl {
    pub name: String,
    pub row: EffectRowSyntax,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct DropDecl {
    pub target: String,
    pub generics: Option<GenericParams>,
    pub target_type: TypeSyntax,
    pub where_clause: Option<WhereClause>,
    pub body: Expr,
    pub self_span: Span,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct TypeAliasDecl {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub generic_span: Option<Span>,
    pub target: TypeSyntax,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct GlobalBinding {
    /// An associated value binding is owned by a nominal type or type alias.
    /// This is a flat value-subnamespace key, not a module path.
    pub owner: Option<String>,
    pub name: String,
    pub value: Expr,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Associativity {
    Left,
    Right,
    /// A nonassociative infix operator: chains such as `a op b op c` are
    /// rejected during operator grouping.
    None,
}

#[derive(Clone, Debug)]
pub struct FixityDecl {
    pub name: String,
    pub kind: FixityKind,
    pub precedence: u8,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FixityKind {
    Infix(Associativity),
    Prefix,
}

#[derive(Clone, Debug)]
pub struct StructDecl {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub generic_span: Option<Span>,
    pub fields: Vec<FieldDecl>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct FieldDecl {
    pub name: String,
    pub ty: TypeSyntax,
    pub visibility: FieldVisibility,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FieldVisibility {
    Public,
    Private,
}

#[derive(Clone, Debug)]
pub struct EnumDecl {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub generic_span: Option<Span>,
    pub variants: Vec<VariantDecl>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct VariantDecl {
    pub name: String,
    pub fields: Vec<TypeSyntax>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeSyntax {
    pub kind: TypeSyntaxKind,
    pub span: Span,
}

impl TypeSyntax {
    /// Returns the spelling only for the legacy frontend's supported type form:
    /// one unqualified identifier with no generic arguments.
    pub fn simple_name(&self) -> Option<&str> {
        let TypeSyntaxKind::Path(segments) = &self.kind else {
            return None;
        };
        (segments.len() == 1).then(|| segments[0].name.as_str())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeSyntaxKind {
    Path(Vec<TypePathSegment>),
    SharedReference(Box<TypeSyntax>),
    UniqueReference(Box<TypeSyntax>),
    Tuple(Vec<TypeSyntax>),
    Application {
        constructor: Box<TypeSyntax>,
        /// Runtime-relevant type arguments, retained in source order relative
        /// to one another. Lifetime arguments are recorded separately with
        /// their original binder positions so mixed applications such as
        /// `Slice<'a, T>` do not turn regions into runtime type identity.
        arguments: Vec<TypeSyntax>,
        lifetime_arguments: Vec<GenericLifetimeArgumentSyntax>,
    },
    Projection {
        subject: Box<TypeSyntax>,
        trait_ref: TraitRefSyntax,
        item: TypePathSegment,
        arguments: Vec<AssociatedArgumentSyntax>,
        /// Structural const arguments with their original binder positions,
        /// interleaved with `arguments` by position to recover source order.
        const_arguments: Vec<ConstAssociatedArgumentSyntax>,
    },
    Never,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GenericLifetimeArgumentSyntax {
    pub position: usize,
    pub lifetime: LifetimeSyntax,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypePathSegment {
    pub name: String,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct EffectDecl {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub generic_span: Option<Span>,
    pub operations: Vec<EffectOperationDecl>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct EffectOperationDecl {
    pub name: String,
    pub params: Vec<Param>,
    /// `None` is the source-level Unit result written as an empty type.
    pub return_type: Option<TypeSyntax>,
    pub terminal: bool,
    pub resumption_lower: usize,
    pub resumption_upper: Option<usize>,
    pub has_resumption_quantity: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub params: Vec<Param>,
    /// `None` is the source-level Unit form written as an empty result before
    /// the body or effect row.
    pub return_type: Option<TypeSyntax>,
    pub effectful: bool,
    pub outward_effects: Option<EffectRowSyntax>,
    pub where_clause: Option<WhereClause>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: TypeSyntax,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

/// A source label occurrence: the name after `@`, without the sigil.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabelSyntax {
    pub name: Rc<str>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Unit,
    Int(i64),
    /// A float literal. The program's numeric-literal side table retains the
    /// exact token payload; range/precision judgment belongs to expected-type
    /// elaboration.
    Float(f64),
    String(Rc<str>),
    Char(char),
    Byte(u8),
    ByteString(Rc<[u8]>),
    Variable(Rc<[Rc<str>]>),
    Move(Rc<Expr>),
    Closure {
        params: Rc<[Rc<str>]>,
        body: Rc<Expr>,
    },
    /// An explicit typed anonymous callable: `(x: i32) -> i32 { x + 1 }`.
    /// Distinct from tuple/group expressions and compact inferred closures.
    TypedClosure {
        params: Rc<Vec<Param>>,
        return_type: Option<Rc<TypeSyntax>>,
        effectful: bool,
        outward_effects: Option<Rc<EffectRowSyntax>>,
        body: Rc<Expr>,
    },
    /// `@outer: { body }` — a generative label binder over its body. Also
    /// wraps the labeled trailing block of `loop @outer: { body }`.
    Labeled {
        label: LabelSyntax,
        body: Rc<Expr>,
    },
    /// `@outer` without a colon: a reference to an existing label identity.
    LabelReference(LabelSyntax),
    /// `label @done: i32 { body }` — a direct typed destination.
    LabelDestination {
        label: LabelSyntax,
        ty: Option<Rc<TypeSyntax>>,
        body: Rc<Expr>,
    },
    /// `leave@done(42)` — direct typed transfer to a label destination.
    Leave {
        label: LabelSyntax,
        value: Option<Rc<Expr>>,
    },
    /// `resume(k, value)` — structural resumption invocation.
    Resume {
        resumption: Rc<Expr>,
        value: Option<Rc<Expr>>,
    },
    /// `cancel(k)` — structural resumption cancellation.
    Cancel {
        resumption: Rc<Expr>,
    },
    /// `tail(k, value)` — structural tail resumption transfer.
    TailResume {
        resumption: Rc<Expr>,
        value: Option<Rc<Expr>>,
    },
    /// `subject is Pattern` — the core pattern-test expression. Binder
    /// environments are established by later semantic phases.
    Is {
        subject: Rc<Expr>,
        pattern: Rc<Pattern>,
    },
    /// A block in contextual position — a trailing call block or an operator
    /// operand. Whether it is an eagerly evaluated block or a fresh anonymous
    /// callable is decided by expected-type elaboration, never by the parser.
    ContextBlock(Rc<Vec<Stmt>>),
    List(Rc<Vec<Expr>>),
    Tuple(Rc<Vec<Expr>>),
    Struct {
        name: Rc<str>,
        fields: Rc<Vec<(String, Expr)>>,
    },
    Field(Rc<Expr>, String),
    Block(Rc<Vec<Stmt>>),
    Call(Rc<Expr>, Rc<Vec<Expr>>),
    Perform {
        effect: Rc<str>,
        operation: Rc<str>,
        args: Rc<Vec<Expr>>,
    },
    Handle {
        computation: Rc<Expr>,
        clauses: Rc<Vec<HandlerClause>>,
    },
    Unary {
        op: UnaryOp,
        operand: Rc<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Rc<Expr>,
        rhs: Rc<Expr>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnaryOp {
    Negate,
    BorrowShared,
    BorrowUnique,
    Dereference,
}

#[derive(Clone, Debug)]
pub struct HandlerClause {
    pub effect: String,
    pub operation: String,
    pub patterns: Vec<Pattern>,
    pub resumption: Option<String>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

/// The `..` remainder inside a tuple, struct, or variant pattern, with the
/// number of fields that preceded it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PatternRest {
    pub before: usize,
    pub span: Span,
}

/// Maps an explicit positional subpattern to its declaration-order field.
/// With no remainder, short patterns name a prefix. With `..`, entries after
/// the remainder name a suffix from the end.
pub fn pattern_field_index(
    rest: Option<PatternRest>,
    position: usize,
    explicit_len: usize,
    field_count: usize,
) -> usize {
    match rest {
        Some(rest) if position >= rest.before => field_count - (explicit_len - position),
        _ => position,
    }
}

#[derive(Clone, Debug)]
pub enum PatternKind {
    Wildcard,
    Binding(String),
    Unit,
    Int(i64),
    /// Grammar-complete float literal pattern; semantic phases judge whether a
    /// float scalar may be matched.
    Float(f64),
    String(String),
    Char(char),
    Byte(u8),
    Variant {
        path: Vec<String>,
        fields: Vec<Pattern>,
        rest: Option<PatternRest>,
    },
    /// `(a, b, ..)` — a tuple pattern with optional remainder.
    Tuple {
        elements: Vec<Pattern>,
        rest: Option<PatternRest>,
    },
    /// `Name { field: pattern, shorthand, .. }` — a named-struct pattern.
    Struct {
        name: String,
        fields: Vec<StructFieldPattern>,
        rest: Option<PatternRest>,
    },
}

#[derive(Clone, Debug)]
pub struct StructFieldPattern {
    pub field: String,
    pub pattern: Pattern,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Let {
        name: String,
        value: Expr,
        span: Span,
    },
    Deconstruct {
        /// The named struct in a struct pattern, or `None` for a tuple pattern.
        ty: Option<String>,
        fields: Vec<DeconstructField>,
        /// The `..` token when an explicit remainder pattern was written.
        rest: Option<Span>,
        value: Expr,
        span: Span,
    },
    /// Replace or reinitialize one statically selected source place. Assignment
    /// is deliberately a statement: the right-hand side is evaluated before
    /// the destination is inspected or mutated, and the construct has no value.
    Assign {
        destination: AssignmentPlace,
        value: Expr,
        span: Span,
    },
    Expr(Expr),
}

#[derive(Clone, Debug)]
pub struct AssignmentPlace {
    pub kind: AssignmentPlaceKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum AssignmentPlaceKind {
    /// A lexically local root followed only by static tuple/struct fields.
    Local {
        name: Rc<str>,
        fields: Vec<AssignmentField>,
    },
    /// A reference-valued expression followed only by static tuple/struct
    /// fields. Semantic checking requires a live, unsuspended unique reference.
    Dereference {
        reference: Rc<Expr>,
        fields: Vec<AssignmentField>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignmentField {
    pub name: String,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeconstructField {
    pub field: String,
    /// `None` denotes an opaque `_` discard rather than a new owner.
    pub binding: Option<String>,
    /// Tuple fields following `..` are numbered from the end until type
    /// information determines their absolute position. Struct fields never
    /// set this flag.
    pub from_end: bool,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
}
