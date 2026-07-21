use std::rc::Rc;

use crate::frontend::span::Span;

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
}

impl Program {
    pub fn reference_lifetime(&self, reference: Span) -> Option<&LifetimeSyntax> {
        self.reference_lifetimes
            .iter()
            .find(|entry| entry.reference == reference)
            .map(|entry| &entry.lifetime)
    }
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
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedTypeDecl {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct ImplDecl {
    pub generics: Option<GenericParams>,
    pub polarity: GoalPolarity,
    pub trait_ref: TraitRefSyntax,
    pub self_ty: TypeSyntax,
    pub where_clause: Option<WhereClause>,
    pub associated_types: Vec<AssociatedTypeDefinition>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedTypeDefinition {
    pub name: String,
    pub generics: Option<GenericParams>,
    pub value: TypeSyntax,
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
        arguments: Vec<TypeSyntax>,
    },
    Projection {
        subject: Box<TypeSyntax>,
        trait_ref: TraitRefSyntax,
        item: TypePathSegment,
        arguments: Vec<AssociatedArgumentSyntax>,
    },
    Never,
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

#[derive(Clone, Debug)]
pub enum ExprKind {
    Unit,
    Int(i64),
    String(Rc<str>),
    Variable(Rc<[Rc<str>]>),
    Move(Rc<Expr>),
    Closure {
        params: Rc<[Rc<str>]>,
        body: Rc<Expr>,
    },
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

#[derive(Clone, Debug)]
pub enum PatternKind {
    Wildcard,
    Binding(String),
    Unit,
    Int(i64),
    String(String),
    Variant {
        path: Vec<String>,
        fields: Vec<Pattern>,
    },
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
    Expr(Expr),
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
    Eq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
}
