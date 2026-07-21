//! Typed, resolved Core for the deliberately small bytecode compiler slice.

use std::collections::BTreeMap;

use grandiose_vm::{Constant, Primitive, TypeId};

use crate::compiler_traits::HostImportRole;

use crate::span::Span;

pub type LocalId = u32;
pub type DeclarationId = u32;
pub type RegionId = u32;
pub type PointId = u32;
/// Generative identity of one source-level label binder within a body.
pub type LabelId = u32;

#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    pub functions: Vec<Function>,
    /// Canonical interprocedural continuation-performance evidence used by
    /// ownership multiplication during Core lowering.
    pub performance_summaries: Vec<CallablePerformanceSummary>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallablePerformanceSummary {
    pub callable: String,
    /// Finite normal-return multipliers retained by the bounded analysis.
    pub normal_multipliers: Vec<u64>,
    pub may_abandon: bool,
    /// True when recursion, overflow, or opaque dispatch widened the finite
    /// set. Widened evidence can never establish an exact multiplier.
    pub widened: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub declaration: DeclarationId,
    pub name: String,
    pub global_factory: bool,
    pub receiver_mode: Option<u32>,
    pub receiver_type: TypeId,
    pub receiver_captures: Vec<Param>,
    pub no_return: bool,
    pub outward_protocols: Vec<u32>,
    pub params: Vec<Param>,
    pub result: TypeId,
    /// Canonically ordered nonlexical-region proof facts for this body.
    pub regions: Vec<RegionFact>,
    pub body: Expr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegionFact {
    pub region: RegionId,
    pub issued_at: PointId,
    pub live_points: Vec<PointId>,
    pub ended_at: Option<PointId>,
    pub outlives: Vec<RegionId>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    pub local: LocalId,
    pub name: String,
    pub ty: TypeId,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub ty: TypeId,
    pub span: Span,
    /// Compatibility view for a direct reference or a one-leaf carrier.
    pub reference: Option<ReferenceOrigin>,
    /// Canonical reference origins keyed by their path inside this value.
    /// A direct reference uses the empty path.
    pub reference_fields: BTreeMap<Vec<u32>, ReferenceOrigin>,
    pub kind: ExprKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReferenceOrigin {
    pub region: RegionId,
    pub root: LocalId,
    pub path: Vec<u32>,
    pub projection_types: Vec<TypeId>,
    pub external: bool,
    pub unique: bool,
    pub parent: Option<LocalId>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Unit,
    Constant(Constant),
    Local {
        local: LocalId,
        copy: bool,
    },
    Move {
        local: LocalId,
    },
    Borrow {
        source: LocalId,
        unique: bool,
    },
    ProjectBorrow {
        source: LocalId,
        path: Vec<ProjectBorrowStep>,
        unique: bool,
    },
    /// A projected reborrow whose parent reference is itself an expression.
    /// MIR retains the materialized parent as the first link in the generated
    /// borrow-parent chain, so it cannot be ended before the leaf loan.
    TemporaryProjectBorrow {
        source: Box<Expr>,
        path: Vec<ProjectBorrowStep>,
        unique: bool,
    },
    Reborrow {
        source: LocalId,
        unique: bool,
    },
    /// Copy a duplicable referent through a live reference without consuming
    /// either the reference or its owner.
    DerefCopy {
        source: LocalId,
    },
    /// Move the initialized referent through a live named unique reference,
    /// preserving the reference/loan while leaving its referent uninitialized.
    DerefMove {
        source: LocalId,
    },
    Call {
        declaration: DeclarationId,
        args: Vec<Expr>,
    },
    TailCall {
        declaration: DeclarationId,
        args: Vec<Expr>,
    },
    /// The current callable's ABI receiver. This value is only materialized
    /// when a nested generated callable must retain a shared lexical receiver;
    /// ordinary recursive calls use `CallSelf` directly.
    Receiver,
    /// Invoke the current closure function again with its existing receiver
    /// environment. This is a static self identity, not a cyclic callable
    /// capture.
    CallSelf {
        args: Vec<Expr>,
    },
    /// Invoke a statically known closure function through a shared lexical
    /// receiver routed into this generated function. This is used when a
    /// recursive call occurs inside a nested handler body or clause, whose
    /// ABI receiver is not the recursive closure's receiver.
    CallKnownReceiver {
        declaration: DeclarationId,
        receiver: Box<Expr>,
        args: Vec<Expr>,
    },
    /// Tail-transfer to the current closure function and receiver.
    TailCallSelf {
        args: Vec<Expr>,
    },
    TailCallKnownReceiver {
        declaration: DeclarationId,
        receiver: Box<Expr>,
        args: Vec<Expr>,
    },
    MakeCallable {
        declaration: DeclarationId,
        captures: Vec<Expr>,
    },
    CallIndirect {
        callable: Box<Expr>,
        receiver_mode: u32,
        args: Vec<Expr>,
    },
    TailCallIndirect {
        callable: Box<Expr>,
        receiver_mode: u32,
        args: Vec<Expr>,
    },
    /// A direct typed destination. Both normal completion of `body` and a
    /// matching `Leave` produce this expression's value.
    LabelDestination {
        label: LabelId,
        has_leave: bool,
        body: Box<Expr>,
    },
    /// Abandon the intervening lexical scopes and transfer `value` to the
    /// active destination carrying this generative label identity.
    Leave {
        label: LabelId,
        value: Box<Expr>,
    },
    /// An observational decision over a fully typed pattern. The result is a
    /// raw `u32` discriminator; source lowering routes it through the ordinary
    /// standard-library `__g1_bool_from_u32` conversion.
    PatternTest {
        subject: Box<Expr>,
        pattern: DecisionPattern,
    },
    /// An observational pattern decision through a live shared or unique
    /// reference. The referent is inspected in place; no owner is copied,
    /// moved, or reconstructed.
    PatternTestBorrowed {
        reference: LocalId,
        pattern: DecisionPattern,
    },
    /// A non-owning view of an existing reference register used only as the
    /// subject of an observational refinement branch.
    LocalReferenceView {
        local: LocalId,
    },
    /// The compiler-recognized CFG form of the ordinary source composition
    /// `if(subject is P) { positive } else { negative }`.
    RefinementBranch {
        subject: Box<Expr>,
        pattern: DecisionPattern,
        bindings: Vec<DecisionBinding>,
        /// Baseline owners whose branch-specific residual shells are proven
        /// zero-use disposable and are therefore retired on each incoming
        /// edge rather than carried through the join.
        retire_at_join: Vec<LocalId>,
        /// Baseline owners whose top-level field initialization differs on
        /// the incoming edges. Each bitmap marks fields governed by runtime
        /// Empty/drop-flag state after the join.
        conditional_at_join: Vec<(LocalId, Vec<bool>)>,
        /// Exact complementary variant proven on the negative edge when the
        /// enum has exactly two variants.
        negative_variant: Option<u32>,
        positive: Box<Expr>,
        negative: Box<Expr>,
    },
    Construct {
        nominal: TypeId,
        variant: Option<u32>,
        fields: Vec<ConstructField>,
    },
    Project {
        subject: Box<Expr>,
        field: u32,
        copy: bool,
        /// A proof established while lowering a dereferenced enum reference.
        /// The dereference materializes a fresh MIR register, so its dominating
        /// proof must be reattached before the payload projection.
        variant: Option<u32>,
    },
    Primitive {
        primitive: Primitive,
        args: Vec<Expr>,
    },
    HostCall {
        import: HostImportRole,
        args: Vec<Expr>,
    },
    /// Non-callable emitted body for a manifest host leaf. Genuine calls are
    /// replaced at their call site; retaining this declaration slot preserves
    /// stable function numbering without requesting an unused capability.
    HostLeafStub,
    /// Trusted standard-library terminal abort. This is neither a user
    /// intrinsic nor an effect and therefore has no continuation or cleanup
    /// edge.
    Abort {
        message: Option<String>,
    },
    Perform {
        protocol: u32,
        operation: u32,
        payloads: Vec<Expr>,
    },
    Resume {
        resumption: Box<Expr>,
        receiver_mode: u32,
        value: Box<Expr>,
    },
    /// Terminal transfer into a one-shot resumption. Unlike `Resume`, this
    /// expression never returns to the current clause frame.
    TailResume {
        resumption: Box<Expr>,
        value: Box<Expr>,
    },
    Cancel {
        resumption: Box<Expr>,
    },
    Handle {
        handler_def: u32,
        handler_type: TypeId,
        clauses: Vec<(DeclarationId, TypeId, Vec<Expr>)>,
        shared_clause_captures: Vec<Expr>,
        body: DeclarationId,
        body_type: TypeId,
        body_captures: Vec<Expr>,
    },
    Block {
        statements: Vec<Stmt>,
        tail: Box<Expr>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct ConstructField {
    pub field: u32,
    pub value: Expr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeconstructField {
    pub field: u32,
    /// A bound field becomes this fresh owner; a discarded field has no local.
    pub local: Option<LocalId>,
    pub name: Option<String>,
    pub ty: TypeId,
    /// Exact `[0,0]` fields have no runtime representation and need neither a
    /// projection nor a `Drop` instruction.
    pub erased: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub struct DecisionPattern {
    pub ty: TypeId,
    pub span: Span,
    pub kind: DecisionPatternKind,
}

#[derive(Clone, Debug, PartialEq)]
pub enum DecisionPatternKind {
    Wildcard,
    Binding {
        name: String,
    },
    Unit,
    Int(Constant),
    Float(Constant),
    Char(char),
    String(String),
    Variant {
        variant: u32,
        fields: Vec<DecisionPattern>,
    },
    /// Tuple/struct fields in runtime declaration order. Omitted fields are
    /// explicit wildcards, preserving the aggregate width during temporary
    /// projection and reconstruction.
    Aggregate {
        fields: Vec<DecisionPattern>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct DecisionBinding {
    pub local: LocalId,
    pub name: String,
    pub ty: TypeId,
    pub span: Span,
    pub path: Vec<DecisionProjection>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct DecisionProjection {
    pub field: u32,
    pub nominal: TypeId,
    pub variant: Option<u32>,
    pub field_types: Vec<TypeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProjectBorrowStep {
    pub field: u32,
    /// Required active enum variant for this payload step. Tuple and struct
    /// projections carry no variant proof.
    pub variant: Option<u32>,
    pub reference: TypeId,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Let {
        local: LocalId,
        name: String,
        ty: TypeId,
        span: Span,
        value: Expr,
    },
    Deconstruct {
        source: LocalId,
        source_name: String,
        ty: TypeId,
        fields: Vec<DeconstructField>,
        span: Span,
    },
    /// Source assignment after type/visibility/ownership checking. `value`
    /// remains before `destination` so every later lowering preserves the
    /// language's RHS-before-place evaluation order.
    Assign {
        value: Expr,
        destination: AssignmentPlace,
        /// Whether the old initialized subtree must be compiler-destroyed
        /// before storing. False denotes reinitialization after a move.
        destroy_old: bool,
        span: Span,
    },
    EndBorrow {
        local: LocalId,
        region: RegionId,
        span: Span,
    },
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub struct AssignmentPlace {
    pub root: AssignmentRoot,
    pub projections: Vec<AssignmentProjection>,
    pub ty: TypeId,
}

#[derive(Clone, Debug, PartialEq)]
pub enum AssignmentRoot {
    Local {
        local: LocalId,
        name: String,
        ty: TypeId,
    },
    /// A named unique-reference place is observed in situ; assignment through
    /// it neither moves nor copies the reference owner.
    DereferenceLocal {
        local: LocalId,
        name: String,
        reference: TypeId,
        referent: TypeId,
    },
    Dereference {
        reference: Box<Expr>,
        referent: TypeId,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignmentProjection {
    pub field: u32,
    pub ty: TypeId,
    pub span: Span,
}

impl Program {
    pub fn canonical_text(&self) -> String {
        let mut output = String::new();
        use std::fmt::Write as _;
        for summary in &self.performance_summaries {
            writeln!(
                output,
                "performance {:?} normal={:?} abandon={} widened={}",
                summary.callable, summary.normal_multipliers, summary.may_abandon, summary.widened
            )
            .unwrap();
        }
        for function in &self.functions {
            function.write(&mut output);
        }
        output
    }

    pub fn fingerprint(&self) -> u64 {
        stable_fingerprint(self.canonical_text().as_bytes())
    }
}

impl Function {
    fn write(&self, output: &mut String) {
        use std::fmt::Write as _;
        writeln!(
            output,
            "fn#{} {:?} factory={} receiver={:?}:t{} no_return={} outward={:?} -> t{}",
            self.declaration,
            self.name,
            self.global_factory,
            self.receiver_mode,
            self.receiver_type,
            self.no_return,
            self.outward_protocols,
            self.result
        )
        .unwrap();
        for param in &self.params {
            writeln!(
                output,
                "  param l{} {:?}:t{} @{}..{}",
                param.local, param.name, param.ty, param.span.start, param.span.end
            )
            .unwrap();
        }
        for region in &self.regions {
            writeln!(
                output,
                "  region r{} issued=p{} live={:?} ended={:?} outlives={:?}",
                region.region,
                region.issued_at,
                region.live_points,
                region.ended_at.map(|point| format!("p{point}")),
                region.outlives
            )
            .unwrap();
        }
        self.body.write(output, 1);
    }
}

impl Expr {
    fn write(&self, output: &mut String, depth: usize) {
        use std::fmt::Write as _;
        let pad = "  ".repeat(depth);
        write!(
            output,
            "{pad}t{} @{}..{} ref={:?} ",
            self.ty, self.span.start, self.span.end, self.reference_fields
        )
        .unwrap();
        match &self.kind {
            ExprKind::Unit => writeln!(output, "unit").unwrap(),
            ExprKind::Constant(value) => writeln!(output, "const {value:?}").unwrap(),
            ExprKind::Local { local, copy } => {
                writeln!(output, "local l{local} copy={copy}").unwrap()
            }
            ExprKind::Move { local } => writeln!(output, "move l{local}").unwrap(),
            ExprKind::Borrow { source, unique } => {
                writeln!(output, "borrow l{source} unique={unique}").unwrap()
            }
            ExprKind::ProjectBorrow {
                source,
                path,
                unique,
            } => {
                writeln!(output, "project-borrow l{source} unique={unique}").unwrap();
                for step in path {
                    writeln!(
                        output,
                        "{pad}  field#{} variant={:?} t{}",
                        step.field, step.variant, step.reference
                    )
                    .unwrap();
                }
            }
            ExprKind::TemporaryProjectBorrow {
                source,
                path,
                unique,
            } => {
                writeln!(output, "temporary-project-borrow unique={unique}").unwrap();
                source.write(output, depth + 1);
                for step in path {
                    writeln!(
                        output,
                        "{pad}  field#{} variant={:?} t{}",
                        step.field, step.variant, step.reference
                    )
                    .unwrap();
                }
            }
            ExprKind::Reborrow { source, unique } => {
                writeln!(output, "reborrow l{source} unique={unique}").unwrap()
            }
            ExprKind::DerefCopy { source } => writeln!(output, "deref-copy l{source}").unwrap(),
            ExprKind::DerefMove { source } => writeln!(output, "deref-move l{source}").unwrap(),
            ExprKind::Call { declaration, args } => {
                writeln!(output, "call fn#{declaration}").unwrap();
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::TailCall { declaration, args } => {
                writeln!(output, "tail-call fn#{declaration}").unwrap();
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::Receiver => writeln!(output, "receiver").unwrap(),
            ExprKind::CallSelf { args } => {
                writeln!(output, "call-self").unwrap();
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::CallKnownReceiver {
                declaration,
                receiver,
                args,
            } => {
                writeln!(output, "call-known-receiver fn#{declaration}").unwrap();
                receiver.write(output, depth + 1);
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::TailCallSelf { args } => {
                writeln!(output, "tail-call-self").unwrap();
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::TailCallKnownReceiver {
                declaration,
                receiver,
                args,
            } => {
                writeln!(output, "tail-call-known-receiver fn#{declaration}").unwrap();
                receiver.write(output, depth + 1);
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::MakeCallable {
                declaration,
                captures,
            } => {
                writeln!(output, "make-callable fn#{declaration}").unwrap();
                captures
                    .iter()
                    .for_each(|capture| capture.write(output, depth + 1));
            }
            ExprKind::CallIndirect {
                callable,
                receiver_mode,
                args,
            } => {
                writeln!(output, "call-indirect mode={receiver_mode}").unwrap();
                callable.write(output, depth + 1);
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::TailCallIndirect {
                callable,
                receiver_mode,
                args,
            } => {
                writeln!(output, "tail-call-indirect mode={receiver_mode}").unwrap();
                callable.write(output, depth + 1);
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::LabelDestination {
                label,
                has_leave,
                body,
            } => {
                writeln!(output, "label-destination label#{label} leaves={has_leave}").unwrap();
                body.write(output, depth + 1);
            }
            ExprKind::Leave { label, value } => {
                writeln!(output, "leave label#{label}").unwrap();
                value.write(output, depth + 1);
            }
            ExprKind::PatternTest { subject, pattern } => {
                writeln!(output, "pattern-test {pattern:?}").unwrap();
                subject.write(output, depth + 1);
            }
            ExprKind::PatternTestBorrowed { reference, pattern } => {
                writeln!(
                    output,
                    "pattern-test-borrowed local#{reference} {pattern:?}"
                )
                .unwrap();
            }
            ExprKind::LocalReferenceView { local } => {
                writeln!(output, "local-reference-view local#{local}").unwrap();
            }
            ExprKind::RefinementBranch {
                subject,
                pattern,
                bindings,
                retire_at_join,
                conditional_at_join,
                negative_variant,
                positive,
                negative,
            } => {
                writeln!(
                    output,
                    "refinement-branch {pattern:?} bindings={bindings:?} retire={retire_at_join:?} conditional={conditional_at_join:?} negative-variant={negative_variant:?}"
                )
                .unwrap();
                subject.write(output, depth + 1);
                positive.write(output, depth + 1);
                negative.write(output, depth + 1);
            }
            ExprKind::Construct {
                nominal,
                variant,
                fields,
            } => {
                writeln!(output, "construct t{nominal} v{variant:?}").unwrap();
                for field in fields {
                    writeln!(output, "{pad}  field#{}", field.field).unwrap();
                    field.value.write(output, depth + 2);
                }
            }
            ExprKind::Project {
                subject,
                field,
                copy,
                variant,
            } => {
                writeln!(
                    output,
                    "project field#{field} copy={copy} variant={variant:?}"
                )
                .unwrap();
                subject.write(output, depth + 1);
            }
            ExprKind::Primitive { primitive, args } => {
                writeln!(output, "primitive {primitive:?}").unwrap();
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::HostCall { import, args } => {
                writeln!(output, "host-call {import:?}").unwrap();
                args.iter().for_each(|arg| arg.write(output, depth + 1));
            }
            ExprKind::HostLeafStub => writeln!(output, "host-leaf-stub").unwrap(),
            ExprKind::Abort { message } => writeln!(output, "abort {message:?}").unwrap(),
            ExprKind::Perform {
                protocol,
                operation,
                payloads,
            } => {
                writeln!(output, "perform p{protocol}/o{operation}").unwrap();
                payloads
                    .iter()
                    .for_each(|payload| payload.write(output, depth + 1));
            }
            ExprKind::Resume {
                resumption,
                receiver_mode,
                value,
            } => {
                writeln!(output, "resume mode={receiver_mode}").unwrap();
                resumption.write(output, depth + 1);
                value.write(output, depth + 1);
            }
            ExprKind::TailResume { resumption, value } => {
                writeln!(output, "tail-resume").unwrap();
                resumption.write(output, depth + 1);
                value.write(output, depth + 1);
            }
            ExprKind::Cancel { resumption } => {
                writeln!(output, "cancel").unwrap();
                resumption.write(output, depth + 1);
            }
            ExprKind::Handle {
                handler_def,
                handler_type,
                clauses,
                shared_clause_captures,
                body,
                body_type,
                body_captures,
            } => {
                writeln!(
                    output,
                    "handle h{handler_def}:t{handler_type} clauses={clauses:?} body=fn#{body}:t{body_type}"
                )
                .unwrap();
                for (_, _, captures) in clauses {
                    for capture in captures {
                        capture.write(output, depth + 1);
                    }
                }
                for capture in shared_clause_captures {
                    capture.write(output, depth + 1);
                }
                for capture in body_captures {
                    capture.write(output, depth + 1);
                }
            }
            ExprKind::Block { statements, tail } => {
                writeln!(output, "block").unwrap();
                for statement in statements {
                    match statement {
                        Stmt::Let {
                            local,
                            name,
                            ty,
                            span,
                            value,
                        } => {
                            writeln!(
                                output,
                                "{pad}  let l{local} {name:?}:t{ty} @{}..{}",
                                span.start, span.end
                            )
                            .unwrap();
                            value.write(output, depth + 2);
                        }
                        Stmt::Deconstruct {
                            source,
                            source_name,
                            ty,
                            fields,
                            span,
                        } => {
                            writeln!(
                                output,
                                "{pad}  deconstruct l{source} {source_name:?}:t{ty} @{}..{}",
                                span.start, span.end
                            )
                            .unwrap();
                            for field in fields {
                                if let (Some(local), Some(name)) = (field.local, &field.name) {
                                    writeln!(
                                        output,
                                        "{pad}    field#{} -> l{local} {name:?}:t{} @{}..{}",
                                        field.field, field.ty, field.span.start, field.span.end
                                    )
                                    .unwrap();
                                } else {
                                    writeln!(
                                        output,
                                        "{pad}    field#{} -> destroy{}:t{} @{}..{}",
                                        field.field,
                                        if field.erased { "-erased" } else { "" },
                                        field.ty,
                                        field.span.start,
                                        field.span.end
                                    )
                                    .unwrap();
                                }
                            }
                        }
                        Stmt::Assign {
                            destination,
                            value,
                            destroy_old,
                            span,
                        } => {
                            value.write(output, depth + 2);
                            match &destination.root {
                                AssignmentRoot::Local {
                                    local, name, ty, ..
                                } => writeln!(
                                    output,
                                    "{pad}  assign l{local} {name:?}:t{ty} destroy-old={destroy_old} @{}..{}",
                                    span.start, span.end
                                )
                                .unwrap(),
                                AssignmentRoot::DereferenceLocal {
                                    local,
                                    name,
                                    reference,
                                    referent,
                                } => {
                                    writeln!(
                                        output,
                                        "{pad}  assign *l{local} {name:?}:t{reference}->t{referent} destroy-old={destroy_old} @{}..{}",
                                        span.start, span.end
                                    )
                                    .unwrap();
                                }
                                AssignmentRoot::Dereference {
                                    reference,
                                    referent,
                                } => {
                                    writeln!(
                                        output,
                                        "{pad}  assign *:t{referent} destroy-old={destroy_old} @{}..{}",
                                        span.start, span.end
                                    )
                                    .unwrap();
                                    reference.write(output, depth + 2);
                                }
                            }
                            for projection in &destination.projections {
                                writeln!(
                                    output,
                                    "{pad}    .#{}:t{} @{}..{}",
                                    projection.field,
                                    projection.ty,
                                    projection.span.start,
                                    projection.span.end
                                )
                                .unwrap();
                            }
                        }
                        Stmt::EndBorrow {
                            local,
                            region,
                            span,
                        } => {
                            writeln!(
                                output,
                                "{pad}  end-borrow l{local} r{region} @{}..{}",
                                span.start, span.end
                            )
                            .unwrap();
                        }
                        Stmt::Expr(value) => value.write(output, depth + 1),
                    }
                }
                writeln!(output, "{pad}  tail").unwrap();
                tail.write(output, depth + 2);
            }
        }
    }
}

pub(crate) fn stable_fingerprint(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}
