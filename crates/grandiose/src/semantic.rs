//! Compiler-owned semantic side tables for editor and build-tool consumers.
//!
//! These tables are derived from successfully elaborated typed Core. They are
//! therefore never a substitute parser or a lexical name-resolution fallback.

use std::collections::BTreeMap;

use grandiose_vm::{Type, TypeId};
use serde::Serialize;

use crate::CompiledPhases;
use crate::compiler_core::{
    AssignmentRoot, DecisionBinding, Expr, ExprKind, Function, LocalId, Stmt,
};
use crate::lossless::{LosslessKind, lex_lossless};
use crate::source_bundle::SourceBundle;
use crate::span::Span;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SemanticLocal {
    pub body_identity: String,
    pub identity: String,
    pub name: String,
    pub file: String,
    pub definition_start_byte: usize,
    pub definition_end_byte: usize,
    pub scope_start_byte: usize,
    pub scope_end_byte: usize,
    pub inferred_type: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SemanticLocalOccurrence {
    pub body_identity: String,
    pub identity: String,
    pub file: String,
    pub start_byte: usize,
    pub end_byte: usize,
    pub definition: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SemanticExpressionType {
    pub body_identity: String,
    pub file: String,
    pub start_byte: usize,
    pub end_byte: usize,
    pub inferred_type: String,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct SemanticSnapshot {
    pub bodies: Vec<SemanticBodySnapshot>,
    pub locals: Vec<SemanticLocal>,
    pub occurrences: Vec<SemanticLocalOccurrence>,
    pub expressions: Vec<SemanticExpressionType>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct SemanticBodySnapshot {
    pub identity: String,
    pub file: String,
    pub start_byte: usize,
    pub end_byte: usize,
    pub source_fingerprint: u64,
    pub locals: Vec<SemanticLocal>,
    pub occurrences: Vec<SemanticLocalOccurrence>,
    pub expressions: Vec<SemanticExpressionType>,
}

struct Collector<'a> {
    bundle: &'a SourceBundle,
    phases: &'a CompiledPhases,
    function: &'a Function,
    body_identity: String,
    names: BTreeMap<LocalId, String>,
    identities: BTreeMap<LocalId, String>,
    locals: Vec<SemanticLocal>,
    occurrences: Vec<SemanticLocalOccurrence>,
    expressions: Vec<SemanticExpressionType>,
}

#[derive(Clone, Copy)]
struct BindingSite {
    span: Span,
    scope: Span,
    live_after: Option<Span>,
    last_name: bool,
}

impl<'a> Collector<'a> {
    fn identity(&self, local: LocalId) -> String {
        self.identities.get(&local).cloned().unwrap_or_else(|| {
            format!(
                "local:{}:{}:{}",
                self.function.declaration, self.function.name, local
            )
        })
    }

    fn type_name(&self, ty: TypeId) -> String {
        render_type(&self.phases.artifact.types, ty, 0)
    }

    fn mapped_name(&self, span: Span, name: &str, last: bool) -> Option<(String, usize, usize)> {
        let mapped = self.bundle.map_span(span)?;
        let source = mapped.segment.source();
        let range = mapped.span.range();
        let text = source.get(range.clone())?;
        let tokens = lex_lossless(text).ok()?;
        let mut matches = tokens.into_iter().filter(|token| {
            matches!(
                token.kind,
                LosslessKind::Identifier | LosslessKind::Label | LosslessKind::Lifetime
            ) && token.text(text).trim_start_matches(['@', '\'']) == name
        });
        let token = if last {
            matches.next_back()?
        } else {
            matches.next()?
        };
        let prefix = usize::from(matches!(
            token.kind,
            LosslessKind::Label | LosslessKind::Lifetime
        ));
        Some((
            mapped.segment.name().to_string(),
            range.start + token.span.start + prefix,
            range.start + token.span.end,
        ))
    }

    fn define(&mut self, local: LocalId, name: &str, ty: TypeId, site: BindingSite) {
        let Some((file, start, end)) = self.mapped_name(site.span, name, site.last_name) else {
            return;
        };
        let Some(mapped_scope) = self.bundle.map_span(site.scope) else {
            return;
        };
        if mapped_scope.segment.name() != file {
            return;
        }
        let identity = format!("local:{file}:{start}:{end}");
        self.names.insert(local, name.to_string());
        self.identities.insert(local, identity.clone());
        let live_start = site
            .live_after
            .and_then(|span| self.bundle.map_span(span))
            .filter(|mapped| mapped.segment.name() == file)
            .map_or(mapped_scope.span.start, |mapped| mapped.span.end);
        self.locals.push(SemanticLocal {
            body_identity: self.body_identity.clone(),
            identity: identity.clone(),
            name: name.to_string(),
            file: file.clone(),
            definition_start_byte: start,
            definition_end_byte: end,
            scope_start_byte: live_start,
            scope_end_byte: mapped_scope.span.end,
            inferred_type: self.type_name(ty),
        });
        self.occurrences.push(SemanticLocalOccurrence {
            body_identity: self.body_identity.clone(),
            identity,
            file,
            start_byte: start,
            end_byte: end,
            definition: true,
        });
    }

    fn reference(&mut self, local: LocalId, span: Span, last: bool) {
        let Some(name) = self.names.get(&local).cloned() else {
            return;
        };
        let Some((file, start, end)) = self.mapped_name(span, &name, last) else {
            return;
        };
        self.occurrences.push(SemanticLocalOccurrence {
            body_identity: self.body_identity.clone(),
            identity: self.identity(local),
            file,
            start_byte: start,
            end_byte: end,
            definition: false,
        });
    }

    fn expression_type(&mut self, expression: &Expr) {
        let Some(mapped) = self.bundle.map_span(expression.span) else {
            return;
        };
        self.expressions.push(SemanticExpressionType {
            body_identity: self.body_identity.clone(),
            file: mapped.segment.name().to_string(),
            start_byte: mapped.span.start,
            end_byte: mapped.span.end,
            inferred_type: self.type_name(expression.ty),
        });
    }

    fn collect_definitions(&mut self, expression: &Expr) {
        if let ExprKind::Block { statements, tail } = &expression.kind {
            for statement in statements {
                match statement {
                    Stmt::Let {
                        local,
                        name,
                        ty,
                        span,
                        value,
                    } => {
                        self.collect_definitions(value);
                        self.define(
                            *local,
                            name,
                            *ty,
                            BindingSite {
                                span: *span,
                                scope: expression.span,
                                live_after: Some(*span),
                                last_name: false,
                            },
                        );
                    }
                    Stmt::Deconstruct { fields, span, .. } => {
                        for field in fields {
                            if let (Some(local), Some(name)) = (field.local, field.name.as_deref())
                            {
                                self.define(
                                    local,
                                    name,
                                    field.ty,
                                    BindingSite {
                                        span: field.span,
                                        scope: expression.span,
                                        live_after: Some(*span),
                                        last_name: true,
                                    },
                                );
                            }
                        }
                    }
                    Stmt::Assign { value, .. } | Stmt::Expr(value) => {
                        self.collect_definitions(value);
                    }
                    Stmt::EndBorrow { .. } => {}
                }
            }
            self.collect_definitions(tail);
        }
        if let ExprKind::RefinementBranch {
            bindings,
            positive,
            negative,
            ..
        } = &expression.kind
        {
            for DecisionBinding {
                local,
                name,
                ty,
                span,
                ..
            } in bindings
            {
                self.define(
                    *local,
                    name,
                    *ty,
                    BindingSite {
                        span: *span,
                        scope: positive.span,
                        live_after: None,
                        last_name: true,
                    },
                );
            }
            self.collect_definitions(positive);
            self.collect_definitions(negative);
        }
        for child in expression_children(expression) {
            if !matches!(
                expression.kind,
                ExprKind::Block { .. } | ExprKind::RefinementBranch { .. }
            ) {
                self.collect_definitions(child);
            }
        }
    }

    fn collect_uses(&mut self, expression: &Expr) {
        self.expression_type(expression);
        match &expression.kind {
            ExprKind::Local { local, .. }
            | ExprKind::Move { local }
            | ExprKind::LocalReferenceView { local } => {
                self.reference(*local, expression.span, false)
            }
            ExprKind::Borrow { source, .. }
            | ExprKind::ProjectBorrow { source, .. }
            | ExprKind::Reborrow { source, .. }
            | ExprKind::DerefCopy { source }
            | ExprKind::DerefMove { source } => self.reference(*source, expression.span, false),
            ExprKind::PatternTestBorrowed { reference, .. } => {
                self.reference(*reference, expression.span, false)
            }
            ExprKind::Block { statements, .. } => {
                for statement in statements {
                    if let Stmt::Deconstruct {
                        source,
                        source_name: _,
                        span,
                        ..
                    } = statement
                    {
                        self.reference(*source, *span, true);
                    }
                    if let Stmt::Assign {
                        destination, span, ..
                    } = statement
                    {
                        match &destination.root {
                            AssignmentRoot::Local { local, .. }
                            | AssignmentRoot::DereferenceLocal { local, .. } => {
                                self.reference(*local, *span, false)
                            }
                            AssignmentRoot::Dereference { reference, .. } => {
                                self.collect_uses(reference)
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        for child in expression_children(expression) {
            self.collect_uses(child);
        }
    }
}

/// Export exact local binding/reference and expression-type tables from a
/// successful compiler result. Callers must publish this snapshot atomically
/// with the compilation transaction that produced `phases`.
pub fn semantic_snapshot(bundle: &SourceBundle, phases: &CompiledPhases) -> SemanticSnapshot {
    let mut snapshot = SemanticSnapshot::default();
    for function in &phases.core.functions {
        let body_identity = format!("body:{}", function.name);
        let mut collector = Collector {
            bundle,
            phases,
            function,
            body_identity,
            names: BTreeMap::new(),
            identities: BTreeMap::new(),
            locals: Vec::new(),
            occurrences: Vec::new(),
            expressions: Vec::new(),
        };
        for param in &function.params {
            collector.define(
                param.local,
                &param.name,
                param.ty,
                BindingSite {
                    span: param.span,
                    scope: function.body.span,
                    live_after: None,
                    last_name: false,
                },
            );
        }
        collector.collect_definitions(&function.body);
        collector.collect_uses(&function.body);
        snapshot.locals.extend(collector.locals);
        snapshot.occurrences.extend(collector.occurrences);
        snapshot.expressions.extend(collector.expressions);
    }
    snapshot.locals.sort_by(|left, right| {
        (&left.file, left.definition_start_byte, &left.identity).cmp(&(
            &right.file,
            right.definition_start_byte,
            &right.identity,
        ))
    });
    snapshot
        .locals
        .dedup_by(|left, right| left.identity == right.identity);
    snapshot.occurrences.sort_by(|left, right| {
        (&left.file, left.start_byte, left.end_byte, &left.identity).cmp(&(
            &right.file,
            right.start_byte,
            right.end_byte,
            &right.identity,
        ))
    });
    snapshot.occurrences.dedup();
    let mut expression_types = BTreeMap::<(String, usize, usize), Option<(String, String)>>::new();
    for expression in std::mem::take(&mut snapshot.expressions) {
        let key = (expression.file, expression.start_byte, expression.end_byte);
        expression_types
            .entry(key)
            .and_modify(|known| {
                if let Some((body_identity, inferred_type)) = known {
                    if inferred_type != &expression.inferred_type {
                        *known = None;
                    } else if expression.body_identity < *body_identity {
                        *body_identity = expression.body_identity.clone();
                    }
                }
            })
            .or_insert(Some((expression.body_identity, expression.inferred_type)));
    }
    snapshot.expressions = expression_types
        .into_iter()
        .filter_map(|((file, start_byte, end_byte), evidence)| {
            evidence.map(|(body_identity, inferred_type)| SemanticExpressionType {
                body_identity,
                file,
                start_byte,
                end_byte,
                inferred_type,
            })
        })
        .collect();
    let mut bodies = BTreeMap::<String, SemanticBodySnapshot>::new();
    for function in &phases.core.functions {
        let identity = format!("body:{}", function.name);
        let Some(mapped) = bundle.map_span(function.body.span) else {
            continue;
        };
        let source = mapped.segment.source();
        let start = mapped.span.start.min(source.len());
        let end = mapped.span.end.min(source.len());
        let fingerprint = fnv1a64(source.get(start..end).unwrap_or_default().as_bytes());
        bodies
            .entry(identity.clone())
            .or_insert_with(|| SemanticBodySnapshot {
                identity,
                file: mapped.segment.name().to_string(),
                start_byte: start,
                end_byte: end,
                source_fingerprint: fingerprint,
                locals: snapshot
                    .locals
                    .iter()
                    .filter(|local| local.body_identity == format!("body:{}", function.name))
                    .cloned()
                    .collect(),
                occurrences: snapshot
                    .occurrences
                    .iter()
                    .filter(|occurrence| {
                        occurrence.body_identity == format!("body:{}", function.name)
                    })
                    .cloned()
                    .collect(),
                expressions: snapshot
                    .expressions
                    .iter()
                    .filter(|expression| {
                        expression.body_identity == format!("body:{}", function.name)
                    })
                    .cloned()
                    .collect(),
            });
    }
    snapshot.bodies = bodies.into_values().collect();
    snapshot
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn expression_children(expression: &Expr) -> Vec<&Expr> {
    match &expression.kind {
        ExprKind::TemporaryProjectBorrow { source, .. }
        | ExprKind::LabelDestination { body: source, .. }
        | ExprKind::Leave { value: source, .. }
        | ExprKind::PatternTest {
            subject: source, ..
        }
        | ExprKind::Project {
            subject: source, ..
        }
        | ExprKind::Cancel { resumption: source } => vec![source],
        ExprKind::Call { args, .. }
        | ExprKind::TailCall { args, .. }
        | ExprKind::CallSelf { args }
        | ExprKind::TailCallSelf { args }
        | ExprKind::MakeCallable { captures: args, .. }
        | ExprKind::Primitive { args, .. }
        | ExprKind::HostCall { args, .. }
        | ExprKind::Perform { payloads: args, .. } => args.iter().collect(),
        ExprKind::CallKnownReceiver { receiver, args, .. }
        | ExprKind::TailCallKnownReceiver { receiver, args, .. } => {
            std::iter::once(receiver.as_ref()).chain(args).collect()
        }
        ExprKind::CallIndirect { callable, args, .. }
        | ExprKind::TailCallIndirect { callable, args, .. } => {
            std::iter::once(callable.as_ref()).chain(args).collect()
        }
        ExprKind::RefinementBranch {
            subject,
            positive,
            negative,
            ..
        } => vec![subject, positive, negative],
        ExprKind::Construct { fields, .. } => fields.iter().map(|field| &field.value).collect(),
        ExprKind::Resume {
            resumption, value, ..
        }
        | ExprKind::TailResume { resumption, value } => vec![resumption, value],
        ExprKind::Handle {
            clauses,
            shared_clause_captures,
            body_captures,
            ..
        } => clauses
            .iter()
            .flat_map(|(_, _, captures)| captures)
            .chain(shared_clause_captures)
            .chain(body_captures)
            .collect(),
        ExprKind::Block { statements, tail } => statements
            .iter()
            .filter_map(|statement| match statement {
                Stmt::Let { value, .. } | Stmt::Assign { value, .. } | Stmt::Expr(value) => {
                    Some(value)
                }
                Stmt::Deconstruct { .. } | Stmt::EndBorrow { .. } => None,
            })
            .chain(std::iter::once(tail.as_ref()))
            .collect(),
        ExprKind::Unit
        | ExprKind::Constant(_)
        | ExprKind::Local { .. }
        | ExprKind::Move { .. }
        | ExprKind::Borrow { .. }
        | ExprKind::ProjectBorrow { .. }
        | ExprKind::Reborrow { .. }
        | ExprKind::DerefCopy { .. }
        | ExprKind::DerefMove { .. }
        | ExprKind::Receiver
        | ExprKind::PatternTestBorrowed { .. }
        | ExprKind::LocalReferenceView { .. }
        | ExprKind::HostLeafStub
        | ExprKind::Abort { .. } => Vec::new(),
    }
}

fn render_type(types: &[Type], id: TypeId, depth: usize) -> String {
    if depth > 12 {
        return format!("type#{id}");
    }
    let Some(ty) = types.get(id as usize) else {
        return format!("type#{id}");
    };
    let nested = |id| render_type(types, id, depth + 1);
    match ty {
        Type::Restricted { base, .. } => render_inline_type(types, base, depth + 1),
        Type::Unit => "()".into(),
        Type::Never => "!".into(),
        Type::U8 => "u8".into(),
        Type::U16 => "u16".into(),
        Type::U32 => "u32".into(),
        Type::U64 => "u64".into(),
        Type::U128 => "u128".into(),
        Type::I8 => "i8".into(),
        Type::I16 => "i16".into(),
        Type::I32 => "i32".into(),
        Type::I64 => "i64".into(),
        Type::I128 => "i128".into(),
        Type::Usize => "usize".into(),
        Type::Isize => "isize".into(),
        Type::F32 => "f32".into(),
        Type::F64 => "f64".into(),
        Type::Char => "char".into(),
        Type::Text => "String".into(),
        Type::Bytes => "Bytes".into(),
        Type::Array { element } => format!("Array<{}>", nested(*element)),
        Type::RefShared { referent } => format!("&{}", nested(*referent)),
        Type::RefUnique { referent } => format!("&unique {}", nested(*referent)),
        Type::Callable { identity_name, .. }
        | Type::Handler { identity_name, .. }
        | Type::Resumption { identity_name, .. }
        | Type::BindingPack { identity_name, .. }
        | Type::Available { identity_name } => identity_name.clone(),
        Type::Tuple { fields, .. } => format!(
            "({})",
            fields
                .iter()
                .map(|field| nested(*field))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Struct { name, .. } | Type::Enum { name, .. } => name.clone(),
    }
}

fn render_inline_type(types: &[Type], ty: &Type, depth: usize) -> String {
    if let Some((id, _)) = types
        .iter()
        .enumerate()
        .find(|(_, candidate)| *candidate == ty)
    {
        render_type(types, id as TypeId, depth)
    } else {
        format!("{ty:?}")
    }
}
