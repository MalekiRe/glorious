//! Stable, allocation-independent typing evidence for the monomorphic compiler slice.
//!
//! This pass deliberately does not own borrow checking, effect capture planning, or
//! runtime descriptor allocation.  Its keys and types are suitable for discovering
//! requirements before numeric bytecode identifiers exist.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::ops::ControlFlow;

use grandiose_vm::bytecode::NEVER;
use grandiose_vm::{BYTES, CHAR, F32, F64, I64, Primitive, TEXT, TypeId, U8, UNIT};

use crate::ast::{
    AssignmentPlace, AssignmentPlaceKind, BinaryOp, ConstKind, Expr, ExprKind, ExprVisitor,
    GenericParamKind, PatternKind, Program, Stmt, TypeSyntax, TypeSyntaxKind, UnaryOp,
    pattern_field_index, walk_expr,
};
use crate::ast_visit::TypeSyntaxVisitor;
use crate::compiler_core as core;
use crate::span::Span;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Variance {
    Bivariant,
    Covariant,
    /// Callable parameter syntax is not yet represented in source types.
    #[allow(dead_code)]
    Contravariant,
    Invariant,
}

fn merge_variance(left: Variance, right: Variance) -> Variance {
    use Variance::*;
    match (left, right) {
        (Bivariant, value) | (value, Bivariant) => value,
        (Invariant, _) | (_, Invariant) => Invariant,
        (Covariant, Covariant) => Covariant,
        (Contravariant, Contravariant) => Contravariant,
        (Covariant, Contravariant) | (Contravariant, Covariant) => Invariant,
    }
}

fn compose_variance(context: Variance, parameter: Variance) -> Variance {
    use Variance::*;
    match (context, parameter) {
        (_, Bivariant) | (Bivariant, _) => Bivariant,
        (Invariant, _) | (_, Invariant) => Invariant,
        (Covariant, value) => value,
        (Contravariant, Covariant) => Contravariant,
        (Contravariant, Contravariant) => Covariant,
    }
}

/// Computes declaration-order-independent variance evidence for nominal type
/// and lifetime parameters. Unknown/projection positions are conservatively
/// invariant when they mention a parameter.
pub(crate) fn infer_nominal_variance(program: &Program) -> BTreeMap<String, Vec<Variance>> {
    let declarations = program
        .structs
        .iter()
        .map(|declaration| {
            (
                declaration.name.as_str(),
                declaration.generics.as_ref(),
                declaration
                    .fields
                    .iter()
                    .map(|field| &field.ty)
                    .collect::<Vec<_>>(),
            )
        })
        .chain(program.enums.iter().map(|declaration| {
            (
                declaration.name.as_str(),
                declaration.generics.as_ref(),
                declaration
                    .variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .collect::<Vec<_>>(),
            )
        }))
        .collect::<Vec<_>>();
    let mut evidence = declarations
        .iter()
        .map(|(name, generics, _)| {
            (
                (*name).to_owned(),
                generics
                    .map(|generics| vec![Variance::Bivariant; generics.params.len()])
                    .unwrap_or_default(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    fn mentions(program: &Program, syntax: &TypeSyntax, name: &str) -> bool {
        struct Mentions<'a> {
            name: &'a str,
        }
        impl TypeSyntaxVisitor for Mentions<'_> {
            type Break = ();

            fn visit_type(&mut self, syntax: &TypeSyntax) -> ControlFlow<()> {
                let direct = syntax.simple_name() == Some(self.name)
                    || matches!(&syntax.kind,
                        TypeSyntaxKind::SharedReference { lifetime: Some(lifetime), .. }
                        | TypeSyntaxKind::UniqueReference { lifetime: Some(lifetime), .. }
                        if lifetime.name == self.name)
                    || matches!(&syntax.kind, TypeSyntaxKind::Application { lifetime_arguments, .. }
                        if lifetime_arguments.iter().any(|argument| argument.lifetime.name == self.name))
                    || matches!(&syntax.kind, TypeSyntaxKind::Projection { trait_ref, arguments, .. }
                        if trait_ref.arguments.iter().any(|argument| matches!(argument,
                            crate::ast::GoalArgument::Lifetime { name, .. } if name == self.name))
                        || arguments.iter().any(|argument| matches!(argument,
                            crate::ast::AssociatedArgumentSyntax::Lifetime { name, .. } if name == self.name)));
                if direct {
                    ControlFlow::Break(())
                } else {
                    crate::ast_visit::walk_type(self, syntax)
                }
            }
        }
        let _ = program;
        Mentions { name }.visit_type(syntax).is_break()
    }

    fn visit(
        program: &Program,
        syntax: &TypeSyntax,
        context: Variance,
        params: &BTreeMap<&str, usize>,
        evidence: &BTreeMap<String, Vec<Variance>>,
        found: &mut [Variance],
    ) {
        if let Some(name) = syntax.simple_name() {
            if let Some(index) = params.get(name) {
                found[*index] = merge_variance(found[*index], context);
            }
            return;
        }
        match &syntax.kind {
            TypeSyntaxKind::SharedReference {
                lifetime,
                referent: inner,
            } => {
                if let Some(lifetime) = lifetime
                    && let Some(index) = params.get(lifetime.name.as_str())
                {
                    found[*index] = merge_variance(found[*index], context);
                }
                visit(program, inner, context, params, evidence, found)
            }
            TypeSyntaxKind::UniqueReference {
                lifetime,
                referent: inner,
            } => {
                let invariant = compose_variance(context, Variance::Invariant);
                if let Some(lifetime) = lifetime
                    && let Some(index) = params.get(lifetime.name.as_str())
                {
                    found[*index] = merge_variance(found[*index], invariant);
                }
                visit(program, inner, invariant, params, evidence, found)
            }
            TypeSyntaxKind::Tuple(elements) => {
                for element in elements {
                    visit(program, element, context, params, evidence, found);
                }
            }
            TypeSyntaxKind::Application {
                constructor,
                arguments,
                lifetime_arguments,
            } => {
                if let Some(variances) = constructor
                    .simple_name()
                    .and_then(|name| evidence.get(name))
                {
                    let const_positions = program
                        .type_const_arguments(syntax.span)
                        .iter()
                        .map(|argument| argument.position)
                        .collect::<BTreeSet<_>>();
                    let lifetime_by_position = lifetime_arguments
                        .iter()
                        .map(|argument| (argument.position, &argument.lifetime))
                        .collect::<BTreeMap<_, _>>();
                    let mut source_types = arguments.iter();
                    for (position, variance) in variances.iter().enumerate() {
                        let nested = compose_variance(context, *variance);
                        if let Some(lifetime) = lifetime_by_position.get(&position) {
                            if let Some(index) = params.get(lifetime.name.as_str()) {
                                found[*index] = merge_variance(found[*index], nested);
                            }
                        } else if !const_positions.contains(&position)
                            && let Some(argument) = source_types.next()
                        {
                            visit(program, argument, nested, params, evidence, found);
                        }
                    }
                } else {
                    for argument in arguments.iter() {
                        for (name, index) in params {
                            if mentions(program, argument, name) {
                                found[*index] = merge_variance(found[*index], Variance::Invariant);
                            }
                        }
                    }
                    for argument in lifetime_arguments {
                        if let Some(index) = params.get(argument.lifetime.name.as_str()) {
                            found[*index] = merge_variance(found[*index], Variance::Invariant);
                        }
                    }
                }
            }
            TypeSyntaxKind::Projection { .. } => {
                for (name, index) in params {
                    if mentions(program, syntax, name) {
                        found[*index] = merge_variance(found[*index], Variance::Invariant);
                    }
                }
            }
            TypeSyntaxKind::Path(_) | TypeSyntaxKind::Never => {}
        }
    }

    loop {
        let previous = evidence.clone();
        for (name, generics, fields) in &declarations {
            let Some(generics) = generics else { continue };
            let params = generics
                .params
                .iter()
                .enumerate()
                .filter(|(_, parameter)| {
                    matches!(
                        parameter.kind,
                        GenericParamKind::Type | GenericParamKind::Lifetime
                    )
                })
                .map(|(index, parameter)| (parameter.name.as_str(), index))
                .collect::<BTreeMap<_, _>>();
            let mut found = vec![Variance::Bivariant; generics.params.len()];
            for field in fields {
                visit(
                    program,
                    field,
                    Variance::Covariant,
                    &params,
                    &previous,
                    &mut found,
                );
            }
            evidence.insert((*name).to_owned(), found);
        }
        if evidence == previous {
            return evidence;
        }
    }
}

/// Finds the variance of each source lifetime occurring in a concrete type.
/// This is kept in source space because runtime nominal identity deliberately
/// erases lifetimes.
pub(crate) fn type_lifetime_variance(
    program: &Program,
    syntax: &TypeSyntax,
    nominal_variance: &BTreeMap<String, Vec<Variance>>,
) -> BTreeMap<String, Variance> {
    fn record(found: &mut BTreeMap<String, Variance>, name: &str, variance: Variance) {
        if name != "'_" {
            found
                .entry(name.to_owned())
                .and_modify(|current| *current = merge_variance(*current, variance))
                .or_insert(variance);
        }
    }

    fn visit(
        program: &Program,
        syntax: &TypeSyntax,
        context: Variance,
        nominal_variance: &BTreeMap<String, Vec<Variance>>,
        found: &mut BTreeMap<String, Variance>,
    ) {
        match &syntax.kind {
            TypeSyntaxKind::SharedReference { lifetime, referent } => {
                if let Some(lifetime) = lifetime {
                    record(found, &lifetime.name, context);
                }
                visit(program, referent, context, nominal_variance, found);
            }
            TypeSyntaxKind::UniqueReference { lifetime, referent } => {
                let invariant = compose_variance(context, Variance::Invariant);
                if let Some(lifetime) = lifetime {
                    record(found, &lifetime.name, invariant);
                }
                visit(program, referent, invariant, nominal_variance, found);
            }
            TypeSyntaxKind::Tuple(elements) => {
                for element in elements {
                    visit(program, element, context, nominal_variance, found);
                }
            }
            TypeSyntaxKind::Application {
                constructor,
                arguments,
                lifetime_arguments,
            } => {
                let variances = constructor
                    .simple_name()
                    .and_then(|name| nominal_variance.get(name));
                let const_positions = program
                    .type_const_arguments(syntax.span)
                    .iter()
                    .map(|argument| argument.position)
                    .collect::<BTreeSet<_>>();
                let lifetime_by_position = lifetime_arguments
                    .iter()
                    .map(|argument| (argument.position, &argument.lifetime))
                    .collect::<BTreeMap<_, _>>();
                let positions = variances.map_or(
                    arguments.len() + lifetime_arguments.len() + const_positions.len(),
                    Vec::len,
                );
                let mut source_types = arguments.iter();
                for position in 0..positions {
                    let parameter = variances
                        .and_then(|variances| variances.get(position))
                        .copied()
                        .unwrap_or(Variance::Invariant);
                    let nested = compose_variance(context, parameter);
                    if let Some(lifetime) = lifetime_by_position.get(&position) {
                        record(found, &lifetime.name, nested);
                    } else if !const_positions.contains(&position)
                        && let Some(argument) = source_types.next()
                    {
                        visit(program, argument, nested, nominal_variance, found);
                    }
                }
            }
            TypeSyntaxKind::Projection {
                subject,
                trait_ref,
                arguments,
                ..
            } => {
                visit(
                    program,
                    subject,
                    Variance::Invariant,
                    nominal_variance,
                    found,
                );
                for argument in &trait_ref.arguments {
                    match argument {
                        crate::ast::GoalArgument::Type(argument) => visit(
                            program,
                            argument,
                            Variance::Invariant,
                            nominal_variance,
                            found,
                        ),
                        crate::ast::GoalArgument::Lifetime { name, .. } => {
                            record(found, name, Variance::Invariant)
                        }
                        _ => {}
                    }
                }
                for argument in arguments {
                    match argument {
                        crate::ast::AssociatedArgumentSyntax::Type(argument) => visit(
                            program,
                            argument,
                            Variance::Invariant,
                            nominal_variance,
                            found,
                        ),
                        crate::ast::AssociatedArgumentSyntax::Lifetime { name, .. } => {
                            record(found, name, Variance::Invariant)
                        }
                    }
                }
            }
            TypeSyntaxKind::Path(_) | TypeSyntaxKind::Never => {}
        }
    }

    let mut found = BTreeMap::new();
    visit(
        program,
        syntax,
        Variance::Covariant,
        nominal_variance,
        &mut found,
    );
    found
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ProvisionalConst {
    U32(u32),
    Quantity { lower: u32, upper: Option<u32> },
    Rigid { index: u32, kind: ConstKind },
}

impl ProvisionalConst {
    pub(crate) fn encoded_name(&self) -> String {
        match self {
            Self::U32(value) => format!("$const$u32${value}"),
            Self::Quantity { lower, upper } => format!(
                "$const$quantity${lower}${}",
                upper.map_or_else(|| "infinity".to_owned(), |upper| upper.to_string())
            ),
            Self::Rigid { index, kind } => format!("$const$rigid${kind:?}${index}"),
        }
    }

    pub(crate) fn decode_encoded_name(name: &str) -> Option<Self> {
        if let Some(value) = name.strip_prefix("$const$u32$") {
            return Some(Self::U32(value.parse().ok()?));
        }
        if let Some(value) = name.strip_prefix("$const$quantity$") {
            let (lower, upper) = value.split_once('$')?;
            return Some(Self::Quantity {
                lower: lower.parse().ok()?,
                upper: (upper != "infinity")
                    .then(|| upper.parse())
                    .transpose()
                    .ok()?,
            });
        }
        let value = name.strip_prefix("$const$rigid$")?;
        let (kind, index) = value.split_once('$')?;
        let kind = match kind {
            "U32" => ConstKind::U32,
            "Quantity" => ConstKind::Quantity,
            _ => return None,
        };
        Some(Self::Rigid {
            index: index.parse().ok()?,
            kind,
        })
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ProvisionalType {
    Predefined(String),
    Const(ProvisionalConst),
    Nominal(NominalInstanceKey),
    Tuple(Vec<ProvisionalType>),
    Shared(Box<Self>),
    Unique(Box<Self>),
    /// Reserved for generic specialization. Source occurrences are rejected earlier.
    #[allow(dead_code)]
    Param(GenericParamKey),
    /// Reserved for first-class callable specialization. Not produced by monomorphic Core.
    #[allow(dead_code)]
    Callable(Box<CallableShape>),
}

impl ProvisionalType {
    pub(crate) fn shared(referent: Self) -> Self {
        Self::Shared(Box::new(referent))
    }

    pub(crate) fn unique(referent: Self) -> Self {
        Self::Unique(Box::new(referent))
    }

    fn write(&self, output: &mut String) {
        match self {
            Self::Predefined(name) => output.push_str(name),
            Self::Const(value) => output.push_str(&value.encoded_name()),
            Self::Nominal(instance) => {
                write!(output, "nominal:{:?}", instance.declaration.0).unwrap();
                if !instance.arguments.is_empty() {
                    output.push('<');
                    for (index, argument) in instance.arguments.iter().enumerate() {
                        if index != 0 {
                            output.push(',');
                        }
                        argument.write(output);
                    }
                    output.push('>');
                }
            }
            Self::Tuple(elements) => {
                output.push('(');
                for element in elements {
                    element.write(output);
                    output.push(',');
                }
                output.push(')');
            }
            Self::Shared(referent) => {
                output.push('&');
                referent.write(output);
            }
            Self::Unique(referent) => {
                output.push_str("&mut ");
                referent.write(output);
            }
            Self::Param(key) => write!(output, "param:{key:?}").unwrap(),
            Self::Callable(shape) => {
                output.push_str("callable:(");
                for (index, param) in shape.params.iter().enumerate() {
                    if index != 0 {
                        output.push(',');
                    }
                    param.write(output);
                }
                output.push_str(")->");
                shape.result.write(output);
                output.push_str("/{");
                for (index, effect) in shape.effects.iter().enumerate() {
                    if index != 0 {
                        output.push(',');
                    }
                    write!(
                        output,
                        "{}:{}",
                        effect.declaration.0.len(),
                        effect.declaration.0
                    )
                    .unwrap();
                    if !effect.arguments.is_empty() {
                        output.push('<');
                        for (index, argument) in effect.arguments.iter().enumerate() {
                            if index != 0 {
                                output.push(',');
                            }
                            argument.write(output);
                        }
                        output.push('>');
                    }
                }
                output.push('}');
                if shape.infer_effects {
                    output.push('?');
                }
                if let Some(tail) = &shape.effect_tail {
                    write!(output, "|row:{tail:?}").unwrap();
                }
            }
        }
    }
}

/// Rebuilds the provisional type algebra while allowing a pass to replace any
/// node. Pass-specific binder and cycle rules belong in `fold_type`; the
/// exhaustive structural recursion stays here.
pub(crate) trait ProvisionalTypeFolder {
    type Error;

    fn fold_type(&mut self, ty: &ProvisionalType) -> Result<ProvisionalType, Self::Error> {
        fold_provisional_type_children(self, ty)
    }

    fn fold_callable_effect(
        &mut self,
        effect: &CallableEffect,
    ) -> Result<CallableEffect, Self::Error> {
        Ok(CallableEffect {
            declaration: effect.declaration.clone(),
            arguments: effect
                .arguments
                .iter()
                .map(|argument| self.fold_type(argument))
                .collect::<Result<_, _>>()?,
        })
    }
}

pub(crate) fn fold_provisional_type_children<F: ProvisionalTypeFolder + ?Sized>(
    folder: &mut F,
    ty: &ProvisionalType,
) -> Result<ProvisionalType, F::Error> {
    Ok(match ty {
        ProvisionalType::Predefined(_) | ProvisionalType::Const(_) | ProvisionalType::Param(_) => {
            ty.clone()
        }
        ProvisionalType::Nominal(instance) => ProvisionalType::Nominal(NominalInstanceKey {
            declaration: instance.declaration.clone(),
            arguments: instance
                .arguments
                .iter()
                .map(|argument| folder.fold_type(argument))
                .collect::<Result<_, _>>()?,
        }),
        ProvisionalType::Tuple(elements) => ProvisionalType::Tuple(
            elements
                .iter()
                .map(|element| folder.fold_type(element))
                .collect::<Result<_, _>>()?,
        ),
        ProvisionalType::Shared(referent) => ProvisionalType::shared(folder.fold_type(referent)?),
        ProvisionalType::Unique(referent) => ProvisionalType::unique(folder.fold_type(referent)?),
        ProvisionalType::Callable(shape) => ProvisionalType::Callable(Box::new(CallableShape {
            params: shape
                .params
                .iter()
                .map(|param| folder.fold_type(param))
                .collect::<Result<_, _>>()?,
            result: folder.fold_type(&shape.result)?,
            effects: shape
                .effects
                .iter()
                .map(|effect| folder.fold_callable_effect(effect))
                .collect::<Result<_, _>>()?,
            effect_tail: shape.effect_tail.clone(),
            infer_effects: shape.infer_effects,
        })),
    })
}

/// Pre-order query over every type-bearing edge, including callable effects.
/// Returning true prunes that node, which makes both `any` and negated `all`
/// queries cheap without another family of recursive matches.
pub(crate) fn provisional_type_any(
    ty: &ProvisionalType,
    predicate: &mut impl FnMut(&ProvisionalType) -> bool,
) -> bool {
    provisional_type_any_with(ty, predicate, true)
}

/// Variant for signature-only policies whose callable effect row is already
/// canonical and intentionally outside the analysis.
pub(crate) fn provisional_signature_type_any(
    ty: &ProvisionalType,
    predicate: &mut impl FnMut(&ProvisionalType) -> bool,
) -> bool {
    provisional_type_any_with(ty, predicate, false)
}

/// Applies a predicate to the immediate signature children of `ty`. Recursive
/// relations can call themselves from the predicate without causing the
/// generic traversal to revisit the same subtree.
pub(crate) fn provisional_signature_children_any(
    ty: &ProvisionalType,
    predicate: &mut impl FnMut(&ProvisionalType) -> bool,
) -> bool {
    match ty {
        ProvisionalType::Nominal(instance) => instance.arguments.iter().any(predicate),
        ProvisionalType::Tuple(elements) => elements.iter().any(predicate),
        ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
            predicate(referent)
        }
        ProvisionalType::Callable(shape) => shape
            .params
            .iter()
            .chain(std::iter::once(&shape.result))
            .any(predicate),
        ProvisionalType::Predefined(_) | ProvisionalType::Const(_) | ProvisionalType::Param(_) => {
            false
        }
    }
}

fn provisional_type_any_with(
    ty: &ProvisionalType,
    predicate: &mut impl FnMut(&ProvisionalType) -> bool,
    visit_effects: bool,
) -> bool {
    predicate(ty)
        || match ty {
            ProvisionalType::Nominal(instance) => instance
                .arguments
                .iter()
                .any(|argument| provisional_type_any_with(argument, predicate, visit_effects)),
            ProvisionalType::Tuple(elements) => elements
                .iter()
                .any(|element| provisional_type_any_with(element, predicate, visit_effects)),
            ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
                provisional_type_any_with(referent, predicate, visit_effects)
            }
            ProvisionalType::Callable(shape) => {
                shape
                    .params
                    .iter()
                    .any(|param| provisional_type_any_with(param, predicate, visit_effects))
                    || provisional_type_any_with(&shape.result, predicate, visit_effects)
                    || visit_effects
                        && shape.effects.iter().any(|effect| {
                            effect.arguments.iter().any(|argument| {
                                provisional_type_any_with(argument, predicate, visit_effects)
                            })
                        })
            }
            ProvisionalType::Predefined(_)
            | ProvisionalType::Const(_)
            | ProvisionalType::Param(_) => false,
        }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct NominalKey(pub(crate) String);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct NominalInstanceKey {
    pub(crate) declaration: NominalKey,
    pub(crate) arguments: Vec<ProvisionalType>,
}

impl NominalInstanceKey {
    pub(crate) fn monomorphic(name: impl Into<String>) -> Self {
        Self {
            declaration: NominalKey(name.into()),
            arguments: vec![],
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum DeclarationKey {
    Function(String),
    Global(String),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct GenericParamKey {
    pub(crate) owner: DeclarationKey,
    pub(crate) ordinal: u32,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct CallableShape {
    pub(crate) params: Vec<ProvisionalType>,
    pub(crate) result: ProvisionalType,
    /// Closed, canonical source-level protocol applications.  These are kept in
    /// declaration space rather than bytecode protocol-table space so closure
    /// and specialization keys do not depend on allocation order.
    pub(crate) effects: Vec<CallableEffect>,
    /// Declaration-bound open-row tail, solved to a closed residual before
    /// specialization emission.
    pub(crate) effect_tail: Option<GenericParamKey>,
    /// Declaration-side associated-row projection awaiting contextual closure
    /// elaboration. Emitted closure keys are always sealed (`false`).
    pub(crate) infer_effects: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct CallableEffect {
    pub(crate) declaration: ProtocolKey,
    pub(crate) arguments: Vec<ProvisionalType>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ProtocolKey(pub(crate) String);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct LocalKey {
    pub(crate) owner: DeclarationKey,
    pub(crate) ordinal: u32,
}

#[derive(Clone, Debug)]
pub(crate) struct FunctionShape {
    pub(crate) declaration: DeclarationKey,
    pub(crate) params: Vec<ProvisionalType>,
    pub(crate) result: ProvisionalType,
}

#[derive(Clone, Debug)]
pub(crate) enum NominalShape {
    Struct(Vec<(String, ProvisionalType)>),
    Enum(Vec<(String, Vec<ProvisionalType>)>),
}

#[derive(Clone, Debug)]
pub(crate) struct OperationShape {
    pub(crate) params: Vec<ProvisionalType>,
    pub(crate) result: ProvisionalType,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Tables {
    pub(crate) functions: BTreeMap<String, FunctionShape>,
    pub(crate) globals: BTreeMap<String, ProvisionalType>,
    pub(crate) nominals: BTreeMap<NominalInstanceKey, NominalShape>,
    pub(crate) operations: BTreeMap<(String, String), OperationShape>,
    pub(crate) operation_sites: BTreeMap<(usize, usize), OperationShape>,
}

#[derive(Clone, Debug)]
pub(crate) struct TypedProgram {
    pub(crate) bodies: BTreeMap<DeclarationKey, TypedExpr>,
    /// Allocation-independent generative label identities and destination
    /// contracts. Runtime target allocation is deliberately deferred to Core.
    pub(crate) labels: BTreeMap<DeclarationKey, Vec<LabelEvidence>>,
    /// Positive/negative pattern-test facts keyed by stable source brands.
    pub(crate) refinements: BTreeMap<DeclarationKey, Vec<RefinementEvidence>>,
    nominal_variance: BTreeMap<String, Vec<Variance>>,
    assignment_reference_requirements: BTreeSet<ProvisionalType>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct IncrementalTypeStats {
    pub(crate) elaborated_bodies: usize,
    pub(crate) reused_bodies: usize,
}

#[derive(Clone, Debug)]
struct CachedTypedBody {
    fingerprint: u64,
    body: TypedExpr,
    refinements: Vec<RefinementEvidence>,
    assignment_reference_requirements: BTreeSet<ProvisionalType>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct IncrementalTypeCache {
    context_fingerprint: Option<u64>,
    bodies: BTreeMap<DeclarationKey, CachedTypedBody>,
    pub(crate) stats: IncrementalTypeStats,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct RefinementBrand {
    pub(crate) owner: DeclarationKey,
    pub(crate) expression_ordinal: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RefinementBinding {
    pub(crate) name: String,
    pub(crate) ty: ProvisionalType,
    pub(crate) projection: Vec<u32>,
    pub(crate) span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct VariantExclusion {
    pub(crate) nominal: NominalInstanceKey,
    pub(crate) variant: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RefinementEvidence {
    pub(crate) brand: RefinementBrand,
    pub(crate) span: Span,
    pub(crate) subject_type: Option<ProvisionalType>,
    /// Bindings visible only in the positive environment selected by this
    /// pattern test. Future branch lowering consumes this exact projection map.
    pub(crate) positive_bindings: Vec<RefinementBinding>,
    /// Constructor facts available in the negative environment.
    pub(crate) negative_exclusions: Vec<VariantExclusion>,
    pub(crate) irrefutable: bool,
    pub(crate) projection_safe: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct LabelBrand {
    pub(crate) owner: DeclarationKey,
    pub(crate) ordinal: u32,
}

pub(crate) const LABEL_TYPE_PREFIX: &str = "$label$";

pub(crate) fn label_provisional_type(
    owner: &DeclarationKey,
    label: &crate::ast::LabelSyntax,
    payload: ProvisionalType,
) -> ProvisionalType {
    let owner = match owner {
        DeclarationKey::Function(name) => format!("f${name}"),
        DeclarationKey::Global(name) => format!("g${name}"),
    };
    ProvisionalType::Nominal(NominalInstanceKey {
        declaration: NominalKey(format!(
            "{LABEL_TYPE_PREFIX}{owner}${}${}",
            label.span.start, label.span.end
        )),
        arguments: vec![payload],
    })
}

pub(crate) fn label_payload_type(ty: &ProvisionalType) -> Option<&ProvisionalType> {
    let ProvisionalType::Nominal(instance) = ty else {
        return None;
    };
    (instance.declaration.0.starts_with(LABEL_TYPE_PREFIX) && instance.arguments.len() == 1)
        .then(|| &instance.arguments[0])
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LabelEvidence {
    pub(crate) brand: LabelBrand,
    pub(crate) name: String,
    pub(crate) binder_span: Span,
    /// Direct label binders always carry a result type (implicit Unit when the
    /// source annotation is omitted). `None` remains only for obsolete
    /// internal ASTs and is never produced by the source grammar.
    pub(crate) destination_result: Option<ProvisionalType>,
    pub(crate) result_contains_references: bool,
    pub(crate) references: Vec<Span>,
    pub(crate) leaves: Vec<LabelLeaveEvidence>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LabelLeaveEvidence {
    pub(crate) span: Span,
    pub(crate) value_span: Option<Span>,
    /// The destination's declared result carrier. This is the provenance
    /// contract later lowering must attach to the transferred value.
    pub(crate) result: ProvisionalType,
    pub(crate) result_contains_references: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct TypedExpr {
    pub(crate) ty: Option<ProvisionalType>,
    pub(crate) span: Span,
    pub(crate) kind: TypedExprKind,
}

#[derive(Clone, Debug)]
pub(crate) enum TypedExprKind {
    Leaf,
    Local(LocalKey),
    Global(DeclarationKey),
    Call {
        declaration: DeclarationKey,
        args: Vec<TypedExpr>,
    },
    Construct {
        nominal: NominalInstanceKey,
        variant: Option<u32>,
        fields: Vec<(u32, TypedExpr)>,
    },
    Tuple(Vec<TypedExpr>),
    Project {
        subject: Box<TypedExpr>,
        field: u32,
    },
    Primitive(Vec<TypedExpr>),
    Borrow {
        source: LocalKey,
        path: Vec<u32>,
        projection_types: Vec<ProvisionalType>,
        reborrow: bool,
        unique: bool,
    },
    Block {
        values: Vec<TypedExpr>,
        tail: Box<TypedExpr>,
    },
    EffectBoundary(Vec<TypedExpr>),
    Unsupported(Vec<TypedExpr>),
}

impl TypedProgram {
    pub(crate) fn expression_type_at(
        &self,
        declaration: &DeclarationKey,
        span: Span,
    ) -> Option<&ProvisionalType> {
        fn find(expression: &TypedExpr, span: Span) -> Option<&ProvisionalType> {
            if expression.span == span {
                return expression.ty.as_ref();
            }
            let children: Vec<&TypedExpr> = match &expression.kind {
                TypedExprKind::Call { args, .. }
                | TypedExprKind::Tuple(args)
                | TypedExprKind::Primitive(args)
                | TypedExprKind::EffectBoundary(args)
                | TypedExprKind::Unsupported(args) => args.iter().collect(),
                TypedExprKind::Construct { fields, .. } => {
                    fields.iter().map(|(_, value)| value).collect()
                }
                TypedExprKind::Project { subject, .. } => vec![subject],
                TypedExprKind::Block { values, tail } => values
                    .iter()
                    .chain(std::iter::once(tail.as_ref()))
                    .collect(),
                TypedExprKind::Leaf
                | TypedExprKind::Local(_)
                | TypedExprKind::Global(_)
                | TypedExprKind::Borrow { .. } => Vec::new(),
            };
            children.into_iter().find_map(|child| find(child, span))
        }
        self.bodies
            .get(declaration)
            .and_then(|body| find(body, span))
    }

    /// Exposes declaration evidence for the region-compatibility phase once
    /// reference types carry explicit regions.
    #[allow(dead_code)]
    pub(crate) fn nominal_variance(&self, declaration: &NominalKey) -> Option<&[Variance]> {
        self.nominal_variance.get(&declaration.0).map(Vec::as_slice)
    }

    pub(crate) fn reference_requirements(&self) -> BTreeSet<ProvisionalType> {
        fn collect(expression: &TypedExpr, found: &mut BTreeSet<ProvisionalType>) {
            if let Some(
                ty @ (ProvisionalType::Tuple(_)
                | ProvisionalType::Shared(_)
                | ProvisionalType::Unique(_)),
            ) = &expression.ty
            {
                found.insert(ty.clone());
            }
            match &expression.kind {
                TypedExprKind::Call { args, .. }
                | TypedExprKind::Primitive(args)
                | TypedExprKind::EffectBoundary(args)
                | TypedExprKind::Unsupported(args) => {
                    args.iter().for_each(|child| collect(child, found));
                }
                TypedExprKind::Construct { fields, .. } => {
                    fields.iter().for_each(|(_, child)| collect(child, found));
                }
                TypedExprKind::Tuple(values) => {
                    values.iter().for_each(|value| collect(value, found));
                }
                TypedExprKind::Project { subject, .. } => collect(subject, found),
                TypedExprKind::Block { values, tail } => {
                    values.iter().for_each(|child| collect(child, found));
                    collect(tail, found);
                }
                TypedExprKind::Leaf | TypedExprKind::Local(_) | TypedExprKind::Global(_) => {}
                TypedExprKind::Borrow {
                    projection_types, ..
                } => found.extend(projection_types.iter().cloned()),
            }
        }
        let mut found = self.assignment_reference_requirements.clone();
        self.bodies
            .values()
            .for_each(|body| collect(body, &mut found));
        found
    }

    pub(crate) fn canonical_text(&self) -> String {
        fn expression(node: &TypedExpr, depth: usize, output: &mut String) {
            let pad = "  ".repeat(depth);
            output.push_str(&pad);
            if let Some(ty) = &node.ty {
                ty.write(output);
            } else {
                output.push('?');
            }
            match &node.kind {
                TypedExprKind::Leaf => writeln!(output, " leaf").unwrap(),
                TypedExprKind::Local(key) => writeln!(output, " local#{:?}", key.ordinal).unwrap(),
                TypedExprKind::Global(key) => writeln!(output, " global {key:?}").unwrap(),
                TypedExprKind::Call { declaration, args } => {
                    writeln!(output, " call {declaration:?}").unwrap();
                    args.iter()
                        .for_each(|arg| expression(arg, depth + 1, output));
                }
                TypedExprKind::Construct {
                    nominal,
                    variant,
                    fields,
                } => {
                    writeln!(output, " construct {nominal:?} {variant:?}").unwrap();
                    fields.iter().for_each(|(field, value)| {
                        writeln!(output, "{pad}  field#{field}").unwrap();
                        expression(value, depth + 2, output);
                    });
                }
                TypedExprKind::Tuple(values) => {
                    writeln!(output, " tuple").unwrap();
                    values
                        .iter()
                        .for_each(|value| expression(value, depth + 1, output));
                }
                TypedExprKind::Project { subject, field } => {
                    writeln!(output, " project#{field}").unwrap();
                    expression(subject, depth + 1, output);
                }
                TypedExprKind::Primitive(args) => {
                    writeln!(output, " primitive").unwrap();
                    args.iter()
                        .for_each(|arg| expression(arg, depth + 1, output));
                }
                TypedExprKind::Borrow {
                    source,
                    path,
                    projection_types: _,
                    reborrow,
                    unique,
                } => {
                    writeln!(
                        output,
                        " borrow#{} path={path:?} reborrow={reborrow} unique={unique}",
                        source.ordinal,
                    )
                    .unwrap();
                }
                TypedExprKind::Block { values, tail } => {
                    writeln!(output, " block").unwrap();
                    values
                        .iter()
                        .for_each(|value| expression(value, depth + 1, output));
                    expression(tail, depth + 1, output);
                }
                TypedExprKind::EffectBoundary(children) => {
                    writeln!(output, " effect-boundary").unwrap();
                    children
                        .iter()
                        .for_each(|child| expression(child, depth + 1, output));
                }
                TypedExprKind::Unsupported(children) => {
                    writeln!(output, " unsupported").unwrap();
                    children
                        .iter()
                        .for_each(|child| expression(child, depth + 1, output));
                }
            }
        }
        let mut output = String::new();
        for (declaration, variances) in &self.nominal_variance {
            writeln!(&mut output, "variance {declaration} {variances:?}").unwrap();
        }
        for requirement in &self.assignment_reference_requirements {
            output.push_str("assignment-reference ");
            requirement.write(&mut output);
            output.push('\n');
        }
        for (owner, labels) in &self.labels {
            for label in labels {
                write!(
                    &mut output,
                    "label {owner:?}#{} @{} direct={} refs={} leaves={} result=",
                    label.brand.ordinal,
                    label.name,
                    label.destination_result.is_some(),
                    label.references.len(),
                    label.leaves.len(),
                )
                .unwrap();
                if let Some(result) = &label.destination_result {
                    result.write(&mut output);
                } else {
                    output.push('-');
                }
                writeln!(
                    &mut output,
                    " reference-result={}",
                    label.result_contains_references
                )
                .unwrap();
                for leave in &label.leaves {
                    write!(
                        &mut output,
                        "  leave {}..{} value={:?} result=",
                        leave.span.start, leave.span.end, leave.value_span
                    )
                    .unwrap();
                    leave.result.write(&mut output);
                    writeln!(
                        &mut output,
                        " reference-result={}",
                        leave.result_contains_references
                    )
                    .unwrap();
                }
            }
        }
        for (owner, refinements) in &self.refinements {
            for refinement in refinements {
                writeln!(
                    &mut output,
                    "refinement {owner:?}#{} safe={} irrefutable={} positive={} negative={}",
                    refinement.brand.expression_ordinal,
                    refinement.projection_safe,
                    refinement.irrefutable,
                    refinement.positive_bindings.len(),
                    refinement.negative_exclusions.len(),
                )
                .unwrap();
                for binding in &refinement.positive_bindings {
                    write!(
                        &mut output,
                        "  bind {} path={:?} ",
                        binding.name, binding.projection
                    )
                    .unwrap();
                    binding.ty.write(&mut output);
                    output.push('\n');
                }
                for exclusion in &refinement.negative_exclusions {
                    writeln!(
                        &mut output,
                        "  exclude {:?}#{}",
                        exclusion.nominal, exclusion.variant
                    )
                    .unwrap();
                }
            }
        }
        for (declaration, body) in &self.bodies {
            writeln!(&mut output, "body {declaration:?}").unwrap();
            expression(body, 1, &mut output);
        }
        output
    }

    pub(crate) fn fingerprint(&self) -> u64 {
        let mut hash = 0xcbf29ce484222325_u64;
        for byte in self.canonical_text().bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash
    }

    pub(crate) fn agrees_with_core(
        &self,
        declaration: &DeclarationKey,
        core: &core::Expr,
        type_id: &impl Fn(&ProvisionalType) -> Option<TypeId>,
        declaration_id: &impl Fn(&DeclarationKey) -> Option<core::DeclarationId>,
        nominal_id: &impl Fn(&NominalInstanceKey) -> Option<TypeId>,
        primitive_id: &impl Fn(&DeclarationKey) -> Option<Primitive>,
    ) -> bool {
        fn expression(
            typed: &TypedExpr,
            core: &core::Expr,
            type_id: &impl Fn(&ProvisionalType) -> Option<TypeId>,
            declaration_id: &impl Fn(&DeclarationKey) -> Option<core::DeclarationId>,
            nominal_id: &impl Fn(&NominalInstanceKey) -> Option<TypeId>,
            primitive_id: &impl Fn(&DeclarationKey) -> Option<Primitive>,
        ) -> bool {
            if typed.span != core.span {
                return false;
            }
            let effect_boundary = matches!(
                (&typed.kind, &core.kind),
                (
                    TypedExprKind::EffectBoundary(_),
                    core::ExprKind::Perform { .. } | core::ExprKind::Handle { .. }
                )
            );
            let anonymous_borrow_boundary = matches!(
                (&typed.kind, &core.kind),
                (
                    TypedExprKind::Borrow { source, .. },
                    core::ExprKind::TemporaryProjectBorrow { .. }
                ) if source.ordinal == u32::MAX
            );
            if !effect_boundary
                && !anonymous_borrow_boundary
                && typed
                    .ty
                    .as_ref()
                    .and_then(type_id)
                    .is_some_and(|expected| expected != core.ty)
            {
                return false;
            }
            let agrees = match (&typed.kind, &core.kind) {
                (TypedExprKind::Leaf, core::ExprKind::Unit | core::ExprKind::Constant(_)) => true,
                (
                    TypedExprKind::Local(_),
                    core::ExprKind::Local { local, .. } | core::ExprKind::Move { local },
                ) => {
                    // Core may allocate evaluation temporaries between source
                    // locals (for example, materializing a reference-returning
                    // call before dereference). Numeric local IDs are therefore
                    // intentionally allocation-dependent. Span and type were
                    // checked above; Core remains authoritative for the exact
                    // place identity.
                    let _ = local;
                    true
                }
                (
                    TypedExprKind::Global(declaration),
                    core::ExprKind::Call {
                        declaration: actual,
                        args,
                    }
                    | core::ExprKind::TailCall {
                        declaration: actual,
                        args,
                    },
                ) => args.is_empty() && declaration_id(declaration) == Some(*actual),
                (
                    TypedExprKind::Call { declaration, args },
                    core::ExprKind::Call {
                        declaration: actual,
                        args: lowered,
                    }
                    | core::ExprKind::TailCall {
                        declaration: actual,
                        args: lowered,
                    },
                ) => {
                    declaration_id(declaration) == Some(*actual)
                        && args.len() == lowered.len()
                        && args.iter().zip(lowered).all(|(left, right)| {
                            expression(
                                left,
                                right,
                                type_id,
                                declaration_id,
                                nominal_id,
                                primitive_id,
                            )
                        })
                }
                (
                    TypedExprKind::Call { args, .. },
                    core::ExprKind::HostCall { args: lowered, .. },
                ) => {
                    args.len() == lowered.len()
                        && args.iter().zip(lowered).all(|(left, right)| {
                            expression(
                                left,
                                right,
                                type_id,
                                declaration_id,
                                nominal_id,
                                primitive_id,
                            )
                        })
                }
                (
                    TypedExprKind::Call { declaration, args },
                    core::ExprKind::Primitive {
                        primitive,
                        args: lowered,
                    },
                ) => {
                    primitive_id(declaration) == Some(*primitive)
                        && args.len() == lowered.len()
                        && args.iter().zip(lowered).all(|(left, right)| {
                            expression(
                                left,
                                right,
                                type_id,
                                declaration_id,
                                nominal_id,
                                primitive_id,
                            )
                        })
                }
                (
                    TypedExprKind::Tuple(values),
                    core::ExprKind::Construct {
                        nominal: actual,
                        variant: None,
                        fields: lowered,
                    },
                ) => {
                    (typed.ty.as_ref().and_then(type_id) == Some(*actual)
                        || matches!(
                            &typed.ty,
                            Some(ProvisionalType::Tuple(elements))
                                if elements.iter().all(|element| matches!(element, ProvisionalType::Callable(_)))
                        )
                        || (typed.ty.is_none()
                            && values
                                .iter()
                                .any(|value| matches!(value.kind, TypedExprKind::Unsupported(_)))))
                        && values.len() == lowered.len()
                        && values
                            .iter()
                            .zip(lowered)
                            .enumerate()
                            .all(|(index, (left, right))| {
                                right.field == index as u32
                                    && expression(
                                        left,
                                        &right.value,
                                        type_id,
                                        declaration_id,
                                        nominal_id,
                                        primitive_id,
                                    )
                            })
                }
                (
                    TypedExprKind::Construct {
                        nominal,
                        variant,
                        fields,
                    },
                    core::ExprKind::Construct {
                        nominal: actual,
                        variant: actual_variant,
                        fields: lowered,
                    },
                ) => {
                    let provisional_id = nominal_id(nominal);
                    // A callable-valued generic nominal has no allocation-independent
                    // TypeId (and the provisional typer intentionally leaves its payload
                    // unsupported). Core selects its reserved exact-identity instance from
                    // the construction-site side table, so there is no shape-based fallback
                    // to validate here.
                    provisional_id.is_none()
                        || (provisional_id == Some(*actual)
                            && variant == actual_variant
                            && fields.len() == lowered.len()
                            && fields.iter().zip(lowered).all(|((field, left), right)| {
                                *field == right.field
                                    && expression(
                                        left,
                                        &right.value,
                                        type_id,
                                        declaration_id,
                                        nominal_id,
                                        primitive_id,
                                    )
                            }))
                }
                (
                    TypedExprKind::Project { subject, field },
                    core::ExprKind::Project {
                        subject: lowered,
                        field: actual,
                        ..
                    },
                ) => {
                    field == actual
                        && expression(
                            subject,
                            lowered,
                            type_id,
                            declaration_id,
                            nominal_id,
                            primitive_id,
                        )
                }
                (
                    TypedExprKind::Primitive(args),
                    core::ExprKind::Primitive { args: lowered, .. },
                ) => {
                    args.len() == lowered.len()
                        && args.iter().zip(lowered).all(|(left, right)| {
                            expression(
                                left,
                                right,
                                type_id,
                                declaration_id,
                                nominal_id,
                                primitive_id,
                            )
                        })
                }
                // Unary minus on a literal is folded while Core is constructed.
                (TypedExprKind::Primitive(args), core::ExprKind::Constant(_)) => {
                    args.len() == 1 && matches!(args[0].kind, TypedExprKind::Leaf)
                }
                (
                    TypedExprKind::Borrow {
                        source,
                        path,
                        projection_types: _,
                        reborrow,
                        unique,
                    },
                    core::ExprKind::Borrow {
                        source: actual,
                        unique: actual_unique,
                    },
                ) => {
                    !reborrow
                        && path.is_empty()
                        && source.ordinal == *actual
                        && unique == actual_unique
                }
                (
                    TypedExprKind::Borrow {
                        source,
                        path,
                        projection_types: _,
                        reborrow: false,
                        unique,
                    },
                    core::ExprKind::ProjectBorrow {
                        source: actual,
                        path: core_path,
                        unique: actual_unique,
                    },
                ) => {
                    source.ordinal == *actual
                        && path
                            .iter()
                            .copied()
                            .eq(core_path.iter().map(|step| step.field))
                        && unique == actual_unique
                }
                // The allocation-independent pass deliberately represents a
                // borrow of an anonymous owner with the sentinel local and a
                // placeholder referent. Core retains the evaluated owner in a
                // `TemporaryProjectBorrow` instead. There is no local identity
                // or child provisional expression to compare, but the sentinel
                // and borrow mode still establish the same ownership choice.
                (
                    TypedExprKind::Borrow {
                        source,
                        path,
                        reborrow,
                        unique,
                        ..
                    },
                    core::ExprKind::TemporaryProjectBorrow {
                        unique: actual_unique,
                        ..
                    },
                ) => {
                    source.ordinal == u32::MAX
                        && path.is_empty()
                        && !reborrow
                        && unique == actual_unique
                }
                (
                    TypedExprKind::Borrow {
                        source,
                        path,
                        projection_types: _,
                        reborrow,
                        unique,
                    },
                    core::ExprKind::Reborrow {
                        source: actual,
                        unique: actual_unique,
                    },
                ) => {
                    *reborrow
                        && path.is_empty()
                        && source.ordinal == *actual
                        && unique == actual_unique
                }
                (
                    TypedExprKind::Block { values, tail },
                    core::ExprKind::Block {
                        statements,
                        tail: lowered_tail,
                    },
                ) => {
                    let structural = statements
                        .iter()
                        .filter(|statement| !matches!(statement, core::Stmt::EndBorrow { .. }))
                        .collect::<Vec<_>>();
                    values.len() == structural.len()
                        && values
                            .iter()
                            .zip(structural)
                            .all(|(left, statement)| match statement {
                                core::Stmt::Let { value, .. } | core::Stmt::Expr(value) => {
                                    expression(
                                        left,
                                        value,
                                        type_id,
                                        declaration_id,
                                        nominal_id,
                                        primitive_id,
                                    )
                                }
                                core::Stmt::Deconstruct { source, .. } => {
                                    matches!(
                                        &left.kind,
                                        TypedExprKind::Local(local) if local.ordinal == *source
                                    ) || matches!(&left.kind, TypedExprKind::Unsupported(_))
                                        || matches!(
                                            &left.ty,
                                            Some(ProvisionalType::Nominal(nominal))
                                                if nominal_id(nominal).is_none()
                                        )
                                }
                                core::Stmt::Assign {
                                    destination, value, ..
                                } => {
                                    let TypedExprKind::EffectBoundary(children) = &left.kind else {
                                        return false;
                                    };
                                    children.first().is_some_and(|rhs| {
                                        expression(
                                            rhs,
                                            value,
                                            type_id,
                                            declaration_id,
                                            nominal_id,
                                            primitive_id,
                                        )
                                    }) && match &destination.root {
                                        core::AssignmentRoot::Local { .. } => children.len() == 1,
                                        core::AssignmentRoot::DereferenceLocal { .. } => {
                                            // A projected assignment through
                                            // a named `&mut` local may be
                                            // written with field auto-deref
                                            // (`owner.field = value`). The
                                            // provisional tree then has no
                                            // explicit dereference child even
                                            // though Core canonicalizes both
                                            // spellings to DereferenceLocal.
                                            matches!(children.len(), 1 | 2)
                                        }
                                        core::AssignmentRoot::Dereference { reference, .. } => {
                                            children.len() == 2
                                                && expression(
                                                    &children[1],
                                                    reference,
                                                    type_id,
                                                    declaration_id,
                                                    nominal_id,
                                                    primitive_id,
                                                )
                                        }
                                    }
                                }
                                core::Stmt::EndBorrow { .. } => unreachable!(
                                    "synthetic end-borrow statements are filtered structurally"
                                ),
                            })
                        && expression(
                            tail,
                            lowered_tail,
                            type_id,
                            declaration_id,
                            nominal_id,
                            primitive_id,
                        )
                }
                // Effect lowering deliberately changes structure and introduces synthetic
                // callable/resumption types. Children are still typed for requirements.
                (
                    TypedExprKind::EffectBoundary(_),
                    core::ExprKind::Perform { .. } | core::ExprKind::Handle { .. },
                ) => true,
                // Unsupported nodes remain under CoreLowerer's diagnostic authority.
                (TypedExprKind::Unsupported(_), _) => true,
                _ => false,
            };
            agrees
        }

        self.bodies.get(declaration).is_some_and(|typed| {
            expression(
                typed,
                core,
                type_id,
                declaration_id,
                nominal_id,
                primitive_id,
            )
        })
    }
}

pub(crate) fn predefined_named(name: impl Into<String>) -> ProvisionalType {
    ProvisionalType::Predefined(name.into())
}

fn predefined(id: TypeId) -> ProvisionalType {
    ProvisionalType::Predefined(match id {
        UNIT => "Unit".into(),
        TEXT => "Text".into(),
        I64 => "i64".into(),
        F32 => "f32".into(),
        F64 => "f64".into(),
        CHAR => "Char".into(),
        U8 => "u8".into(),
        BYTES => "Bytes".into(),
        NEVER => "Never".into(),
        _ => unreachable!("the provisional expression typer only defaults literal leaf types"),
    })
}

fn provisional_label_type(syntax: Option<&TypeSyntax>) -> Option<ProvisionalType> {
    let Some(syntax) = syntax else {
        return Some(predefined(UNIT));
    };
    match &syntax.kind {
        TypeSyntaxKind::Never => Some(predefined_named("Never")),
        TypeSyntaxKind::Path(_) => {
            let name = syntax.simple_name()?.to_owned();
            Some(
                if matches!(
                    name.as_str(),
                    "Unit"
                        | "Text"
                        | "Bytes"
                        | "Char"
                        | "f32"
                        | "f64"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                ) {
                    predefined_named(name)
                } else {
                    ProvisionalType::Nominal(NominalInstanceKey::monomorphic(name))
                },
            )
        }
        TypeSyntaxKind::Tuple(elements) => Some(ProvisionalType::Tuple(
            elements
                .iter()
                .map(|element| provisional_label_type(Some(element)))
                .collect::<Option<Vec<_>>>()?,
        )),
        TypeSyntaxKind::SharedReference { referent, .. } => Some(ProvisionalType::shared(
            provisional_label_type(Some(referent))?,
        )),
        TypeSyntaxKind::UniqueReference { referent, .. } => Some(ProvisionalType::unique(
            provisional_label_type(Some(referent))?,
        )),
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            ..
        } => Some(ProvisionalType::Nominal(NominalInstanceKey {
            declaration: NominalKey(constructor.simple_name()?.to_owned()),
            arguments: arguments
                .iter()
                .map(|argument| provisional_label_type(Some(argument)))
                .collect::<Option<Vec<_>>>()?,
        })),
        TypeSyntaxKind::Projection { .. } => None,
    }
}

fn provisional_contains_references(ty: &ProvisionalType) -> bool {
    match ty {
        ProvisionalType::Shared(_) | ProvisionalType::Unique(_) => true,
        ProvisionalType::Tuple(elements) => elements.iter().any(provisional_contains_references),
        ProvisionalType::Nominal(_)
        | ProvisionalType::Predefined(_)
        | ProvisionalType::Const(_)
        | ProvisionalType::Param(_)
        | ProvisionalType::Callable(_) => false,
    }
}

fn collect_label_evidence(owner: DeclarationKey, root: &Expr) -> Vec<LabelEvidence> {
    struct Collector<'a> {
        owner: &'a DeclarationKey,
        active: BTreeMap<String, usize>,
        evidence: Vec<LabelEvidence>,
    }

    impl Collector<'_> {
        fn bind(
            &mut self,
            label: &crate::ast::LabelSyntax,
            result: Option<ProvisionalType>,
            body: &Expr,
        ) {
            let index = self.evidence.len();
            self.evidence.push(LabelEvidence {
                brand: LabelBrand {
                    owner: self.owner.clone(),
                    ordinal: index as u32,
                },
                name: label.name.to_string(),
                binder_span: label.span,
                result_contains_references: result
                    .as_ref()
                    .is_some_and(provisional_contains_references),
                destination_result: result,
                references: vec![],
                leaves: vec![],
            });
            let previous = self.active.insert(label.name.to_string(), index);
            let _ = self.visit_expr(body);
            if let Some(previous) = previous {
                self.active.insert(label.name.to_string(), previous);
            } else {
                self.active.remove(label.name.as_ref());
            }
        }
    }

    impl<'ast> ExprVisitor<'ast> for Collector<'_> {
        type Break = ();

        fn visit_expr(&mut self, expression: &'ast Expr) -> ControlFlow<()> {
            match &expression.kind {
                ExprKind::LabelDestination { label, ty, body } => self.bind(
                    label,
                    Some(provisional_label_type(ty.as_deref()).unwrap_or_else(|| predefined(UNIT))),
                    body,
                ),
                ExprKind::LabelReference(label) => {
                    if let Some(index) = self.active.get(label.name.as_ref()).copied() {
                        self.evidence[index].references.push(label.span);
                    }
                }
                ExprKind::Call(callee, arguments)
                    if let ExprKind::LabelReference(label) = &callee.kind =>
                {
                    if let Some(index) = self.active.get(label.name.as_ref()).copied()
                        && let Some(result) = self.evidence[index].destination_result.clone()
                    {
                        self.evidence[index].leaves.push(LabelLeaveEvidence {
                            span: expression.span,
                            value_span: arguments.first().map(|value| value.span),
                            result_contains_references: provisional_contains_references(&result),
                            result,
                        });
                    }
                    for argument in arguments.iter() {
                        self.visit_expr(argument)?;
                    }
                }
                _ => walk_expr(self, expression)?,
            }
            ControlFlow::Continue(())
        }
    }

    let mut collector = Collector {
        owner: &owner,
        active: BTreeMap::new(),
        evidence: Vec::new(),
    };
    let _ = collector.visit_expr(root);
    collector.evidence
}

pub(crate) fn type_program(
    program: &Program,
    tables: &Tables,
    constructions: &BTreeMap<(DeclarationKey, u32), NominalInstanceKey>,
    call_shapes: &BTreeMap<(DeclarationKey, u32), FunctionShape>,
) -> TypedProgram {
    type_program_incremental(program, tables, constructions, call_shapes, None)
}

pub(crate) fn type_program_incremental(
    program: &Program,
    tables: &Tables,
    constructions: &BTreeMap<(DeclarationKey, u32), NominalInstanceKey>,
    call_shapes: &BTreeMap<(DeclarationKey, u32), FunctionShape>,
    incremental: Option<(
        &mut IncrementalTypeCache,
        u64,
        &BTreeMap<DeclarationKey, u64>,
    )>,
) -> TypedProgram {
    let mut incremental = incremental;
    if let Some((cache, context_fingerprint, _)) = incremental.as_mut() {
        cache.stats = IncrementalTypeStats::default();
        if cache.context_fingerprint != Some(*context_fingerprint) {
            cache.context_fingerprint = Some(*context_fingerprint);
            cache.bodies.clear();
        }
    }
    let mut tables = tables.clone();
    let mut bodies = BTreeMap::new();
    let mut refinements = BTreeMap::new();
    let labels = program
        .globals
        .iter()
        .map(|global| {
            let owner = DeclarationKey::Global(global.name.clone());
            (owner.clone(), collect_label_evidence(owner, &global.value))
        })
        .chain(program.functions.iter().map(|function| {
            let owner = DeclarationKey::Function(function.name.clone());
            let body = function.semantic_body();
            (owner.clone(), collect_label_evidence(owner, &body))
        }))
        .collect::<BTreeMap<_, _>>();
    let mut assignment_reference_requirements = BTreeSet::new();
    // Global source types are inferred symbolically as well. This deliberately
    // accepts only whatever the ordinary expression typer can prove; the existing
    // global resolver remains responsible for user-facing cycle/shape diagnostics.
    for _ in 0..=program.globals.len() {
        let mut progressed = false;
        for global in &program.globals {
            if tables.globals.contains_key(&global.name) {
                continue;
            }
            let key = DeclarationKey::Global(global.name.clone());
            let mut typer = Typer::new(
                key.clone(),
                &tables,
                constructions,
                call_shapes,
                &global.value,
            );
            let body = typer.expression(&global.value, None);
            if let Some(ty) = body.ty.clone() {
                let global_reference_requirements = typer.assignment_reference_requirements.clone();
                let global_refinements = std::mem::take(&mut typer.refinements);
                drop(typer);
                assignment_reference_requirements.extend(global_reference_requirements);
                tables.globals.insert(global.name.clone(), ty);
                bodies.insert(key, body);
                refinements.insert(
                    DeclarationKey::Global(global.name.clone()),
                    global_refinements,
                );
                progressed = true;
            }
        }
        if !progressed {
            break;
        }
    }
    for function in &program.functions {
        let Some(shape) = tables.functions.get(&function.name) else {
            continue;
        };
        let labeled_body = function.semantic_body();
        let fingerprint = incremental
            .as_ref()
            .and_then(|(_, _, fingerprints)| fingerprints.get(&shape.declaration))
            .copied();
        if let Some((cache, _, _)) = incremental.as_mut()
            && let Some(fingerprint) = fingerprint
            && let Some(cached) = cache.bodies.get(&shape.declaration)
            && cached.fingerprint == fingerprint
        {
            assignment_reference_requirements
                .extend(cached.assignment_reference_requirements.iter().cloned());
            refinements.insert(shape.declaration.clone(), cached.refinements.clone());
            bodies.insert(shape.declaration.clone(), cached.body.clone());
            cache.stats.reused_bodies += 1;
            continue;
        }
        let mut typer = Typer::new(
            shape.declaration.clone(),
            &tables,
            constructions,
            call_shapes,
            &labeled_body,
        );
        for (param, ty) in function.params.iter().zip(&shape.params) {
            typer.bind(param.name.clone(), ty.clone());
        }
        let body = typer.expression(&labeled_body, Some(&shape.result));
        let body_refinements = std::mem::take(&mut typer.refinements);
        let body_requirements = typer.assignment_reference_requirements.clone();
        assignment_reference_requirements.extend(body_requirements.iter().cloned());
        refinements.insert(shape.declaration.clone(), body_refinements.clone());
        bodies.insert(shape.declaration.clone(), body.clone());
        if let Some((cache, _, _)) = incremental.as_mut()
            && let Some(fingerprint) = fingerprint
        {
            cache.bodies.insert(
                shape.declaration.clone(),
                CachedTypedBody {
                    fingerprint,
                    body,
                    refinements: body_refinements,
                    assignment_reference_requirements: body_requirements,
                },
            );
            cache.stats.elaborated_bodies += 1;
        }
    }
    TypedProgram {
        bodies,
        labels,
        refinements,
        nominal_variance: infer_nominal_variance(program),
        assignment_reference_requirements,
    }
}

struct Typer<'a> {
    owner: DeclarationKey,
    tables: &'a Tables,
    locals: BTreeMap<String, (LocalKey, ProvisionalType)>,
    next_local: u32,
    constructions: &'a BTreeMap<(DeclarationKey, u32), NominalInstanceKey>,
    call_shapes: &'a BTreeMap<(DeclarationKey, u32), FunctionShape>,
    expression_ordinals: BTreeMap<usize, u32>,
    assignment_reference_requirements: BTreeSet<ProvisionalType>,
    active_labels: BTreeMap<String, Option<ProvisionalType>>,
    refinements: Vec<RefinementEvidence>,
}

impl<'a> Typer<'a> {
    fn pattern_refinement(
        &self,
        pattern: &crate::ast::Pattern,
        ty: Option<&ProvisionalType>,
        projection: &mut Vec<u32>,
        bindings: &mut Vec<RefinementBinding>,
        exclusions: &mut Vec<VariantExclusion>,
    ) -> (bool, bool) {
        let integer = |ty: Option<&ProvisionalType>| {
            matches!(ty, Some(ProvisionalType::Predefined(name)) if matches!(
                name.as_str(),
                "i8" | "i16" | "i32" | "i64" | "i128" | "u8" | "u16" | "u32" | "u64" | "u128"
            ))
        };
        match &pattern.kind {
            PatternKind::Wildcard => (true, true),
            PatternKind::Binding(name) => {
                let Some(ty) = ty else {
                    return (true, false);
                };
                bindings.push(RefinementBinding {
                    name: name.clone(),
                    ty: ty.clone(),
                    projection: projection.clone(),
                    span: pattern.span,
                });
                (true, true)
            }
            PatternKind::Unit => (
                false,
                matches!(ty, Some(ProvisionalType::Predefined(name)) if name == "Unit"),
            ),
            PatternKind::Int(_) => (false, integer(ty)),
            PatternKind::Float(_) => (
                false,
                matches!(ty, Some(ProvisionalType::Predefined(name)) if matches!(name.as_str(), "f32" | "f64")),
            ),
            PatternKind::String(_) => (
                false,
                matches!(ty, Some(ProvisionalType::Predefined(name)) if name == "Text"),
            ),
            PatternKind::Char(_) => (
                false,
                matches!(ty, Some(ProvisionalType::Predefined(name)) if name == "Char"),
            ),
            PatternKind::Byte(_) => (
                false,
                matches!(ty, Some(ProvisionalType::Predefined(name)) if name == "u8"),
            ),
            PatternKind::Tuple { elements, rest } => {
                let Some(ProvisionalType::Tuple(types)) = ty else {
                    return (false, false);
                };
                if elements.len() > types.len() {
                    return (false, false);
                }
                let mut irrefutable = true;
                let mut safe = true;
                for (index, element) in elements.iter().enumerate() {
                    let field = pattern_field_index(*rest, index, elements.len(), types.len());
                    projection.push(field as u32);
                    let (child_irrefutable, child_safe) = self.pattern_refinement(
                        element,
                        types.get(field),
                        projection,
                        bindings,
                        exclusions,
                    );
                    projection.pop();
                    irrefutable &= child_irrefutable;
                    safe &= child_safe;
                }
                (irrefutable, safe)
            }
            PatternKind::Struct { name, fields, .. } => {
                let Some(ProvisionalType::Nominal(key)) = ty else {
                    return (false, false);
                };
                let Some(NominalShape::Struct(types)) = self.tables.nominals.get(key) else {
                    return (false, false);
                };
                if key.declaration.0 != *name {
                    return (false, false);
                }
                let mut irrefutable = true;
                let mut safe = true;
                for field in fields {
                    let Some((index, (_, field_ty))) = types
                        .iter()
                        .enumerate()
                        .find(|(_, (candidate, _))| candidate == &field.field)
                    else {
                        safe = false;
                        continue;
                    };
                    projection.push(index as u32);
                    let (child_irrefutable, child_safe) = self.pattern_refinement(
                        &field.pattern,
                        Some(field_ty),
                        projection,
                        bindings,
                        exclusions,
                    );
                    projection.pop();
                    irrefutable &= child_irrefutable;
                    safe &= child_safe;
                }
                (irrefutable, safe)
            }
            PatternKind::Variant { path, fields, rest } => {
                // A negative refinement can exclude a constructor only when
                // failure of this whole test is equivalent to failure of the
                // outer constructor test. Nested constructors and variants
                // with refutable payload patterns do not satisfy that rule:
                // `!(value is Outer::Some(Inner::Some(_)))`, for example,
                // says nothing unconditional about either constructor.
                let root_variant = projection.is_empty();
                let Some(ProvisionalType::Nominal(key)) = ty else {
                    return (false, false);
                };
                let Some(NominalShape::Enum(variants)) = self.tables.nominals.get(key) else {
                    return (false, false);
                };
                let Some(variant_name) = path.last() else {
                    return (false, false);
                };
                let Some((variant, (_, types))) = variants
                    .iter()
                    .enumerate()
                    .find(|(_, (name, _))| name == variant_name)
                else {
                    return (false, false);
                };
                if fields.len() > types.len() {
                    return (false, false);
                }
                let mut children_irrefutable = true;
                let mut safe = true;
                for (position, pattern) in fields.iter().enumerate() {
                    let field = pattern_field_index(*rest, position, fields.len(), types.len());
                    let field_ty = &types[field];
                    projection.extend([u32::MAX - variant as u32, field as u32]);
                    let (irrefutable, child_safe) = self.pattern_refinement(
                        pattern,
                        Some(field_ty),
                        projection,
                        bindings,
                        exclusions,
                    );
                    projection.pop();
                    projection.pop();
                    children_irrefutable &= irrefutable;
                    safe &= child_safe;
                }
                if root_variant && children_irrefutable {
                    exclusions.push(VariantExclusion {
                        nominal: key.clone(),
                        variant: variant as u32,
                    });
                }
                (variants.len() == 1 && children_irrefutable, safe)
            }
        }
    }

    fn shadow_syntax_type(&self, syntax: &TypeSyntax) -> Option<ProvisionalType> {
        match &syntax.kind {
            TypeSyntaxKind::Never => Some(predefined_named("Never")),
            TypeSyntaxKind::Path(_) => {
                let name = syntax.simple_name()?;
                if matches!(
                    name,
                    "Unit"
                        | "Text"
                        | "Bytes"
                        | "Char"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "usize"
                        | "isize"
                        | "f32"
                        | "f64"
                ) {
                    Some(predefined_named(name))
                } else {
                    Some(ProvisionalType::Nominal(NominalInstanceKey::monomorphic(
                        name,
                    )))
                }
            }
            TypeSyntaxKind::SharedReference { referent, .. } => self
                .shadow_syntax_type(referent)
                .map(ProvisionalType::shared),
            TypeSyntaxKind::UniqueReference { referent, .. } => self
                .shadow_syntax_type(referent)
                .map(ProvisionalType::unique),
            TypeSyntaxKind::Tuple(elements) => elements
                .iter()
                .map(|element| self.shadow_syntax_type(element))
                .collect::<Option<Vec<_>>>()
                .map(ProvisionalType::Tuple),
            TypeSyntaxKind::Application {
                constructor,
                arguments,
                ..
            } => Some(ProvisionalType::Nominal(NominalInstanceKey {
                declaration: NominalKey(constructor.simple_name()?.to_owned()),
                arguments: arguments
                    .iter()
                    .map(|argument| self.shadow_syntax_type(argument))
                    .collect::<Option<Vec<_>>>()?,
            })),
            TypeSyntaxKind::Projection { .. } => None,
        }
    }

    fn recursive_typed_closure_shape(&self, value: &Expr, name: &str) -> Option<ProvisionalType> {
        if !crate::compiler_specialization::recursive_closure_binding(value, name) {
            return None;
        }
        let ExprKind::TypedClosure {
            params,
            return_type,
            ..
        } = &value.kind
        else {
            return None;
        };
        let params = params
            .iter()
            .map(|parameter| self.shadow_syntax_type(&parameter.ty))
            .collect::<Option<Vec<_>>>()?;
        let result = return_type.as_ref().map_or_else(
            || Some(predefined(UNIT)),
            |result| self.shadow_syntax_type(result),
        )?;
        Some(ProvisionalType::Callable(Box::new(CallableShape {
            params,
            result,
            effects: vec![],
            effect_tail: None,
            infer_effects: false,
        })))
    }

    fn assignment_place_type(
        &mut self,
        place: &AssignmentPlace,
    ) -> (Option<ProvisionalType>, Vec<TypedExpr>) {
        let (mut ty, mut children) = match &place.kind {
            AssignmentPlaceKind::Local { name, .. } => (
                self.locals.get(name.as_ref()).map(|(_, ty)| ty.clone()),
                Vec::new(),
            ),
            AssignmentPlaceKind::Dereference { reference, .. } => {
                let reference = self.expression(reference, None);
                let ty = match reference.ty.as_ref() {
                    Some(ProvisionalType::Unique(referent)) => Some((**referent).clone()),
                    _ => None,
                };
                (ty, vec![reference])
            }
        };
        let fields = match &place.kind {
            AssignmentPlaceKind::Local { fields, .. }
            | AssignmentPlaceKind::Dereference { fields, .. } => fields,
        };
        // Field assignment auto-dereferences a named `&mut` owner in Core.
        // Carry the same referent into provisional field selection so scalar
        // RHS operators inherit the field's type instead of defaulting to i64.
        if !fields.is_empty()
            && let Some(ProvisionalType::Unique(referent)) = &ty
        {
            ty = Some((**referent).clone());
        }
        for field in fields {
            ty = match ty.as_ref() {
                Some(ProvisionalType::Tuple(elements)) => field
                    .name
                    .parse::<usize>()
                    .ok()
                    .and_then(|index| elements.get(index).cloned()),
                Some(ProvisionalType::Nominal(key)) => {
                    self.tables.nominals.get(key).and_then(|shape| match shape {
                        NominalShape::Struct(fields) => fields
                            .iter()
                            .find(|(name, _)| name == &field.name)
                            .map(|(_, ty)| ty.clone()),
                        NominalShape::Enum(variants) => {
                            let index = field.name.parse::<usize>().ok()?;
                            let mut candidates =
                                variants.iter().filter_map(|(_, fields)| fields.get(index));
                            let first = candidates.next()?.clone();
                            candidates
                                .all(|candidate| candidate == &first)
                                .then_some(first)
                        }
                    })
                }
                _ => None,
            };
            if let Some(ty) = &ty {
                self.assignment_reference_requirements
                    .insert(ProvisionalType::unique(ty.clone()));
            }
        }
        (ty, std::mem::take(&mut children))
    }

    fn new(
        owner: DeclarationKey,
        tables: &'a Tables,
        constructions: &'a BTreeMap<(DeclarationKey, u32), NominalInstanceKey>,
        call_shapes: &'a BTreeMap<(DeclarationKey, u32), FunctionShape>,
        root: &Expr,
    ) -> Self {
        Self {
            owner,
            tables,
            locals: BTreeMap::new(),
            next_local: 0,
            constructions,
            call_shapes,
            expression_ordinals: crate::compiler_specialization::expression_ordinals(root),
            assignment_reference_requirements: BTreeSet::new(),
            active_labels: BTreeMap::new(),
            refinements: Vec::new(),
        }
    }

    fn planned_construction(&self, source: &Expr) -> Option<NominalInstanceKey> {
        let ordinal = self
            .expression_ordinals
            .get(&(std::ptr::from_ref(source) as usize))?;
        self.constructions
            .get(&(self.owner.clone(), *ordinal))
            .cloned()
    }

    fn planned_call_shape(&self, source: &Expr) -> Option<FunctionShape> {
        let ordinal = self
            .expression_ordinals
            .get(&(std::ptr::from_ref(source) as usize))?;
        self.call_shapes
            .get(&(self.owner.clone(), *ordinal))
            .cloned()
    }

    fn obvious_non_never_context_type(&self, source: &Expr) -> Option<ProvisionalType> {
        self.obvious_context_type(source)
            .filter(|ty| !matches!(ty, ProvisionalType::Predefined(name) if name == "Never"))
    }

    fn obvious_context_type(&self, source: &Expr) -> Option<ProvisionalType> {
        match &source.kind {
            ExprKind::Move(value) => self.obvious_context_type(value),
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                let Stmt::Expr(tail) = statements.last()? else {
                    return None;
                };
                self.obvious_context_type(tail)
            }
            ExprKind::Variable(path) if path.len() == 1 => self
                .locals
                .get(path[0].as_ref())
                .map(|(_, ty)| ty.clone())
                .or_else(|| self.tables.globals.get(path[0].as_ref()).cloned()),
            ExprKind::Call(callee, arguments) => {
                if let Some(nominal) = self.planned_construction(source) {
                    return Some(ProvisionalType::Nominal(nominal));
                }
                if let ExprKind::Variable(path) = &callee.kind
                    && path.len() == 1
                    && path[0].as_ref() == "else"
                    && let [conditional, negative] = arguments.as_slice()
                    && let ExprKind::Call(if_callee, if_arguments) = &conditional.kind
                    && let ExprKind::Variable(if_path) = &if_callee.kind
                    && if_path.len() == 1
                    && if_path[0].as_ref() == "if"
                    && let [_, positive] = if_arguments.as_slice()
                {
                    return self
                        .obvious_non_never_context_type(positive)
                        .or_else(|| self.obvious_non_never_context_type(negative));
                }
                self.planned_call_shape(source)
                    .map(|shape| shape.result)
                    .or_else(|| {
                        let ExprKind::Variable(path) = &callee.kind else {
                            return None;
                        };
                        let [name] = path.as_ref() else {
                            return None;
                        };
                        self.tables
                            .functions
                            .get(name.as_ref())
                            .map(|shape| shape.result.clone())
                    })
            }
            ExprKind::Unit => Some(predefined(UNIT)),
            ExprKind::String(_) => Some(ProvisionalType::Predefined("Text".into())),
            ExprKind::Char(_) => Some(ProvisionalType::Predefined("Char".into())),
            ExprKind::Byte(_) => Some(ProvisionalType::Predefined("u8".into())),
            ExprKind::ByteString(_) => Some(ProvisionalType::Predefined("Bytes".into())),
            ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::List(_)
            | ExprKind::Tuple(_)
            | ExprKind::Struct { .. }
            | ExprKind::Field(_, _)
            | ExprKind::Perform { .. }
            | ExprKind::Handle { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Closure { .. }
            | ExprKind::TypedClosure { .. }
            | ExprKind::LabelDestination { .. }
            | ExprKind::LabelReference(_)
            | ExprKind::Is { .. }
            | ExprKind::Resume { .. }
            | ExprKind::Cancel { .. }
            | ExprKind::TailResume { .. }
            | ExprKind::Variable(_) => None,
        }
    }

    fn bind(&mut self, name: String, ty: ProvisionalType) -> LocalKey {
        let key = LocalKey {
            owner: self.owner.clone(),
            ordinal: self.next_local,
        };
        self.next_local += 1;
        self.locals.insert(name, (key.clone(), ty));
        key
    }

    fn node(&self, source: &Expr, ty: Option<ProvisionalType>, kind: TypedExprKind) -> TypedExpr {
        TypedExpr {
            ty,
            span: source.span,
            kind,
        }
    }

    fn expression(&mut self, source: &Expr, expected: Option<&ProvisionalType>) -> TypedExpr {
        match &source.kind {
            ExprKind::Unit => self.node(source, Some(predefined(UNIT)), TypedExprKind::Leaf),
            ExprKind::Int(_) => self.node(
                source,
                Some(expected.cloned().unwrap_or_else(|| predefined(I64))),
                TypedExprKind::Leaf,
            ),
            ExprKind::String(_) => self.node(source, Some(predefined(TEXT)), TypedExprKind::Leaf),
            ExprKind::Float(_) => self.node(
                source,
                Some(expected.cloned().unwrap_or_else(|| predefined(F64))),
                TypedExprKind::Leaf,
            ),
            ExprKind::Char(_) => self.node(source, Some(predefined(CHAR)), TypedExprKind::Leaf),
            ExprKind::Byte(_) => self.node(source, Some(predefined(U8)), TypedExprKind::Leaf),
            ExprKind::ByteString(_) => {
                self.node(source, Some(predefined(BYTES)), TypedExprKind::Leaf)
            }
            ExprKind::Move(operand) => {
                let moved = self.expression(operand, expected);
                self.node(source, moved.ty, moved.kind)
            }
            ExprKind::Variable(path) if path.len() == 1 => {
                let name = path[0].as_ref();
                if let Some((key, ty)) = self.locals.get(name) {
                    self.node(source, Some(ty.clone()), TypedExprKind::Local(key.clone()))
                } else if let Some(ty) = self.tables.globals.get(name) {
                    self.node(
                        source,
                        Some(ty.clone()),
                        TypedExprKind::Global(DeclarationKey::Global(name.into())),
                    )
                } else {
                    self.node(source, None, TypedExprKind::Unsupported(vec![]))
                }
            }
            ExprKind::Struct { name, fields } => {
                self.construct_struct(source, name, fields, expected)
            }
            ExprKind::Field(subject, field) => {
                let subject = self.expression(subject, None);
                let selection = match subject.ty.as_ref() {
                    Some(ProvisionalType::Tuple(elements)) => {
                        field.parse::<usize>().ok().and_then(|index| {
                            elements.get(index).cloned().map(|ty| (index as u32, ty))
                        })
                    }
                    Some(ProvisionalType::Nominal(key)) => {
                        self.tables.nominals.get(key).and_then(|shape| match shape {
                            NominalShape::Struct(fields) => fields
                                .iter()
                                .enumerate()
                                .find(|(_, (name, _))| name == field)
                                .map(|(index, (_, ty))| (index as u32, ty.clone())),
                            NominalShape::Enum(_) => None,
                        })
                    }
                    _ => None,
                };
                let Some((field, ty)) = selection else {
                    return self.node(source, None, TypedExprKind::Unsupported(vec![subject]));
                };
                self.node(
                    source,
                    Some(ty),
                    TypedExprKind::Project {
                        subject: Box::new(subject),
                        field,
                    },
                )
            }
            ExprKind::Call(callee, args) if let ExprKind::LabelReference(label) = &callee.kind => {
                let destination = self
                    .active_labels
                    .get(label.name.as_ref())
                    .and_then(Clone::clone);
                let children = args
                    .iter()
                    .map(|value| self.expression(value, destination.as_ref()))
                    .collect();
                self.node(source, None, TypedExprKind::EffectBoundary(children))
            }
            ExprKind::Call(callee, args) => self.call(source, callee, args, expected),
            ExprKind::Unary {
                op: UnaryOp::Negate,
                operand,
            } => {
                let ty = expected.cloned().unwrap_or_else(|| predefined(I64));
                let operand = self.expression(operand, Some(&ty));
                self.node(source, Some(ty), TypedExprKind::Primitive(vec![operand]))
            }
            ExprKind::Unary { op, operand }
                if matches!(op, UnaryOp::BorrowShared | UnaryOp::BorrowUnique) =>
            {
                self.borrow(source, operand, *op == UnaryOp::BorrowUnique)
            }
            ExprKind::Unary { operand, .. } => {
                let operand = self.expression(operand, None);
                self.node(source, None, TypedExprKind::Unsupported(vec![operand]))
            }
            ExprKind::Binary {
                lhs,
                rhs,
                op: BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem,
            } => {
                let ty = expected.cloned().unwrap_or_else(|| predefined(I64));
                let lhs = self.expression(lhs, Some(&ty));
                let rhs = self.expression(rhs, Some(&ty));
                self.node(source, Some(ty), TypedExprKind::Primitive(vec![lhs, rhs]))
            }
            ExprKind::Block(statements) => self.block(source, statements, expected),
            ExprKind::Perform {
                effect,
                operation,
                args,
            } => {
                let shape = self
                    .tables
                    .operation_sites
                    .get(&(source.span.start, source.span.end))
                    .or_else(|| {
                        self.tables
                            .operations
                            .get(&(effect.to_string(), operation.to_string()))
                    });
                let children = args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        self.expression(arg, shape.and_then(|shape| shape.params.get(index)))
                    })
                    .collect();
                let ty = shape
                    .map(|shape| shape.result.clone())
                    .or_else(|| expected.cloned());
                self.node(source, ty, TypedExprKind::EffectBoundary(children))
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                let outer_locals = self.locals.clone();
                let outer_next_local = self.next_local;
                let computation = self.expression(computation, expected);
                // The handled computation is emitted as its own synthetic
                // callable. Its lexical locals must not shift identities in
                // the enclosing function after the handler expression.
                self.locals = outer_locals.clone();
                self.next_local = outer_next_local;
                let never = predefined(NEVER);
                let mut handler_result = expected.cloned().or_else(|| {
                    computation
                        .ty
                        .clone()
                        .filter(|candidate| candidate != &never)
                });
                let mut children = vec![computation];
                for clause in clauses.iter() {
                    let saved = outer_locals.clone();
                    let saved_next_local = outer_next_local;
                    self.locals = saved.clone();
                    self.next_local = saved_next_local;
                    if let Some(shape) = self
                        .tables
                        .operation_sites
                        .get(&(clause.span.start, clause.span.end))
                        .or_else(|| {
                            self.tables
                                .operations
                                .get(&(clause.effect.clone(), clause.operation.clone()))
                        })
                        .cloned()
                    {
                        for (pattern, ty) in clause.patterns.iter().zip(&shape.params) {
                            if let PatternKind::Binding(name) = &pattern.kind {
                                self.bind(name.clone(), ty.clone());
                            }
                        }
                        if let (Some(resumption), Some(handler_result)) =
                            (&clause.resumption, &handler_result)
                        {
                            self.bind(
                                resumption.clone(),
                                ProvisionalType::Callable(Box::new(CallableShape {
                                    params: vec![shape.result.clone()],
                                    result: handler_result.clone(),
                                    effects: vec![],
                                    effect_tail: None,
                                    infer_effects: false,
                                })),
                            );
                        }
                    }
                    children.push(self.expression(&clause.body, handler_result.as_ref()));
                    self.locals = saved;
                    // Handler clause parameters and resumptions live in
                    // generated clause callables, not in the enclosing Core
                    // function's local arena. Do not let their shadow-typing
                    // ordinals shift locals declared after the handler.
                    self.next_local = saved_next_local;
                }
                if handler_result.is_none() {
                    let mut inferred = children
                        .iter()
                        .filter_map(|child| child.ty.clone())
                        .filter(|ty| ty != &never);
                    if let Some(first) = inferred.next()
                        && inferred.all(|candidate| candidate == first)
                    {
                        handler_result = Some(first);
                    }
                }
                self.node(
                    source,
                    handler_result,
                    TypedExprKind::EffectBoundary(children),
                )
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                let lhs = self.expression(lhs, None);
                let rhs = self.expression(rhs, None);
                self.node(
                    source,
                    expected.cloned(),
                    TypedExprKind::Unsupported(vec![lhs, rhs]),
                )
            }
            // Closures (inferred and explicitly typed) receive their real
            // shapes during specialization discovery; the shadow typer only
            // walks their bodies for site coverage.
            ExprKind::Closure { body, .. } | ExprKind::TypedClosure { body, .. } => {
                let body = self.expression(body, None);
                self.node(source, None, TypedExprKind::Unsupported(vec![body]))
            }
            ExprKind::List(values) => {
                let values = values
                    .iter()
                    .map(|value| self.expression(value, None))
                    .collect();
                self.node(source, None, TypedExprKind::Unsupported(values))
            }
            ExprKind::Tuple(values) => {
                let expected = expected.and_then(|expected| match expected {
                    ProvisionalType::Tuple(elements) if elements.len() == values.len() => {
                        Some(elements)
                    }
                    _ => None,
                });
                let values = values
                    .iter()
                    .enumerate()
                    .map(|(index, value)| {
                        self.expression(value, expected.and_then(|types| types.get(index)))
                    })
                    .collect::<Vec<_>>();
                let ty = values
                    .iter()
                    .map(|value| value.ty.clone())
                    .collect::<Option<Vec<_>>>()
                    .map(ProvisionalType::Tuple);
                self.node(source, ty, TypedExprKind::Tuple(values))
            }
            ExprKind::Variable(_) => self.node(source, None, TypedExprKind::Unsupported(vec![])),
            ExprKind::LabelDestination { label, ty, body } => {
                let result =
                    provisional_label_type(ty.as_deref()).unwrap_or_else(|| predefined(UNIT));
                let previous = self
                    .active_labels
                    .insert(label.name.to_string(), Some(result.clone()));
                let body = self.expression(body, Some(&result));
                if let Some(previous) = previous {
                    self.active_labels.insert(label.name.to_string(), previous);
                } else {
                    self.active_labels.remove(label.name.as_ref());
                }
                self.node(source, Some(result), TypedExprKind::Unsupported(vec![body]))
            }
            ExprKind::LabelReference(_) => {
                self.node(source, None, TypedExprKind::Unsupported(vec![]))
            }
            ExprKind::Is { subject, pattern } => {
                let subject = self.expression(subject, None);
                let mut positive_bindings = Vec::new();
                let mut negative_exclusions = Vec::new();
                let (irrefutable, projection_safe) = self.pattern_refinement(
                    pattern,
                    subject.ty.as_ref(),
                    &mut Vec::new(),
                    &mut positive_bindings,
                    &mut negative_exclusions,
                );
                let expression_ordinal = self
                    .expression_ordinals
                    .get(&(std::ptr::from_ref(source) as usize))
                    .copied()
                    .unwrap_or(0);
                self.refinements.push(RefinementEvidence {
                    brand: RefinementBrand {
                        owner: self.owner.clone(),
                        expression_ordinal,
                    },
                    span: source.span,
                    subject_type: subject.ty.clone(),
                    positive_bindings,
                    negative_exclusions,
                    irrefutable,
                    projection_safe,
                });
                self.node(
                    source,
                    Some(ProvisionalType::Nominal(NominalInstanceKey {
                        declaration: NominalKey("Result".into()),
                        arguments: vec![predefined_named("Unit"), predefined_named("Unit")],
                    })),
                    TypedExprKind::Unsupported(vec![subject]),
                )
            }
            // Grammar-complete forms rejected by `validate` before typing; if
            // one reaches this shadow typer it is deliberately untyped.
            ExprKind::ContextBlock(statements) => {
                // Context blocks are structurally lowered by their enclosing
                // control-flow primitive, but their source lets still consume
                // identities in Core's function-local arena. Walk the block so
                // later provisional locals retain those same identities.
                let block = self.block(source, statements, expected);
                self.node(
                    source,
                    block.ty.clone(),
                    TypedExprKind::Unsupported(vec![block]),
                )
            }
            ExprKind::Resume { .. } | ExprKind::Cancel { .. } | ExprKind::TailResume { .. } => {
                self.node(source, None, TypedExprKind::Unsupported(vec![]))
            }
        }
    }

    fn borrow(&mut self, source: &Expr, operand: &Expr, unique: bool) -> TypedExpr {
        let (local, path, projection_types, referent, reborrow) = match &operand.kind {
            ExprKind::Variable(path) if path.len() == 1 => self
                .locals
                .get(path[0].as_ref())
                .map(|(key, ty)| (key.clone(), vec![], vec![], ty.clone(), false)),
            ExprKind::Field(subject, field) => {
                let mut names = vec![field.as_str()];
                let mut base = subject.as_ref();
                while let ExprKind::Field(parent, name) = &base.kind {
                    names.push(name.as_str());
                    base = parent.as_ref();
                }
                names.reverse();
                let ExprKind::Variable(base) = &base.kind else {
                    return self.node(source, None, TypedExprKind::Unsupported(vec![]));
                };
                (base.len() == 1)
                    .then(|| self.locals.get(base[0].as_ref()))
                    .flatten()
                    .and_then(|(key, ty)| {
                        let mut ty = ty.clone();
                        ty = match &ty {
                            ProvisionalType::Shared(inner) if !unique => (**inner).clone(),
                            ProvisionalType::Unique(inner) => (**inner).clone(),
                            ProvisionalType::Shared(_) => return None,
                            _ => ty.clone(),
                        };
                        let mut path = Vec::with_capacity(names.len());
                        let mut projection_types = Vec::with_capacity(names.len());
                        for name in names {
                            let (field, next) = match &ty {
                                ProvisionalType::Tuple(elements) => {
                                    let field = name.parse::<usize>().ok()?;
                                    (field as u32, elements.get(field)?.clone())
                                }
                                ProvisionalType::Nominal(nominal)
                                    if nominal.arguments.is_empty() =>
                                {
                                    let NominalShape::Struct(fields) =
                                        self.tables.nominals.get(nominal)?
                                    else {
                                        return None;
                                    };
                                    let (field, (_, ty)) = fields
                                        .iter()
                                        .enumerate()
                                        .find(|(_, (field, _))| field == name)?;
                                    (field as u32, ty.clone())
                                }
                                _ => return None,
                            };
                            path.push(field);
                            ty = next;
                            projection_types.push(if unique {
                                ProvisionalType::unique(ty.clone())
                            } else {
                                ProvisionalType::shared(ty.clone())
                            });
                        }
                        Some((key.clone(), path, projection_types, ty, false))
                    })
            }
            ExprKind::Unary {
                op: UnaryOp::Dereference,
                operand,
            } => match &operand.kind {
                ExprKind::Variable(path) if path.len() == 1 => self
                    .locals
                    .get(path[0].as_ref())
                    .and_then(|(key, ty)| match ty {
                        ProvisionalType::Shared(ty) | ProvisionalType::Unique(ty) => {
                            Some((key.clone(), vec![], vec![], (**ty).clone(), true))
                        }
                        _ => None,
                    }),
                _ => None,
            },
            _ => None,
        }
        .unwrap_or((
            LocalKey {
                owner: self.owner.clone(),
                ordinal: u32::MAX,
            },
            vec![],
            vec![],
            predefined(UNIT),
            false,
        ));
        let ty = if unique {
            ProvisionalType::unique(referent)
        } else {
            ProvisionalType::shared(referent)
        };
        self.node(
            source,
            Some(ty),
            TypedExprKind::Borrow {
                source: local,
                path,
                projection_types,
                reborrow,
                unique,
            },
        )
    }

    fn call(
        &mut self,
        source: &Expr,
        callee: &Expr,
        args: &[Expr],
        expected: Option<&ProvisionalType>,
    ) -> TypedExpr {
        let ExprKind::Variable(path) = &callee.kind else {
            let mut children = vec![self.expression(callee, None)];
            children.extend(args.iter().map(|arg| self.expression(arg, None)));
            return self.node(source, None, TypedExprKind::Unsupported(children));
        };
        if path.len() == 1
            && let Some((_, ProvisionalType::Callable(shape))) =
                self.locals.get(path[0].as_ref()).cloned()
        {
            let mut children = vec![self.expression(callee, None)];
            children.extend(args.iter().enumerate().map(|(index, argument)| {
                self.call_argument_in(argument, shape.params.get(index), args, index)
            }));
            return self.node(
                source,
                Some(shape.result.clone()),
                TypedExprKind::Unsupported(children),
            );
        }
        if path.len() == 1
            && let Some(shape) = self.tables.functions.get(path[0].as_ref()).cloned()
        {
            let args = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    self.call_argument_in(arg, shape.params.get(index), args, index)
                })
                .collect();
            return self.node(
                source,
                Some(shape.result),
                TypedExprKind::Call {
                    declaration: shape.declaration,
                    args,
                },
            );
        }
        if path.len() == 1
            && path[0].as_ref() == "else"
            && let [conditional, negative] = args
            && let ExprKind::Call(if_callee, if_arguments) = &conditional.kind
            && let ExprKind::Variable(if_path) = &if_callee.kind
            && if_path.len() == 1
            && if_path[0].as_ref() == "if"
            && let [condition, positive] = if_arguments.as_slice()
            && matches!(condition.kind, ExprKind::Is { .. })
        {
            // A planned generic control specialization may itself contain a
            // numeric fallback chosen before a sibling branch was known.
            // Prefer either branch's independently synthesized non-default
            // type, then use the enclosing expectation as the fallback.
            let branch_expected = expected.cloned().or_else(|| {
                self.obvious_non_never_context_type(positive)
                    .or_else(|| self.obvious_non_never_context_type(negative))
            });
            let condition = self.expression(condition, None);
            self.next_local += self
                .refinements
                .last()
                .map(|refinement| refinement.positive_bindings.len() as u32)
                .unwrap_or(0);
            let positive = self.expression(positive, branch_expected.as_ref());
            let conditional = self.node(
                conditional,
                None,
                TypedExprKind::Unsupported(vec![condition, positive]),
            );
            let negative = self.expression(negative, branch_expected.as_ref());
            return self.node(
                source,
                branch_expected,
                TypedExprKind::Unsupported(vec![conditional, negative]),
            );
        }
        if let Some(shape) = self.planned_call_shape(source) {
            let mut children = vec![self.expression(callee, None)];
            children.extend(args.iter().enumerate().map(|(index, argument)| {
                self.call_argument_in(argument, shape.params.get(index), args, index)
            }));
            return self.node(
                source,
                Some(shape.result),
                TypedExprKind::Unsupported(children),
            );
        }
        if path.len() == 2 {
            let key = expected
                .and_then(|ty| match ty {
                    ProvisionalType::Nominal(key) if key.declaration.0 == path[0].as_ref() => {
                        Some(key.clone())
                    }
                    _ => None,
                })
                .or_else(|| self.planned_construction(source))
                .unwrap_or_else(|| NominalInstanceKey::monomorphic(path[0].to_string()));
            if let Some(NominalShape::Enum(variants)) = self.tables.nominals.get(&key) {
                let selected = variants
                    .iter()
                    .enumerate()
                    .find(|(_, (name, _))| name == path[1].as_ref())
                    .map(|(index, (_, fields))| (index as u32, fields.clone()));
                if let Some((variant, types)) = selected {
                    let fields = args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| (index as u32, self.expression(arg, types.get(index))))
                        .collect();
                    return self.node(
                        source,
                        Some(ProvisionalType::Nominal(key.clone())),
                        TypedExprKind::Construct {
                            nominal: key,
                            variant: Some(variant),
                            fields,
                        },
                    );
                }
            }
        }
        // A structural `if(subject is Pattern, positive)` is consumed by its
        // enclosing `else` and lowered as one refinement branch. Keep the
        // ordinary allocation-independent typing behavior for both arguments,
        // but reserve Core's successful-edge decision binders before walking
        // the positive context block. Their names remain branch-local and are
        // deliberately not installed in this shadow environment.
        if path.len() == 1
            && path[0].as_ref() == "if"
            && let [condition, positive] = args
            && matches!(condition.kind, ExprKind::Is { .. })
        {
            let condition = self.expression(condition, None);
            self.next_local += self
                .refinements
                .last()
                .map(|refinement| refinement.positive_bindings.len() as u32)
                .unwrap_or(0);
            let positive = self.expression(positive, None);
            return self.node(
                source,
                None,
                TypedExprKind::Unsupported(vec![condition, positive]),
            );
        }
        let children = args.iter().map(|arg| self.expression(arg, None)).collect();
        self.node(source, None, TypedExprKind::Unsupported(children))
    }

    fn call_argument(&mut self, source: &Expr, expected: Option<&ProvisionalType>) -> TypedExpr {
        if let (Some(expected), ExprKind::Variable(path)) = (expected, &source.kind)
            && path.len() == 1
            && let Some((local, actual)) = self.locals.get(path[0].as_ref()).cloned()
        {
            let unique = matches!(expected, ProvisionalType::Unique(_));
            let compatible = match (expected, &actual) {
                (ProvisionalType::Unique(expected), ProvisionalType::Unique(actual))
                | (ProvisionalType::Shared(expected), ProvisionalType::Shared(actual))
                | (ProvisionalType::Shared(expected), ProvisionalType::Unique(actual)) => {
                    expected == actual
                }
                _ => false,
            };
            if compatible {
                return self.node(
                    source,
                    Some(expected.clone()),
                    TypedExprKind::Borrow {
                        source: local,
                        path: vec![],
                        projection_types: vec![],
                        reborrow: true,
                        unique,
                    },
                );
            }
        }
        self.expression(source, expected)
    }

    fn call_argument_in(
        &mut self,
        source: &Expr,
        expected: Option<&ProvisionalType>,
        arguments: &[Expr],
        index: usize,
    ) -> TypedExpr {
        let overlapping = match (&source.kind, expected) {
            (ExprKind::Variable(path), Some(ProvisionalType::Unique(_))) if path.len() == 1 => {
                arguments.iter().enumerate().any(|(other, argument)| {
                    other != index
                        && matches!(
                            crate::ast::visit_expr_preorder(argument, |expression| {
                                if matches!(&expression.kind, ExprKind::Variable(candidate)
                                    if candidate.len() == 1 && candidate[0] == path[0])
                                {
                                    ControlFlow::Break(())
                                } else {
                                    ControlFlow::Continue(())
                                }
                            }),
                            ControlFlow::Break(())
                        )
                })
            }
            _ => false,
        };
        if overlapping {
            self.expression(source, expected)
        } else {
            self.call_argument(source, expected)
        }
    }

    fn construct_struct(
        &mut self,
        source: &Expr,
        name: &str,
        supplied: &[(String, Expr)],
        expected: Option<&ProvisionalType>,
    ) -> TypedExpr {
        let key = self
            .planned_construction(source)
            .or_else(|| {
                expected.and_then(|ty| match ty {
                    ProvisionalType::Nominal(key) if key.declaration.0 == name => Some(key.clone()),
                    _ => None,
                })
            })
            .unwrap_or_else(|| NominalInstanceKey::monomorphic(name));
        let declared = match self.tables.nominals.get(&key) {
            Some(NominalShape::Struct(fields)) => fields.clone(),
            _ => vec![],
        };
        let fields = declared
            .iter()
            .enumerate()
            .filter_map(|(index, (name, ty))| {
                supplied
                    .iter()
                    .find(|(supplied, _)| supplied == name)
                    .map(|(_, value)| (index as u32, self.expression(value, Some(ty))))
            })
            .collect();
        self.node(
            source,
            Some(ProvisionalType::Nominal(key.clone())),
            TypedExprKind::Construct {
                nominal: key,
                variant: None,
                fields,
            },
        )
    }

    fn later_binding_type(&self, binding: &str, remaining: &[Stmt]) -> Option<ProvisionalType> {
        fn binding_name(expression: &Expr) -> Option<&str> {
            let expression = match &expression.kind {
                ExprKind::Move(value) => value.as_ref(),
                _ => expression,
            };
            let ExprKind::Variable(path) = &expression.kind else {
                return None;
            };
            (path.len() == 1).then_some(path[0].as_ref())
        }

        fn pattern_binds(pattern: &crate::ast::Pattern, binding: &str) -> bool {
            match &pattern.kind {
                PatternKind::Binding(name) => name == binding,
                PatternKind::Variant { fields, .. } => {
                    fields.iter().any(|field| pattern_binds(field, binding))
                }
                PatternKind::Tuple { elements, .. } => elements
                    .iter()
                    .any(|element| pattern_binds(element, binding)),
                PatternKind::Struct { fields, .. } => fields
                    .iter()
                    .any(|field| pattern_binds(&field.pattern, binding)),
                PatternKind::Wildcard
                | PatternKind::Unit
                | PatternKind::Int(_)
                | PatternKind::Float(_)
                | PatternKind::String(_)
                | PatternKind::Char(_)
                | PatternKind::Byte(_) => false,
            }
        }

        fn statements_binding_type(
            typer: &Typer<'_>,
            statements: &[Stmt],
            binding: &str,
        ) -> Option<ProvisionalType> {
            for statement in statements {
                let (value, shadows_after_value) = match statement {
                    Stmt::Let { name, value, .. } => (value, name == binding),
                    Stmt::Deconstruct { fields, value, .. } => (
                        value,
                        fields
                            .iter()
                            .any(|field| field.binding.as_deref() == Some(binding)),
                    ),
                    Stmt::Expr(value) | Stmt::Assign { value, .. } => (value, false),
                };
                if let Some(ty) = expression_binding_type(typer, value, binding) {
                    return Some(ty);
                }
                if shadows_after_value {
                    return None;
                }
            }
            None
        }

        fn expression_binding_type(
            typer: &Typer<'_>,
            expression: &Expr,
            binding: &str,
        ) -> Option<ProvisionalType> {
            match &expression.kind {
                ExprKind::Call(callee, arguments) => {
                    if let ExprKind::Variable(path) = &callee.kind
                        && path.len() == 1
                        && let Some(shape) = typer.tables.functions.get(path[0].as_ref())
                    {
                        for (argument, formal) in arguments.iter().zip(&shape.params) {
                            let (candidate, expected) = match (&argument.kind, formal) {
                                (
                                    ExprKind::Unary {
                                        op: UnaryOp::BorrowUnique,
                                        operand,
                                    },
                                    ProvisionalType::Unique(referent),
                                )
                                | (
                                    ExprKind::Unary {
                                        op: UnaryOp::BorrowShared,
                                        operand,
                                    },
                                    ProvisionalType::Shared(referent),
                                ) => (operand.as_ref(), referent.as_ref()),
                                _ => (argument, formal),
                            };
                            if binding_name(candidate) == Some(binding) {
                                return Some(expected.clone());
                            }
                        }
                    }
                    expression_binding_type(typer, callee, binding).or_else(|| {
                        arguments
                            .iter()
                            .find_map(|argument| expression_binding_type(typer, argument, binding))
                    })
                }
                ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                    statements_binding_type(typer, statements, binding)
                }
                ExprKind::Handle {
                    computation,
                    clauses,
                } => expression_binding_type(typer, computation, binding).or_else(|| {
                    clauses.iter().find_map(|clause| {
                        let shadows = clause.resumption.as_deref() == Some(binding)
                            || clause
                                .patterns
                                .iter()
                                .any(|pattern| pattern_binds(pattern, binding));
                        (!shadows)
                            .then(|| expression_binding_type(typer, &clause.body, binding))
                            .flatten()
                    })
                }),
                ExprKind::List(values) | ExprKind::Tuple(values) => values
                    .iter()
                    .find_map(|value| expression_binding_type(typer, value, binding)),
                ExprKind::Struct { fields, .. } => fields
                    .iter()
                    .find_map(|(_, value)| expression_binding_type(typer, value, binding)),
                ExprKind::Field(subject, _)
                | ExprKind::Move(subject)
                | ExprKind::Unary {
                    operand: subject, ..
                } => expression_binding_type(typer, subject, binding),
                ExprKind::Binary { lhs, rhs, .. } => expression_binding_type(typer, lhs, binding)
                    .or_else(|| expression_binding_type(typer, rhs, binding)),
                ExprKind::Perform { args, .. } => args
                    .iter()
                    .find_map(|argument| expression_binding_type(typer, argument, binding)),
                ExprKind::LabelDestination { body, .. } => {
                    expression_binding_type(typer, body, binding)
                }
                ExprKind::Is { subject, .. } => expression_binding_type(typer, subject, binding),
                ExprKind::Resume { resumption, value }
                | ExprKind::TailResume { resumption, value } => {
                    expression_binding_type(typer, resumption, binding).or_else(|| {
                        value
                            .as_deref()
                            .and_then(|value| expression_binding_type(typer, value, binding))
                    })
                }
                ExprKind::Cancel { resumption } => {
                    expression_binding_type(typer, resumption, binding)
                }
                ExprKind::Closure { params, body } => {
                    (!params.iter().any(|parameter| parameter.as_ref() == binding))
                        .then(|| expression_binding_type(typer, body, binding))
                        .flatten()
                }
                ExprKind::TypedClosure { params, body, .. } => {
                    (!params.iter().any(|parameter| parameter.name == binding))
                        .then(|| expression_binding_type(typer, body, binding))
                        .flatten()
                }
                ExprKind::Unit
                | ExprKind::Int(_)
                | ExprKind::Float(_)
                | ExprKind::Char(_)
                | ExprKind::Byte(_)
                | ExprKind::ByteString(_)
                | ExprKind::String(_)
                | ExprKind::Variable(_)
                | ExprKind::LabelReference(_) => None,
            }
        }

        statements_binding_type(self, remaining, binding)
    }

    fn block(
        &mut self,
        source: &Expr,
        statements: &[Stmt],
        expected: Option<&ProvisionalType>,
    ) -> TypedExpr {
        let saved = self.locals.clone();
        let mut values = Vec::new();
        let mut tail = self.node(source, Some(predefined(UNIT)), TypedExprKind::Leaf);
        for (index, statement) in statements.iter().enumerate() {
            let last = index + 1 == statements.len();
            match statement {
                Stmt::Let { name, value, .. } => {
                    let recursive_shape = self.recursive_typed_closure_shape(value, name);
                    if let Some(shape) = &recursive_shape {
                        self.bind(name.clone(), shape.clone());
                    }
                    let inferred = self.later_binding_type(name, &statements[index + 1..]);
                    let value = self.expression(value, inferred.as_ref());
                    if let Some(ty) = value.ty.clone() {
                        self.bind(name.clone(), ty);
                    } else if let Some(ty) = inferred {
                        self.bind(name.clone(), ty);
                    } else if recursive_shape.is_some() {
                        // Keep the prebound self identity as the final local;
                        // specialization owns the exact closure request.
                    } else {
                        // Core assigns an identity to every source `let`, even
                        // when this allocation-independent shadow typer leaves
                        // the initializer deliberately unsupported (notably a
                        // generic specialization call). Preserve that ordinal
                        // so later typed locals still agree with Core.
                        self.next_local += 1;
                    }
                    values.push(value);
                }
                Stmt::Deconstruct {
                    ty, fields, value, ..
                } => {
                    let value = self.expression(value, None);
                    if let Some(ty) = ty {
                        let key = NominalInstanceKey::monomorphic(ty);
                        if value.ty.as_ref() == Some(&ProvisionalType::Nominal(key.clone()))
                            && let Some(NominalShape::Struct(declared)) =
                                self.tables.nominals.get(&key)
                        {
                            for field in fields {
                                if let (Some(binding), Some((_, field_ty))) = (
                                    &field.binding,
                                    declared.iter().find(|(name, _)| name == &field.field),
                                ) {
                                    self.bind(binding.clone(), field_ty.clone());
                                }
                            }
                        }
                    } else if let Some(ProvisionalType::Tuple(elements)) = &value.ty {
                        for field in fields {
                            let offset = field.field.parse::<usize>().ok();
                            let index = offset.and_then(|offset| {
                                if field.from_end {
                                    elements.len().checked_sub(offset)
                                } else {
                                    Some(offset)
                                }
                            });
                            if let (Some(binding), Some(field_ty)) =
                                (&field.binding, index.and_then(|index| elements.get(index)))
                            {
                                self.bind(binding.clone(), field_ty.clone());
                            }
                        }
                    }
                    values.push(value);
                }
                Stmt::Assign {
                    destination,
                    value,
                    span,
                } => {
                    let (destination_ty, destination_children) =
                        self.assignment_place_type(destination);
                    // Typed evidence records the language-level evaluation
                    // order, even though resolving the static destination type
                    // above has no runtime behavior.
                    let mut children = vec![self.expression(value, destination_ty.as_ref())];
                    children.extend(destination_children);
                    values.push(TypedExpr {
                        ty: Some(predefined(UNIT)),
                        span: *span,
                        kind: TypedExprKind::EffectBoundary(children),
                    });
                    if last {
                        tail = TypedExpr {
                            ty: Some(predefined(UNIT)),
                            span: *span,
                            kind: TypedExprKind::Leaf,
                        };
                    }
                }
                Stmt::Expr(value) if last => tail = self.expression(value, expected),
                Stmt::Expr(value) => values.push(self.expression(value, None)),
            }
        }
        self.locals = saved;
        let ty = tail.ty.clone();
        self.node(
            source,
            ty,
            TypedExprKind::Block {
                values,
                tail: Box::new(tail),
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn provisional_folder_rebuilds_every_type_bearing_edge() {
        struct Rename;
        impl ProvisionalTypeFolder for Rename {
            type Error = std::convert::Infallible;

            fn fold_type(&mut self, ty: &ProvisionalType) -> Result<ProvisionalType, Self::Error> {
                if matches!(ty, ProvisionalType::Predefined(name) if name == "Old") {
                    Ok(predefined_named("New"))
                } else {
                    fold_provisional_type_children(self, ty)
                }
            }
        }

        let old = predefined_named("Old");
        let ty = ProvisionalType::Callable(Box::new(CallableShape {
            params: vec![ProvisionalType::Tuple(vec![old.clone()])],
            result: ProvisionalType::shared(old.clone()),
            effects: vec![CallableEffect {
                declaration: ProtocolKey("Effect".into()),
                arguments: vec![ProvisionalType::Nominal(NominalInstanceKey {
                    declaration: NominalKey("Box".into()),
                    arguments: vec![old],
                })],
            }],
            effect_tail: None,
            infer_effects: false,
        }));
        let folded = Rename.fold_type(&ty).unwrap();

        assert!(!provisional_type_any(&folded, &mut |ty| {
            matches!(ty, ProvisionalType::Predefined(name) if name == "Old")
        }));
    }

    #[test]
    fn signature_queries_deliberately_exclude_callable_effect_arguments() {
        let ty = ProvisionalType::Callable(Box::new(CallableShape {
            params: vec![],
            result: predefined_named("Unit"),
            effects: vec![CallableEffect {
                declaration: ProtocolKey("Effect".into()),
                arguments: vec![ProvisionalType::unique(predefined_named("i64"))],
            }],
            effect_tail: None,
            infer_effects: false,
        }));
        let unique = &mut |ty: &ProvisionalType| matches!(ty, ProvisionalType::Unique(_));

        assert!(provisional_type_any(&ty, unique));
        assert!(!provisional_signature_type_any(&ty, unique));
    }

    #[test]
    fn reserved_types_have_canonical_distinct_spellings() {
        let types = [
            ProvisionalType::Param(GenericParamKey {
                owner: DeclarationKey::Function("f".into()),
                ordinal: 0,
            }),
            ProvisionalType::Callable(Box::new(CallableShape {
                params: vec![predefined_named("i64")],
                result: predefined_named("Unit"),
                effects: vec![],
                effect_tail: None,
                infer_effects: false,
            })),
        ];
        let mut text = String::new();
        types.iter().for_each(|ty| ty.write(&mut text));
        assert_eq!(
            text,
            "param:GenericParamKey { owner: Function(\"f\"), ordinal: 0 }callable:(i64)->Unit/{}"
        );
    }

    #[test]
    fn nominal_variance_reaches_a_recursive_declaration_order_independent_fixed_point() {
        let parse = |source| crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let first = parse(
            "struct Leaf<T>{value:T} struct Shared<'a,T>{value:&'a T} struct Unique<'a,T>{value:&'a mut T} struct Phantom<T>{marker:i64} struct Recursive<'a,T>{next:&'a Recursive<'a,T>,leaf:Leaf<T>} struct Outer<T>{inner:Unique<'static,T>} main()->{()}",
        );
        let reordered = parse(
            "main()->{()} struct Outer<X>{inner:Unique<'static,X>} struct Recursive<'r,X>{leaf:Leaf<X>,next:&'r Recursive<'r,X>} struct Phantom<X>{marker:i64} struct Unique<'r,X>{value:&'r mut X} struct Shared<'r,X>{value:&'r X} struct Leaf<X>{value:X}",
        );
        let expected = BTreeMap::from([
            ("Leaf".into(), vec![Variance::Covariant]),
            ("Outer".into(), vec![Variance::Invariant]),
            ("Phantom".into(), vec![Variance::Bivariant]),
            (
                "Recursive".into(),
                vec![Variance::Covariant, Variance::Covariant],
            ),
            (
                "Shared".into(),
                vec![Variance::Covariant, Variance::Covariant],
            ),
            (
                "Unique".into(),
                vec![Variance::Invariant, Variance::Invariant],
            ),
        ]);
        assert_eq!(infer_nominal_variance(&first), expected);
        assert_eq!(infer_nominal_variance(&reordered), expected);
    }

    #[test]
    fn shadow_typing_prebinds_recursive_typed_closure_self_as_a_callable_local() {
        let program = crate::parser::parse(
            crate::lexer::lex(
                "answer() -> i64 {
                     let recurse = (value: i64) -> i64 { recurse(value) };
                     42
                 }",
            )
            .unwrap(),
        )
        .unwrap();
        let owner = DeclarationKey::Function("answer".into());
        let tables = Tables {
            functions: BTreeMap::from([(
                "answer".into(),
                FunctionShape {
                    declaration: owner.clone(),
                    params: vec![],
                    result: predefined(I64),
                },
            )]),
            ..Tables::default()
        };
        let typed = type_program(&program, &tables, &BTreeMap::new(), &BTreeMap::new());
        let body = &typed.bodies[&owner];

        fn contains_self_local(expression: &TypedExpr, owner: &DeclarationKey) -> bool {
            match &expression.kind {
                TypedExprKind::Local(key) => key.owner == *owner && key.ordinal == 0,
                TypedExprKind::Call { args, .. }
                | TypedExprKind::Primitive(args)
                | TypedExprKind::EffectBoundary(args)
                | TypedExprKind::Unsupported(args) => {
                    args.iter().any(|child| contains_self_local(child, owner))
                }
                TypedExprKind::Construct { fields, .. } => fields
                    .iter()
                    .any(|(_, child)| contains_self_local(child, owner)),
                TypedExprKind::Tuple(values) => {
                    values.iter().any(|child| contains_self_local(child, owner))
                }
                TypedExprKind::Project { subject, .. } => contains_self_local(subject, owner),
                TypedExprKind::Block { values, tail } => {
                    values.iter().any(|child| contains_self_local(child, owner))
                        || contains_self_local(tail, owner)
                }
                TypedExprKind::Borrow { .. } | TypedExprKind::Leaf | TypedExprKind::Global(_) => {
                    false
                }
            }
        }

        assert!(contains_self_local(body, &owner), "{body:#?}");
    }

    #[test]
    fn label_evidence_uses_stable_generative_brands_and_reference_result_contracts() {
        let program = crate::parser::parse(
            crate::lexer::lex(
                "select<'a>(value:&'a i64)->&'a i64{@done:&'a i64{@scope:{@scope;@done(value)}}} main()->{()}",
            )
            .unwrap(),
        )
        .unwrap();
        let owner = DeclarationKey::Function("select".into());
        let labels = collect_label_evidence(owner.clone(), &program.functions[0].body);
        assert_eq!(labels.len(), 2);
        assert_eq!(
            labels[0].brand,
            LabelBrand {
                owner: owner.clone(),
                ordinal: 0
            }
        );
        assert_eq!(labels[1].brand, LabelBrand { owner, ordinal: 1 });
        assert_eq!(labels[0].name, "done");
        assert!(labels[0].result_contains_references);
        assert_eq!(labels[0].leaves.len(), 1);
        assert!(labels[0].leaves[0].result_contains_references);
        assert_eq!(labels[1].name, "scope");
        assert_eq!(labels[1].references.len(), 1);
        assert_eq!(
            labels[1].destination_result,
            Some(ProvisionalType::Predefined("Unit".into()))
        );
    }

    #[test]
    fn refinement_evidence_keeps_binder_paths_but_only_sound_negative_exclusions() {
        let program = crate::parser::parse(
            crate::lexer::lex(
                "enum Inner { Some(i64), None }
                 enum Outer { Some(Inner), None }
                 nested(value: Outer) -> Bool {
                     value is Outer::Some(Inner::Some(found))
                 }
                 shallow(value: Outer) -> Bool {
                     value is Outer::Some(_)
                 }",
            )
            .unwrap(),
        )
        .unwrap();
        let inner = NominalInstanceKey::monomorphic("Inner");
        let outer = NominalInstanceKey::monomorphic("Outer");
        let tables = Tables {
            functions: BTreeMap::from([
                (
                    "nested".into(),
                    FunctionShape {
                        declaration: DeclarationKey::Function("nested".into()),
                        params: vec![ProvisionalType::Nominal(outer.clone())],
                        result: ProvisionalType::Nominal(NominalInstanceKey::monomorphic("Bool")),
                    },
                ),
                (
                    "shallow".into(),
                    FunctionShape {
                        declaration: DeclarationKey::Function("shallow".into()),
                        params: vec![ProvisionalType::Nominal(outer.clone())],
                        result: ProvisionalType::Nominal(NominalInstanceKey::monomorphic("Bool")),
                    },
                ),
            ]),
            nominals: BTreeMap::from([
                (
                    inner.clone(),
                    NominalShape::Enum(vec![
                        ("Some".into(), vec![predefined(I64)]),
                        ("None".into(), vec![]),
                    ]),
                ),
                (
                    outer.clone(),
                    NominalShape::Enum(vec![
                        ("Some".into(), vec![ProvisionalType::Nominal(inner)]),
                        ("None".into(), vec![]),
                    ]),
                ),
            ]),
            ..Tables::default()
        };
        let typed = type_program(&program, &tables, &BTreeMap::new(), &BTreeMap::new());

        let nested = &typed.refinements[&DeclarationKey::Function("nested".into())][0];
        assert_eq!(nested.positive_bindings.len(), 1);
        assert_eq!(nested.positive_bindings[0].name, "found");
        assert_eq!(
            nested.positive_bindings[0].projection,
            vec![u32::MAX, 0, u32::MAX, 0]
        );
        assert!(nested.negative_exclusions.is_empty());

        let shallow = &typed.refinements[&DeclarationKey::Function("shallow".into())][0];
        assert_eq!(
            shallow.negative_exclusions,
            vec![VariantExclusion {
                nominal: outer,
                variant: 0,
            }]
        );
    }

    #[test]
    fn provisional_const_identity_round_trips_only_at_text_boundaries() {
        for identity in [
            ProvisionalConst::U32(42),
            ProvisionalConst::Quantity {
                lower: 2,
                upper: Some(7),
            },
            ProvisionalConst::Quantity {
                lower: 3,
                upper: None,
            },
            ProvisionalConst::Rigid {
                index: 9,
                kind: ConstKind::Quantity,
            },
        ] {
            assert_eq!(
                ProvisionalConst::decode_encoded_name(&identity.encoded_name()),
                Some(identity)
            );
        }
        assert_eq!(ProvisionalConst::decode_encoded_name("i64"), None);
    }
}
