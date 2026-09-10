//! Generic ownership elaboration over ordered CFG, before concrete instances.
//! Every produced value has an inventory entry, including unnamed temporary
//! owners. Suspensions carry the live residual inventory, not just bindings.
use crate::control_mir::*;
use crate::{
    CoreId, DefKey, ElaboratedInterface, GenericArgument, PlaceFlow, Quantity, Safety, Type,
};
use std::collections::{BTreeMap, BTreeSet};

mod emission;
mod graph;
mod inventory;
// Experimental direct-local path checker. Its join/view model is not yet
// sufficient for production; imported PlaceFlow remains authoritative here.
#[cfg(test)]
mod paths;
mod validate;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct OwnerId(pub u32);
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LoanId(pub u32);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OwnerKind {
    Parameter,
    Binding,
    Temporary,
    Join,
    SharedLoan,
    UniqueLoan,
    Callable,
    Continuation,
    Capture(crate::CaptureMode),
    View,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Owner {
    pub value: ControlValue,
    pub kind: OwnerKind,
    pub scope: Option<ControlScopeId>,
    pub quantity: Option<Quantity>,
    /// Projection of the sealed quantity product, not a Copy permission.
    pub(crate) retains_resumption: bool,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Loan {
    pub id: LoanId,
    pub destination: ControlValue,
    pub place: ControlPlace,
    pub unique: bool,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueTransfer {
    Copy,
    Move,
    Reborrow,
    /// Retain only a checked replay capability's carrier. Its continuation
    /// and invocation budget stay with the same dynamic owner.
    RetainResumption,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OwnershipOperand {
    pub value: ControlValue,
    pub mode: ValueTransfer,
}

/// Permission to duplicate/discard an environment is structural ownership
/// evidence, not the number of invocations permitted for each callable copy.
fn environment_quantity(
    captures: &[(ControlValue, crate::CaptureMode)],
    owners: &[Owner],
) -> Option<Quantity> {
    captures.iter().try_fold(Quantity::UNRESTRICTED, |quantity, (value, mode)| {
        let capture = match mode {
            crate::CaptureMode::SharedBorrow => Quantity::UNRESTRICTED,
            crate::CaptureMode::UniqueBorrow => Quantity::AFFINE,
            crate::CaptureMode::Copy | crate::CaptureMode::Move => owners.get(value.0 as usize)?.quantity?,
        };
        quantity.intersection(capture).ok()
    })
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OwnershipAggregate {
    Tuple,
    Array,
    Record(DefKey),
    Enum { definition: DefKey, variant: u32 },
}

/// The leaf computations are deliberately separated from owner operations.
/// Construction is private; an ownership operation cannot be hidden here.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OwnershipComputation {
    Literal(String),
    ConstValue(GenericArgument),
    Unit,
    Function {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
    },
    Intrinsic {
        operator: String,
        arguments: Vec<ControlValue>,
    },
    HostFunction {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
        import: crate::signature::HostImport,
    },
    TraitMethod {
        evidence: DefKey,
        method: DefKey,
        trait_arguments: Vec<GenericArgument>,
        method_arguments: Vec<GenericArgument>,
        deferred: Option<crate::core::DeferredTraitMethod>,
    },
    Constant {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
    },
    Test {
        subject: ControlValue,
        pattern: crate::core::CorePattern,
    },
    Label(ControlLabelId),
    Resumption {
        handler: ControlHandlerId,
        clause: u32,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OwnershipOperation {
    Compute(OwnershipComputation),
    Construct {
        aggregate: OwnershipAggregate,
        fields: Vec<OwnershipOperand>,
    },
    Transfer {
        value: ControlValue,
        mode: ValueTransfer,
    },
    Read(ControlValue),
    ReadReference(ControlValue),
    ReadPlace {
        place: ControlPlace,
        mode: ValueTransfer,
    },
    Project {
        place: ControlPlace,
        base: ControlValue,
        index: u32,
        field_count: u32,
        mode: ValueTransfer,
    },
    Borrow(LoanId),
    MovePlace(ControlPlace),
    Replace {
        place: ControlPlace,
        value: ControlValue,
        mode: ValueTransfer,
    },
    Discard(OwnerId),
    ExitScope {
        scope: ControlScopeId,
        result: ControlValue,
        mode: ValueTransfer,
        owners: Vec<OwnerId>,
    },
    Capture {
        closure: ControlClosureId,
        captures: Vec<(ControlValue, crate::CaptureMode)>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OwnershipInstruction {
    pub scope: ControlScopeId,
    pub destination: ControlValue,
    pub operation: OwnershipOperation,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OwnerDisposition {
    Transfer,
    Retain,
    Suspend,
    Abandon,
    ReturnCapture,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OwnershipTerminator {
    pub control: ControlTerminator,
    pub operands: Vec<OwnershipOperand>,
    pub dispositions: Vec<(OwnerId, OwnerDisposition)>,
    pub successors: Vec<OwnershipSuccessor>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OwnershipSuccessor {
    pub target: ControlBlockId,
    pub arguments: Vec<OwnershipOperand>,
    /// May-initialized owners after this selected edge has transferred its
    /// arguments and established the destination block parameters.
    pub inventory: Vec<OwnerId>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OwnershipBlock {
    pub parameters: Vec<ControlValue>,
    pub instructions: Vec<OwnershipInstruction>,
    pub terminator: OwnershipTerminator,
}
#[derive(Clone, Debug)]
pub struct OwnershipMir {
    pub(crate) definition: DefKey,
    pub(crate) safety: Safety,
    pub(crate) unsafe_execution: bool,
    pub(crate) parameters: Vec<ControlValue>,
    pub(crate) values: Vec<ControlValueDecl>,
    pub(crate) scopes: Vec<ControlScope>,
    pub(crate) entry: ControlBlockId,
    pub(crate) labels: Vec<ControlLabel>,
    pub(crate) handlers: Vec<ControlHandler>,
    pub(crate) closures: Vec<OwnershipClosure>,
    pub(crate) source_bindings: BTreeMap<crate::placeflow::PlaceBindingOrigin, ControlValue>,
    pub(crate) source_flow: PlaceFlow,
    pub(crate) owners: Vec<Owner>,
    pub(crate) loans: Vec<Loan>,
    pub(crate) blocks: Vec<OwnershipBlock>,
    pub(crate) live_in: Vec<BTreeSet<ControlValue>>,
    pub(crate) aliases: BTreeMap<ControlValue, ControlValue>,
}
#[derive(Clone, Debug)]
pub struct OwnershipClosure {
    pub environment: crate::core::CaptureEnvironment,
    pub body: Box<OwnershipMir>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OwnershipError(pub String);

impl OwnershipMir {
    /// A lifted body returns its checked value refinement, which may retain
    /// captures and residual predicates absent from a written callable ABI.
    /// Keep the declared result for a bottom body or inconsistent exits; the
    /// latter must still fail the ordinary exact MIR return validation.
    pub(crate) fn refined_result_type<'a>(&'a self, declared: &'a Type) -> &'a Type {
        let mut results = self.blocks.iter().filter_map(|block| match block.terminator.control {
            ControlTerminator::Return(value) => self.values.get(value.0 as usize).map(|value| &value.ty),
            _ => None,
        });
        let Some(result) = results.next() else { return declared; };
        if results.all(|other| other == result) { result } else { declared }
    }

    /// Common executable frontend boundary. It never selects concrete
    /// instances or emits runtime instructions.
    pub fn from_typed(definition: DefKey, body: &crate::TypedBody, flow: &PlaceFlow,
        signatures: Option<&ElaboratedInterface>) -> Result<(Self, Type), OwnershipError> {
        let solver = signatures.map(crate::TraitSolver::new);
        Self::from_typed_with_frozen_solver(definition, body, flow, signatures, solver.as_ref())
    }

    /// The supplied snapshot belongs to the same immutable interface. Never
    /// share mutable query tables or consume the producer's work budget.
    pub(crate) fn from_typed_with_frozen_solver(
        definition: DefKey, body: &crate::TypedBody, flow: &PlaceFlow,
        signatures: Option<&ElaboratedInterface>, solver: Option<&crate::TraitSolver>,
    ) -> Result<(Self, Type), OwnershipError> {
        if body.recovered || !body.diagnostics.is_empty() || !body.validate().is_empty() {
            return Err(OwnershipError("cannot lower invalid Typed Core".into()));
        }
        let facts = flow.continuations_for(body).map_err(|error| OwnershipError(error.message))?;
        let evaluation = crate::evaluation_mir::EvaluationMir::lower_with_continuations(definition, body, facts)
            .map_err(|error| OwnershipError(format!("invalid Evaluation MIR: {error:?}")))?;
        let control = ControlMir::lower(&evaluation).map_err(|error| OwnershipError(format!("invalid Control MIR: {error:?}")))?;
        let closure_flows = flow.closure_flows().iter().map(|(brand, child)|
            (crate::mir::lifted_callable_definition(*brand), child.clone())).collect();
        let ownership = Self::lower_body(control, flow, &closure_flows, signatures, solver, &[])?;
        let result = if body.expression(body.root).ty == Type::Never {
            signatures.and_then(|signatures| signatures.definitions.get(&definition)).and_then(|header| match header {
                crate::ElaboratedHeader::Callable(signature) | crate::ElaboratedHeader::ValueAlias { signature, .. } => Some(signature.result.clone()),
                _ => None,
            }).unwrap_or(Type::Never)
        } else { body.expression(body.root).ty.clone() };
        Ok((ownership, result))
    }

    pub fn owners(&self) -> &[Owner] {
        &self.owners
    }
    pub fn loans(&self) -> &[Loan] {
        &self.loans
    }
    pub fn blocks(&self) -> &[OwnershipBlock] {
        &self.blocks
    }
    pub fn values(&self) -> &[ControlValueDecl] {
        &self.values
    }
    pub fn parameters(&self) -> &[ControlValue] {
        &self.parameters
    }
    pub fn scopes(&self) -> &[ControlScope] {
        &self.scopes
    }
    pub fn closures(&self) -> &[OwnershipClosure] {
        &self.closures
    }
    pub fn source_bindings(&self) -> &BTreeMap<crate::placeflow::PlaceBindingOrigin, ControlValue> {
        &self.source_bindings
    }
    pub fn live_in(&self) -> &[BTreeSet<ControlValue>] {
        &self.live_in
    }

    pub fn lower(
        control: ControlMir,
        flow: &PlaceFlow,
        signatures: Option<&ElaboratedInterface>,
    ) -> Result<Self, OwnershipError> {
        Self::lower_with_closure_flows(control, flow, &BTreeMap::new(), signatures)
    }

    pub(crate) fn lower_with_closure_flows(
        control: ControlMir,
        flow: &PlaceFlow,
        closure_flows: &BTreeMap<DefKey, PlaceFlow>,
        signatures: Option<&ElaboratedInterface>,
    ) -> Result<Self, OwnershipError> {
        let solver = signatures.map(crate::TraitSolver::new);
        Self::lower_body(control, flow, closure_flows, signatures, solver.as_ref(), &[])
    }

    fn lower_body(
        control: ControlMir,
        flow: &PlaceFlow,
        closure_flows: &BTreeMap<DefKey, PlaceFlow>,
        signatures: Option<&ElaboratedInterface>,
        solver: Option<&crate::TraitSolver>,
        captures: &[crate::CaptureMode],
    ) -> Result<Self, OwnershipError> {
        control
            .validate()
            .map_err(|error| OwnershipError(format!("invalid control: {error:?}")))?;
        if !flow.diagnostics.is_empty() {
            return Err(OwnershipError(
                format!("ownership input has diagnosed obligations: {:?}", flow.diagnostics),
            ));
        }
        let mut owners = control
            .values()
            .iter()
            .enumerate()
            .map(|(index, decl)| {
                let value = ControlValue(index as u32);
                let kind = match &decl.ty {
                    Type::Reference {
                        mutability: crate::Mutability::Unique,
                        ..
                    } => OwnerKind::UniqueLoan,
                    Type::Reference { .. } => OwnerKind::SharedLoan,
                    Type::Callable { .. } => OwnerKind::Callable,
                    _ if control.parameters().contains(&value) => OwnerKind::Parameter,
                    _ => OwnerKind::Temporary,
                };
                let quantity = match &decl.ty {
                    Type::Callable { invocation, .. } => Some(*invocation),
                    Type::Reference {
                        mutability: crate::Mutability::Unique,
                        ..
                    } => Some(Quantity::AFFINE),
                    Type::Reference { .. } | Type::Scalar(_) | Type::Unit | Type::Never => {
                        Some(Quantity::UNRESTRICTED)
                    }
                    ty => signatures
                        .zip(solver)
                        .and_then(|(signatures, solver)| {
                            signatures
                                .principal_use_interval_with_solver(ty, solver)
                                .or_else(|| {
                                    signatures.principal_use_interval_with_bounds_and_solver(
                                        ty,
                                        &flow.lexical_bounds,
                                        solver,
                                    )
                                })
                        }),
                };
                Owner {
                    value,
                    kind,
                    retains_resumption: flow.retains_resumption(decl.source),
                    scope: decl.scope.or_else(|| {
                        control
                            .parameters()
                            .contains(&value)
                            .then_some(ControlScopeId(0))
                    }),
                    quantity,
                }
            })
            .collect::<Vec<_>>();
        for (value, mode) in control.parameters().iter().zip(captures) {
            owners[value.0 as usize].kind = OwnerKind::Capture(*mode);
        }
        for (index, scope) in control.scopes().iter().enumerate() {
            for binding in &scope.bindings {
                owners[binding.0 as usize].kind = OwnerKind::Binding;
                owners[binding.0 as usize].scope = Some(ControlScopeId(index as u32));
            }
        }
        let mut aliases = BTreeMap::new();
        let mut observed = BTreeSet::new();
        for block in control.blocks() {
            for parameter in &block.parameters {
                if !control.parameters().contains(parameter) {
                    owners[parameter.0 as usize].kind = OwnerKind::Join;
                }
            }
            for instruction in &block.instructions {
                if let ControlOperation::Read(source) = instruction.operation {
                    owners[instruction.destination.0 as usize].kind = OwnerKind::View;
                    aliases.insert(instruction.destination, source);
                }
                if matches!(
                    instruction.operation,
                    ControlOperation::Function { .. }
                        | ControlOperation::Capability(
                            ControlCapabilityOperation::HostFunction { .. }
                                | ControlCapabilityOperation::TraitMethod { .. }
                        )
                ) {
                    owners[instruction.destination.0 as usize].quantity =
                        Some(Quantity::UNRESTRICTED);
                }
                match &instruction.operation {
                    ControlOperation::Capability(ControlCapabilityOperation::Test {
                        subject,
                        ..
                    }) => {
                        // Testing a tag observes the place. Pattern bindings
                        // subsequently perform their own explicit transfers.
                        observed.insert(*subject);
                    }
                    ControlOperation::Capability(ControlCapabilityOperation::Resumption {
                        ..
                    }) => {
                        owners[instruction.destination.0 as usize].kind = OwnerKind::Continuation;
                    }
                    ControlOperation::Capability(ControlCapabilityOperation::ReadReference(
                        reference,
                    )) => {
                        observed.insert(*reference);
                        if owners[instruction.destination.0 as usize].quantity
                            != Some(Quantity::UNRESTRICTED)
                        {
                            owners[instruction.destination.0 as usize].kind = OwnerKind::View;
                        }
                    }
                    ControlOperation::Capability(ControlCapabilityOperation::Project {
                        base,
                        ..
                    }) => {
                        observed.insert(*base);
                    }
                    ControlOperation::Capability(
                        ControlCapabilityOperation::Borrow { place, .. }
                        | ControlCapabilityOperation::ReadPlace(place)
                        | ControlCapabilityOperation::Move(place)
                        | ControlCapabilityOperation::Assign { place, .. },
                    ) => {
                        observed.insert(place.root());
                    }
                    _ => {}
                }
            }
        }
        loop {
            let previous = observed.len();
            for instruction in control
                .blocks()
                .iter()
                .flat_map(|block| &block.instructions)
            {
                if observed.contains(&instruction.destination) {
                    // A binding establishes independent storage. Later
                    // observations of it cannot turn its initializer into a
                    // borrowed view of the pre-binding source place.
                    if owners[instruction.destination.0 as usize].kind == OwnerKind::Binding {
                        continue;
                    }
                    match instruction.operation {
                        ControlOperation::Read(source) | ControlOperation::Forward(source) => {
                            observed.insert(source);
                        }
                        // A completed copyable expression owns its result.
                        // Its temporary reference may be destroyed at this
                        // scope boundary, before a later pattern observes or
                        // binds the result. Do not retarget those later uses
                        // through the expired reference.
                        ControlOperation::EndScope { value: source, .. }
                            if owners[instruction.destination.0 as usize].quantity
                                != Some(Quantity::UNRESTRICTED) => {
                            observed.insert(source);
                        }
                        _ => {}
                    }
                }
            }
            if observed.len() == previous {
                break;
            }
        }
        let mut value_places = BTreeMap::new();
        let mut place_views = BTreeSet::new();
        for instruction in control
            .blocks()
            .iter()
            .flat_map(|block| &block.instructions)
        {
            let place = match &instruction.operation {
                ControlOperation::Read(source) => {
                    if place_views.contains(source) {
                        place_views.insert(instruction.destination);
                    }
                    value_places
                        .get(source)
                        .cloned()
                        .unwrap_or(ControlPlace::Local(*source))
                }
                ControlOperation::Capability(ControlCapabilityOperation::ReadReference(
                    reference,
                )) => {
                    // A dereference used to name a projected place is a view,
                    // even when copying the entire referent would be legal.
                    // Giving that intermediate an owner would destroy an
                    // unrequested copy (and can recursively invoke Drop).
                    if observed.contains(&instruction.destination) {
                        owners[instruction.destination.0 as usize].kind = OwnerKind::View;
                    }
                    if owners[instruction.destination.0 as usize].kind == OwnerKind::View {
                        place_views.insert(instruction.destination);
                    }
                    ControlPlace::Deref {
                        reference: *reference,
                        ty: control.values()[instruction.destination.0 as usize]
                            .ty
                            .clone(),
                    }
                }
                ControlOperation::Capability(ControlCapabilityOperation::Project {
                    base,
                    index,
                    field_count,
                }) => {
                    if observed.contains(&instruction.destination) {
                        owners[instruction.destination.0 as usize].kind = OwnerKind::View;
                        place_views.insert(instruction.destination);
                    }
                    ControlPlace::Field {
                        base: Box::new(
                            value_places
                                .get(base)
                                .cloned()
                                .unwrap_or(ControlPlace::Local(*base)),
                        ),
                        index: *index,
                        field_count: *field_count,
                        ty: control.values()[instruction.destination.0 as usize]
                            .ty
                            .clone(),
                    }
                }
                ControlOperation::EndScope { .. }
                    if owners[instruction.destination.0 as usize].quantity
                        == Some(Quantity::UNRESTRICTED) =>
                {
                    ControlPlace::Local(instruction.destination)
                }
                ControlOperation::Forward(source) | ControlOperation::EndScope { value: source, .. }
                    if place_views.contains(source)
                        && owners[instruction.destination.0 as usize].kind
                            != OwnerKind::Binding =>
                {
                    owners[instruction.destination.0 as usize].kind = OwnerKind::View;
                    place_views.insert(instruction.destination);
                    value_places
                        .get(source)
                        .cloned()
                        .unwrap_or(ControlPlace::Local(*source))
                }
                _ => ControlPlace::Local(instruction.destination),
            };
            value_places.insert(instruction.destination, place);
        }
        let mut replacements = BTreeMap::<ControlValue, Vec<ControlValue>>::new();
        for instruction in control.blocks().iter().flat_map(|block| &block.instructions) {
            if let ControlOperation::Capability(ControlCapabilityOperation::Assign {
                place: ControlPlace::Local(destination) | ControlPlace::Temporary(destination), value,
            }) = &instruction.operation {
                replacements.entry(*destination).or_default().push(*value);
            }
        }
        loop {
            let mut quantities = owners.iter().map(|owner| owner.quantity).collect::<Vec<_>>();
            for instruction in control
                .blocks()
                .iter()
                .flat_map(|block| &block.instructions)
            {
                let quantity = match &instruction.operation {
                    ControlOperation::Read(source)
                    | ControlOperation::Forward(source)
                    | ControlOperation::EndScope { value: source, .. } => Some(owners[source.0 as usize].quantity),
                    ControlOperation::Capability(ControlCapabilityOperation::Closure { closure, captures }) => {
                        let captures = captures.iter().zip(&control.closures()[closure.0 as usize].environment.captures)
                            .map(|(value, capture)| (*value, capture.mode)).collect::<Vec<_>>();
                        Some(environment_quantity(&captures, &owners))
                    }
                    _ => None,
                };
                if let Some(quantity) = quantity {
                    quantities[instruction.destination.0 as usize] = quantity;
                }
            }
            // A storage binding must admit every resident assigned to it,
            // not just its initializer. In particular an initially empty
            // callable environment cannot authorize copying a later affine
            // capture environment out of the same variable.
            for (destination, values) in &replacements {
                quantities[destination.0 as usize] = quantities[destination.0 as usize].and_then(|quantity|
                    values.iter().try_fold(quantity, |quantity, value|
                        quantity.intersection(owners[value.0 as usize].quantity?).ok()));
            }
            if owners.iter().zip(&quantities).all(|(owner, quantity)| owner.quantity == *quantity) {
                break;
            }
            for (owner, quantity) in owners.iter_mut().zip(quantities) { owner.quantity = quantity; }
        }
        let ControlMir {
            definition,
            safety,
            unsafe_execution,
            parameters,
            mut values,
            scopes,
            entry,
            blocks: control_blocks,
            labels,
            handlers,
            closures,
            source_bindings,
        } = control;
        let quantities = owners
            .iter()
            .map(|owner| owner.quantity)
            .collect::<Vec<_>>();
        let retained_resumptions = owners.iter().map(|owner| owner.retains_resumption).collect::<Vec<_>>();
        let place_transfer = |value: ControlValue| {
            if retained_resumptions[value.0 as usize] {
                ValueTransfer::RetainResumption
            } else if quantities[value.0 as usize] == Some(Quantity::UNRESTRICTED) {
                ValueTransfer::Copy
            } else {
                ValueTransfer::Move
            }
        };
        let views = owners
            .iter()
            .filter_map(|owner| (owner.kind == OwnerKind::View).then_some(owner.value))
            .collect::<BTreeSet<_>>();
        let transfer = |value: ControlValue| {
            // An already produced rvalue has its own owner to transfer.
            // Duplicability authorizes copying a place; it does not require
            // copying every temporary again at each forwarding boundary.
            if views.contains(&value) {
                place_transfer(value)
            } else {
                ValueTransfer::Move
            }
        };
        let mut loans = vec![];
        let mut blocks = vec![];
        for block in control_blocks {
            let mut instructions = vec![];
            for instruction in block.instructions {
                let operation = match instruction.operation {
                    ControlOperation::Tuple(fields) => OwnershipOperation::Construct {
                        aggregate: OwnershipAggregate::Tuple,
                        fields: fields
                            .into_iter()
                            .map(|value| OwnershipOperand {
                                value,
                                mode: transfer(value),
                            })
                            .collect(),
                    },
                    ControlOperation::Array(fields) => OwnershipOperation::Construct {
                        aggregate: OwnershipAggregate::Array,
                        fields: fields
                            .into_iter()
                            .map(|value| OwnershipOperand {
                                value,
                                mode: transfer(value),
                            })
                            .collect(),
                    },
                    ControlOperation::Capability(ControlCapabilityOperation::Record {
                        definition,
                        fields,
                    }) => OwnershipOperation::Construct {
                        aggregate: OwnershipAggregate::Record(definition),
                        fields: fields
                            .into_iter()
                            .map(|value| OwnershipOperand {
                                value,
                                mode: transfer(value),
                            })
                            .collect(),
                    },
                    ControlOperation::Capability(ControlCapabilityOperation::Enum {
                        definition,
                        variant,
                        fields,
                    }) => OwnershipOperation::Construct {
                        aggregate: OwnershipAggregate::Enum {
                            definition,
                            variant,
                        },
                        fields: fields
                            .into_iter()
                            .map(|value| OwnershipOperand {
                                value,
                                mode: transfer(value),
                            })
                            .collect(),
                    },
                    ControlOperation::Forward(value) => OwnershipOperation::Transfer {
                        value,
                        mode: transfer(value),
                    },
                    ControlOperation::Read(value) => OwnershipOperation::Read(value),
                    ControlOperation::Discard(value) => {
                        // A lexical read is a view, not an owner to destroy.
                        // Materialize its consuming use explicitly, preserving
                        // the original only when generic Use permits a copy.
                        let owner = if aliases.contains_key(&value) {
                            let destination = ControlValue(
                                u32::try_from(values.len())
                                    .map_err(|_| OwnershipError("owner arena exhausted".into()))?,
                            );
                            let mut declaration = values[value.0 as usize].clone();
                            declaration.scope = Some(instruction.scope);
                            values.push(declaration);
                            let mut owner = owners[value.0 as usize].clone();
                            owner.value = destination;
                            owner.kind = OwnerKind::Temporary;
                            owner.scope = Some(instruction.scope);
                            owners.push(owner);
                            instructions.push(OwnershipInstruction {
                                scope: instruction.scope,
                                destination,
                                operation: OwnershipOperation::Transfer {
                                    value,
                                    mode: transfer(value),
                                },
                            });
                            OwnerId(destination.0)
                        } else {
                            OwnerId(value.0)
                        };
                        OwnershipOperation::Discard(owner)
                    }
                    ControlOperation::EndScope { scope, value, .. } => {
                        OwnershipOperation::ExitScope {
                            scope,
                            result: value,
                            mode: transfer(value),
                            owners: vec![], // Filled from forward owner availability.
                        }
                    }
                    ControlOperation::Capability(ControlCapabilityOperation::Borrow {
                        place,
                        unique,
                    }) => {
                        let id = LoanId(loans.len() as u32);
                        loans.push(Loan {
                            id,
                            destination: instruction.destination,
                            place: resolve_place(place, &value_places),
                            unique,
                        });
                        OwnershipOperation::Borrow(id)
                    }
                    ControlOperation::Capability(ControlCapabilityOperation::Move(place)) => {
                        OwnershipOperation::MovePlace(resolve_place(place, &value_places))
                    }
                    ControlOperation::Capability(ControlCapabilityOperation::Assign {
                        place,
                        value,
                    }) => OwnershipOperation::Replace {
                        place: resolve_place(place, &value_places),
                        value,
                        mode: transfer(value),
                    },
                    ControlOperation::Capability(ControlCapabilityOperation::ReadPlace(place)) => {
                        OwnershipOperation::ReadPlace {
                            place: resolve_place(place, &value_places),
                            mode: place_transfer(instruction.destination),
                        }
                    }
                    ControlOperation::Capability(ControlCapabilityOperation::ReadReference(
                        value,
                    )) => OwnershipOperation::ReadReference(value),
                    ControlOperation::Capability(ControlCapabilityOperation::Project {
                        base,
                        index,
                        field_count,
                    }) => OwnershipOperation::Project {
                        place: value_places[&instruction.destination].clone(),
                        base,
                        index,
                        field_count,
                        mode: if observed.contains(&instruction.destination) {
                            ValueTransfer::Reborrow
                        } else {
                            place_transfer(instruction.destination)
                        },
                    },
                    ControlOperation::Capability(ControlCapabilityOperation::Closure {
                        closure,
                        captures,
                    }) => OwnershipOperation::Capture {
                        closure,
                        captures: captures
                            .iter()
                            .zip(&closures[closure.0 as usize].environment.captures)
                            .map(|(value, capture)| (*value, capture.mode))
                            .collect(),
                    },
                    operation => OwnershipOperation::Compute(match operation {
                        ControlOperation::Literal(text) => OwnershipComputation::Literal(text),
                        ControlOperation::ConstValue(value) => OwnershipComputation::ConstValue(value),
                        ControlOperation::Unit => OwnershipComputation::Unit,
                        ControlOperation::Function {
                            definition,
                            arguments,
                        } => OwnershipComputation::Function {
                            definition,
                            arguments,
                        },
                        ControlOperation::Intrinsic {
                            operator,
                            arguments,
                        } => OwnershipComputation::Intrinsic {
                            operator,
                            arguments,
                        },
                        ControlOperation::Capability(capability) => match capability {
                            ControlCapabilityOperation::HostFunction {
                                definition,
                                arguments,
                                import,
                            } => OwnershipComputation::HostFunction {
                                definition,
                                arguments,
                                import,
                            },
                            ControlCapabilityOperation::TraitMethod {
                                evidence,
                                method,
                                trait_arguments,
                                method_arguments,
                                deferred,
                            } => OwnershipComputation::TraitMethod {
                                evidence,
                                method,
                                trait_arguments,
                                method_arguments,
                                deferred,
                            },
                            ControlCapabilityOperation::Constant {
                                definition,
                                arguments,
                            } => OwnershipComputation::Constant {
                                definition,
                                arguments,
                            },
                            ControlCapabilityOperation::Test { subject, pattern } => {
                                OwnershipComputation::Test { subject, pattern }
                            }
                            ControlCapabilityOperation::Label(label) => {
                                OwnershipComputation::Label(label)
                            }
                            ControlCapabilityOperation::Resumption { handler, clause } => {
                                OwnershipComputation::Resumption { handler, clause }
                            }
                            _ => unreachable!("owner operations are elaborated above"),
                        },
                        _ => unreachable!("owner operations are elaborated above"),
                    }),
                };
                instructions.push(OwnershipInstruction {
                    scope: instruction.scope,
                    destination: instruction.destination,
                    operation,
                });
            }
            blocks.push(OwnershipBlock {
                parameters: block.parameters,
                instructions,
                terminator: OwnershipTerminator {
                    successors: block
                        .terminator
                        .edges()
                        .into_iter()
                        .map(|edge| OwnershipSuccessor {
                            target: edge.target,
                            arguments: edge
                                .arguments
                                .into_iter()
                                .map(|value| OwnershipOperand {
                                    value,
                                    mode: transfer(value),
                                })
                                .collect(),
                            inventory: vec![],
                        })
                        .collect(),
                    operands: block
                        .terminator
                        .inputs()
                        .into_iter()
                        .enumerate()
                        .map(|(index, value)| OwnershipOperand {
                            value,
                            mode: match &block.terminator {
                                ControlTerminator::Invoke { .. } if index == 0 => {
                                    ValueTransfer::Reborrow
                                }
                                ControlTerminator::SwitchBool { .. } if index == 0 => {
                                    ValueTransfer::Copy
                                }
                                _ => transfer(value),
                            },
                        })
                        .collect(),
                    control: block.terminator,
                    dispositions: vec![],
                },
            });
        }
        let closures = closures
            .into_iter()
            .map(|closure| {
                let child_flow =
                    closure_flows
                        .get(&closure.body.definition())
                        .ok_or_else(|| {
                            OwnershipError(
                                "closure is missing its independently checked source ownership"
                                    .into(),
                            )
                        })?;
                let captures = closure
                    .environment
                    .captures
                    .iter()
                    .map(|capture| capture.mode)
                    .collect::<Vec<_>>();
                Ok(OwnershipClosure {
                    environment: closure.environment,
                    body: Box::new(Self::lower_body(
                        *closure.body,
                        child_flow,
                        closure_flows,
                        signatures,
                        solver,
                        &captures,
                    )?),
                })
            })
            .collect::<Result<Vec<_>, OwnershipError>>()?;
        let mut result = Self {
            definition,
            safety,
            unsafe_execution,
            parameters,
            values,
            scopes,
            entry,
            labels,
            handlers,
            closures,
            source_bindings,
            source_flow: flow.clone(),
            owners,
            loans,
            blocks,
            live_in: vec![],
            aliases,
        };
        result.live_in = result.compute_liveness();
        result.elaborate_inventory();
        result.validate()?;
        Ok(result)
    }
}

impl OwnershipMir {
    fn compute_liveness(&self) -> Vec<BTreeSet<ControlValue>> {
        let mut live = vec![BTreeSet::new(); self.blocks.len()];
        loop {
            let mut changed = false;
            for (index, block) in self.blocks.iter().enumerate().rev() {
                let mut values = BTreeSet::new();
                for edge in block.terminator.control.edges() {
                    values.extend(live[edge.target.0 as usize].iter().copied());
                }
                values.extend(block.terminator.control.inputs());
                for instruction in block.instructions.iter().rev() {
                    values.remove(&instruction.destination);
                    values.extend(instruction.operation.inputs(&self.loans));
                }
                for parameter in &block.parameters {
                    values.remove(parameter);
                }
                if live[index] != values {
                    live[index] = values;
                    changed = true;
                }
            }
            if !changed {
                return live;
            }
        }
    }
}

fn resolve_place(
    place: ControlPlace,
    values: &BTreeMap<ControlValue, ControlPlace>,
) -> ControlPlace {
    match place {
        ControlPlace::Local(value) | ControlPlace::Temporary(value) => values
            .get(&value)
            .cloned()
            .unwrap_or(ControlPlace::Local(value)),
        ControlPlace::Field {
            base,
            index,
            field_count,
            ty,
        } => ControlPlace::Field {
            base: Box::new(resolve_place(*base, values)),
            index,
            field_count,
            ty,
        },
        place @ ControlPlace::Deref { .. } => place,
    }
}
