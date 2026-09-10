//! Closed executable instances of Ownership MIR. This language has no trait
//! method selection, generic source call target, or deferred scalar type.
//! Destruction remains an owner disposition; concrete cleanup is a later pass.
use crate::control_mir::*;
use crate::ownership_mir::{
    Loan, LoanId, Owner, OwnerDisposition, OwnerId, OwnershipAggregate,
    OwnershipOperand, OwnershipSuccessor, ValueTransfer,
};
use crate::{DefKey, GenericArgument, InstanceKey, PlaceFlow, Safety, Type};
use std::collections::{BTreeMap, BTreeSet};

mod graph;
mod layout;
pub(crate) use layout::validate_layout_closure;
mod lower;
mod program;
mod regions;
mod validate;
pub(crate) use validate::closed_type;
pub use program::{SpecializationInput, SpecializedDiscoveryError, SpecializedProgram};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpecializedComputation {
    Literal(String),
    Unit,
    /// An executable key, or a sealed machine leaf with closed type arguments.
    Function {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
    },
    HostFunction {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
        import: crate::signature::HostImport,
    },
    Intrinsic {
        operator: String,
        arguments: Vec<ControlValue>,
    },
    Constant {
        definition: DefKey,
    },
    Test {
        subject: ControlValue,
        pattern: crate::CorePattern,
    },
    Label(ControlLabelId),
    Resumption {
        handler: ControlHandlerId,
        clause: u32,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpecializedOperation {
    Compute(SpecializedComputation),
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
    PrepareInvocation(ControlPlace),
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
pub struct SpecializedInstruction {
    pub scope: ControlScopeId,
    pub destination: ControlValue,
    pub operation: SpecializedOperation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpecializedCallTarget {
    Direct(DefKey),
    Primitive {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
    },
    Host {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
        import: crate::signature::HostImport,
    },
    Resumption {
        handler: ControlHandlerId,
        clause: u32,
    },
    Indirect,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpecializedControl {
    Goto(ControlEdge),
    SwitchBool {
        condition: ControlValue,
        on_true: ControlEdge,
        on_false: ControlEdge,
    },
    Invoke {
        callee: ControlValue,
        target: SpecializedCallTarget,
        arguments: Vec<ControlValue>,
        result: ControlValue,
        contract: crate::evaluation_mir::EvaluationCallContract,
        continuation: Option<ControlBlockId>,
    },
    Return(ControlValue),
    Unreachable,
    Transfer(ControlTransfer),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecializedTerminator {
    pub control: SpecializedControl,
    pub operands: Vec<OwnershipOperand>,
    pub dispositions: Vec<(OwnerId, OwnerDisposition)>,
    pub successors: Vec<OwnershipSuccessor>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecializedBlock {
    pub parameters: Vec<ControlValue>,
    pub instructions: Vec<SpecializedInstruction>,
    pub terminator: SpecializedTerminator,
}

#[derive(Clone, Debug)]
pub struct SpecializedClosure {
    pub environment: crate::CaptureEnvironment,
    pub body: Box<SpecializedMir>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecializedLayout {
    pub ty: Type,
    pub source_contract: crate::Digest,
    pub is_enum: bool,
    pub variants: Vec<Vec<Type>>,
}

#[derive(Clone, Debug)]
pub struct SpecializedMir {
    pub(crate) definition: DefKey,
    pub(crate) source_definition: DefKey,
    pub(crate) instance: InstanceKey,
    pub(crate) safety: Safety,
    pub(crate) unsafe_execution: bool,
    pub(crate) parameters: Vec<ControlValue>,
    pub(crate) values: Vec<ControlValueDecl>,
    pub(crate) result: Type,
    pub(crate) scopes: Vec<ControlScope>,
    pub(crate) entry: ControlBlockId,
    pub(crate) labels: Vec<ControlLabel>,
    pub(crate) handlers: Vec<ControlHandler>,
    pub(crate) closures: Vec<SpecializedClosure>,
    pub(crate) source_bindings: BTreeMap<crate::placeflow::PlaceBindingOrigin, ControlValue>,
    pub(crate) source_flow: PlaceFlow,
    pub(crate) minimum_discharge: crate::placeflow::DischargedMinimum,
    pub(crate) owners: Vec<Owner>,
    pub(crate) loans: Vec<Loan>,
    pub(crate) blocks: Vec<SpecializedBlock>,
    /// Includes ordinary functions and constants, never opaque machine leaves.
    pub(crate) dependencies: BTreeMap<DefKey, InstanceKey>,
    /// Declaration-only function values do not occupy a runtime register.
    pub(crate) symbols: BTreeSet<ControlValue>,
    pub(crate) primitive_definitions: BTreeSet<DefKey>,
    pub(crate) layouts: Vec<SpecializedLayout>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecializedError(pub String);

impl SpecializedMir {
    pub fn definition(&self) -> DefKey {
        self.definition
    }
    pub fn instance(&self) -> &InstanceKey {
        &self.instance
    }
    pub fn values(&self) -> &[ControlValueDecl] {
        &self.values
    }
    pub fn blocks(&self) -> &[SpecializedBlock] {
        &self.blocks
    }
    pub fn result(&self) -> &Type {
        &self.result
    }
    pub fn closures(&self) -> &[SpecializedClosure] {
        &self.closures
    }
    pub fn dependencies(&self) -> &BTreeMap<DefKey, InstanceKey> {
        &self.dependencies
    }
    pub fn layouts(&self) -> &[SpecializedLayout] {
        &self.layouts
    }
}

impl SpecializedOperation {
    pub(super) fn inputs(&self, loans: &[Loan]) -> Vec<ControlValue> {
        match self {
            Self::Compute(SpecializedComputation::Intrinsic { arguments, .. }) => arguments.clone(),
            Self::Compute(SpecializedComputation::Test { subject, .. }) => vec![*subject],
            Self::Compute(_) => vec![],
            Self::Construct { fields, .. } => fields.iter().map(|operand| operand.value).collect(),
            Self::Transfer { value, .. } | Self::Read(value) | Self::ReadReference(value) => {
                vec![*value]
            }
            Self::ReadPlace { place, .. } | Self::MovePlace(place) | Self::PrepareInvocation(place) => vec![place.root()],
            Self::Project { place, base, .. } => vec![place.root(), *base],
            Self::Borrow(id) => loans
                .get(id.0 as usize)
                .map(|loan| vec![loan.place.root()])
                .unwrap_or_default(),
            Self::Replace { place, value, .. } => vec![place.root(), *value],
            Self::Discard(owner) => vec![ControlValue(owner.0)],
            Self::ExitScope { result, .. } => vec![*result],
            Self::Capture { captures, .. } => captures.iter().map(|(value, _)| *value).collect(),
        }
    }
}

impl SpecializedControl {
    pub(super) fn edges(&self) -> Vec<ControlEdge> {
        match self {
            Self::Goto(edge) => vec![edge.clone()],
            Self::SwitchBool {
                on_true, on_false, ..
            } => vec![on_true.clone(), on_false.clone()],
            Self::Invoke {
                result,
                continuation: Some(target),
                ..
            } => vec![ControlEdge {
                target: *target,
                arguments: vec![*result],
            }],
            Self::Transfer(transfer) => match transfer {
                ControlTransfer::Leave { edge, .. }
                | ControlTransfer::CompleteHandler { edge, .. }
                | ControlTransfer::FinishClause { edge, .. } => vec![edge.clone()],
                ControlTransfer::EnterHandler {
                    computation,
                    clauses,
                    ..
                } => std::iter::once(computation.clone())
                    .chain(clauses.iter().cloned())
                    .collect(),
                ControlTransfer::Perform {
                    result,
                    continuation: Some(target),
                    ..
                } => vec![ControlEdge {
                    target: *target,
                    arguments: vec![*result],
                }],
                _ => vec![],
            },
            _ => vec![],
        }
    }
    pub(super) fn inputs(&self) -> Vec<ControlValue> {
        match self {
            Self::Goto(edge) => edge.arguments.clone(),
            Self::SwitchBool {
                condition,
                on_true,
                on_false,
            } => std::iter::once(*condition)
                .chain(on_true.arguments.iter().copied())
                .chain(on_false.arguments.iter().copied())
                .collect(),
            Self::Invoke {
                callee, arguments, ..
            } => std::iter::once(*callee)
                .chain(arguments.iter().copied())
                .collect(),
            Self::Return(value) => vec![*value],
            Self::Unreachable => vec![],
            Self::Transfer(transfer) => match transfer {
                ControlTransfer::Leave { edge, .. } => edge.arguments.clone(),
                ControlTransfer::CompleteHandler { value, .. }
                | ControlTransfer::FinishClause { value, .. }
                | ControlTransfer::TailResume { value, .. } => vec![*value],
                ControlTransfer::Perform { arguments, .. } => arguments.clone(),
                ControlTransfer::EnterHandler { computation, .. } => computation.arguments.clone(),
                ControlTransfer::Forward { .. } => vec![],
            },
        }
    }
}
