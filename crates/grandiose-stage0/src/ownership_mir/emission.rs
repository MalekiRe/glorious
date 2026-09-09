//! Emits the ownership-elaborated CFG into the existing concrete MIR ABI.
//! No Control MIR body or Core expression graph is retained or consulted.

use super::*;
use crate::{
    MirBlock, MirBlockId, MirControlTables, MirFunction, MirInstruction, MirLocal, MirLocalDecl,
    MirScopeId, MirTerminator, PrimitiveRole, ScalarType,
};

fn place_path(place: &ControlPlace) -> (ControlValue, Vec<u32>, bool) {
    match place {
        ControlPlace::Local(value) | ControlPlace::Temporary(value) => (*value, vec![], false),
        ControlPlace::Deref { reference, .. } => (*reference, vec![], true),
        ControlPlace::Field { base, index, .. } => {
            let (root, mut fields, reborrow) = place_path(base);
            fields.push(*index);
            (root, fields, reborrow)
        }
    }
}

fn plain(ty: &Type) -> bool {
    !matches!(ty, Type::Infer(_) | Type::Error)
}

fn emit_operand(
    operand: OwnershipOperand,
    source: MirLocal,
    ty: &Type,
    locals: &mut Vec<MirLocalDecl>,
    instructions: &mut Vec<MirInstruction>,
) -> Option<MirLocal> {
    if operand.mode != ValueTransfer::Move {
        return Some(source);
    }
    let dst = MirLocal(u32::try_from(locals.len()).ok()?);
    locals.push(MirLocalDecl {
        source: CoreId(u32::MAX),
        ty: ty.clone(),
    });
    instructions.push(MirInstruction::Move { dst, src: source });
    Some(dst)
}

// Concrete CFG arguments always move into their target registers. Honor an
// Ownership MIR copy by creating the independent outgoing owner first.
fn edge_arguments(
    edge: &OwnershipSuccessor,
    target: &OwnershipBlock,
    values: &[ControlValueDecl],
    local: &impl Fn(ControlValue) -> MirLocal,
    locals: &mut Vec<MirLocalDecl>,
    instructions: &mut Vec<MirInstruction>,
) -> Option<Vec<MirLocal>> {
    edge.arguments
        .iter()
        .zip(&target.parameters)
        .map(|(operand, parameter)| {
            let source = local(operand.value);
            if operand.mode != ValueTransfer::Copy || source == local(*parameter) {
                return Some(source);
            }
            let destination = MirLocal(u32::try_from(locals.len()).ok()?);
            locals.push(MirLocalDecl {
                source: CoreId(u32::MAX),
                ty: values[operand.value.0 as usize].ty.clone(),
            });
            instructions.push(MirInstruction::Copy {
                dst: destination,
                src: source,
            });
            Some(destination)
        })
        .collect()
}

impl OwnershipMir {
    /// Emit the migrated value domain. `None` means the adapter has not yet
    /// acquired this ownership/representation contract, not malformed Core.
    /// All source-owner phases still run on the returned legacy MIR body.
    pub(crate) fn emit_legacy_values(
        &self,
        declared_result: Type,
        capture_count: u32,
        primitives: Option<&BTreeMap<DefKey, PrimitiveRole>>,
        retain_destruction: bool,
        signatures: Option<&crate::ElaboratedInterface>,
    ) -> Option<(MirFunction, BTreeMap<DefKey, MirFunction>)> {
        // The compatibility ABI has no mandatory frame-transfer terminator.
        // Never silently turn a checked tail obligation into an ordinary call.
        if self.blocks.iter().any(|block| matches!(&block.terminator.control,
            ControlTerminator::Invoke { contract, .. } if contract.mandatory_tail)) {
            return None;
        }
        if !plain(&declared_result)
            || self
                .parameters
                .iter()
                .any(|value| !plain(&self.values[value.0 as usize].ty))
        {
            return None;
        }
        let mut functions = BTreeMap::new();
        let mut resumptions = BTreeMap::new();
        let mut aliases = BTreeMap::new();
        let mut direct_functions = BTreeSet::new();
        let mut host_imports = BTreeMap::new();
        let mut trait_methods = BTreeMap::new();
        let mutable_places = self
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter_map(|instruction| match &instruction.operation {
                OwnershipOperation::Replace { place, .. } => Some(place.root()),
                OwnershipOperation::Borrow(id) => Some(self.loans[id.0 as usize].place.root()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        for block in &self.blocks {
            for instruction in &block.instructions {
                if let OwnershipOperation::Read(value) = instruction.operation {
                    aliases.insert(instruction.destination, value);
                }
                if let OwnershipOperation::Compute(OwnershipComputation::Resumption {
                    handler,
                    clause,
                }) = instruction.operation
                {
                    resumptions.insert(instruction.destination, (handler, clause));
                }
                if let OwnershipOperation::Compute(OwnershipComputation::Function {
                    definition,
                    arguments,
                }) = &instruction.operation
                {
                    direct_functions.insert(instruction.destination);
                    functions.insert(instruction.destination, (*definition, arguments.clone()));
                }
                match &instruction.operation {
                    OwnershipOperation::Compute(OwnershipComputation::HostFunction {
                        definition,
                        arguments,
                        import,
                    }) => {
                        direct_functions.insert(instruction.destination);
                        functions.insert(instruction.destination, (*definition, arguments.clone()));
                        host_imports.insert(instruction.destination, import.clone());
                    }
                    OwnershipOperation::Compute(OwnershipComputation::TraitMethod {
                        evidence,
                        method,
                        trait_arguments,
                        method_arguments,
                        deferred,
                    }) => {
                        trait_methods.insert(
                            instruction.destination,
                            (
                                *method,
                                crate::MirTraitMethodInstance {
                                    evidence: *evidence,
                                    trait_arguments: trait_arguments.clone(),
                                    method_arguments: method_arguments.clone(),
                                    deferred: deferred.clone(),
                                },
                            ),
                        );
                    }
                    _ => {}
                }
            }
        }
        // Function identities are immutable symbolic values. Propagate them
        // across lexical aliases without creating an owned closure object.
        loop {
            let mut changed = false;
            for block in &self.blocks {
                for instruction in &block.instructions {
                    if let OwnershipOperation::Transfer { value: source, .. }
                    | OwnershipOperation::Read(source)
                    | OwnershipOperation::ExitScope { result: source, .. } =
                        instruction.operation
                        && let Some(resumption) = resumptions.get(&source).copied()
                        && !resumptions.contains_key(&instruction.destination)
                    {
                        resumptions.insert(instruction.destination, resumption);
                        changed = true;
                    }
                    if let OwnershipOperation::Transfer { value: source, .. }
                    | OwnershipOperation::Read(source)
                    | OwnershipOperation::ExitScope { result: source, .. } =
                        instruction.operation
                        && let Some(function) = functions.get(&source).cloned()
                        && !mutable_places.contains(&instruction.destination)
                        && !functions.contains_key(&instruction.destination)
                    {
                        if let Some(import) = host_imports.get(&source).cloned() {
                            host_imports.insert(instruction.destination, import);
                        }
                        functions.insert(instruction.destination, function);
                        changed = true;
                    }
                    if let OwnershipOperation::Transfer { value: source, .. }
                    | OwnershipOperation::Read(source)
                    | OwnershipOperation::ExitScope { result: source, .. } =
                        instruction.operation
                        && let Some(method) = trait_methods.get(&source).cloned()
                        && !mutable_places.contains(&instruction.destination)
                        && !trait_methods.contains_key(&instruction.destination)
                    {
                        trait_methods.insert(instruction.destination, method);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        // A direct callee is a symbolic identity, not a runtime closure. In
        // particular, its declaration-owned lifetime binders must not become
        // unused registers in the enclosing caller's concrete ABI.
        let mut runtime_values = BTreeSet::new();
        for block in &self.blocks {
            for instruction in &block.instructions {
                match &instruction.operation {
                    OwnershipOperation::Read(_)
                    | OwnershipOperation::Transfer { .. }
                    | OwnershipOperation::ExitScope { .. }
                        if functions.contains_key(&instruction.destination)
                            || trait_methods.contains_key(&instruction.destination) => {}
                    OwnershipOperation::Discard(_) => {}
                    operation => runtime_values.extend(operation.inputs(&self.loans)),
                }
            }
            match &block.terminator.control {
                ControlTerminator::Invoke {
                    callee, arguments, ..
                } => {
                    runtime_values.extend(arguments);
                    if !functions.contains_key(callee) && !trait_methods.contains_key(callee) {
                        runtime_values.insert(*callee);
                    }
                }
                terminator => runtime_values.extend(terminator.inputs()),
            }
        }
        let escaped_functions = runtime_values
            .iter()
            .filter_map(|value| functions.get(value))
            .collect::<Vec<_>>();
        let escaped_methods = runtime_values
            .iter()
            .filter_map(|value| trait_methods.get(value))
            .collect::<Vec<_>>();
        let symbols = functions
            .iter()
            .filter_map(|(value, identity)| {
                (!escaped_functions.contains(&identity)).then_some(*value)
            })
            .chain(trait_methods.iter().filter_map(|(value, identity)| {
                (!escaped_methods.contains(&identity)).then_some(*value)
            }))
            .collect::<BTreeSet<_>>();
        direct_functions.extend(functions.keys().copied());
        if self.values.iter().enumerate().any(|(index, value)| {
            !plain(&value.ty)
                && !functions.contains_key(&ControlValue(index as u32))
                && !resumptions.contains_key(&ControlValue(index as u32))
        }) {
            return None;
        }
        let mut locals: Vec<_> = self
            .values
            .iter()
            .enumerate()
            .map(|(index, value)| MirLocalDecl {
                ty: if symbols.contains(&ControlValue(index as u32)) {
                    Type::Unit
                } else {
                    value.ty.clone()
                },
                source: value.source,
            })
            .collect();
        let mut nominal_copy_descriptors = vec![];
        let mut building_nominal_copy_descriptors = vec![];
        let mut diagnostics = vec![];
        for value in &self.values {
            crate::mir::atomic::AtomicEmitter {
                locals: &mut locals,
                instructions: &mut vec![],
                nominal_copy_descriptors: &mut nominal_copy_descriptors,
                building_nominal_copy_descriptors: &mut building_nominal_copy_descriptors,
                diagnostics: &mut diagnostics,
                signatures,
                runtime_primitives: primitives,
            }
            .register_nominal_copy_descriptors(&value.ty);
        }
        let local = |mut value: ControlValue| {
            for _ in 0..aliases.len() {
                let Some(source) = aliases.get(&value) else {
                    break;
                };
                value = *source;
            }
            MirLocal(value.0)
        };
        let mut blocks = vec![];
        let mut edge_blocks = vec![];
        let mut lifted = BTreeMap::new();
        for block in &self.blocks {
            let mut instructions = vec![];
            for instruction in &block.instructions {
                let dst = local(instruction.destination);
                let ty = &self.values[instruction.destination.0 as usize].ty;
                let operation = match &instruction.operation {
                    OwnershipOperation::Construct { aggregate, fields } => {
                        let field_types = fields
                            .iter()
                            .map(|operand| self.values[operand.value.0 as usize].ty.clone())
                            .collect();
                        let fields = fields
                            .iter()
                            .map(|operand| {
                                emit_operand(
                                    *operand,
                                    local(operand.value),
                                    &self.values[operand.value.0 as usize].ty,
                                    &mut locals,
                                    &mut instructions,
                                )
                            })
                            .collect::<Option<Vec<_>>>()?;
                        match aggregate {
                            OwnershipAggregate::Tuple if fields.is_empty() && ty == &Type::Unit => {
                                MirInstruction::ConstUnit { dst }
                            }
                            OwnershipAggregate::Tuple => MirInstruction::MakeTuple { dst, fields },
                            OwnershipAggregate::Array => MirInstruction::MakeArray {
                                dst,
                                fields,
                                element_type: match ty {
                                    Type::Array(element) | Type::FixedArray { element, .. } => (**element).clone(),
                                    _ => return None,
                                },
                            },
                            OwnershipAggregate::Record(definition) => MirInstruction::MakeRecord {
                                dst,
                                definition: *definition,
                                fields,
                                field_types,
                            },
                            OwnershipAggregate::Enum {
                                definition,
                                variant,
                            } => MirInstruction::MakeEnum {
                                dst,
                                definition: *definition,
                                variant: *variant,
                                fields,
                                field_types,
                            },
                        }
                    }
                    OwnershipOperation::Discard(owner) => {
                        if retain_destruction
                            && self.owners[owner.0 as usize].kind != OwnerKind::View
                            && !symbols.contains(&ControlValue(owner.0))
                        {
                            instructions.push(MirInstruction::Drop {
                                local: local(self.owners[owner.0 as usize].value),
                            });
                        }
                        MirInstruction::ConstUnit { dst }
                    }
                    OwnershipOperation::Read(_) => continue,
                    OwnershipOperation::Transfer { .. }
                        if symbols.contains(&instruction.destination) =>
                    {
                        continue;
                    }
                    OwnershipOperation::Transfer { value, mode } => {
                        if *mode == ValueTransfer::Move {
                            MirInstruction::Move {
                                dst,
                                src: local(*value),
                            }
                        } else {
                            MirInstruction::Copy {
                                dst,
                                src: local(*value),
                            }
                        }
                    }
                    OwnershipOperation::ExitScope {
                        result,
                        mode,
                        owners,
                        ..
                    } => {
                        if !symbols.contains(&instruction.destination) {
                            instructions.push(if *mode == ValueTransfer::Move {
                                MirInstruction::Move {
                                    dst,
                                    src: local(*result),
                                }
                            } else {
                                MirInstruction::Copy {
                                    dst,
                                    src: local(*result),
                                }
                            });
                        }
                        if retain_destruction {
                            for owner in owners {
                                if !symbols.contains(&ControlValue(owner.0)) {
                                    instructions.push(MirInstruction::Drop {
                                        local: local(self.owners[owner.0 as usize].value),
                                    });
                                }
                            }
                        }
                        continue;
                    }
                    OwnershipOperation::Borrow(loan) => {
                        let loan = &self.loans[loan.0 as usize];
                        let (root, fields, reborrow) = place_path(&loan.place);
                        MirInstruction::Borrow {
                            dst,
                            src: local(root),
                            fields,
                            unique: loan.unique,
                            reborrow,
                        }
                    }
                    OwnershipOperation::ReadReference(reference) => MirInstruction::DerefCopy {
                        dst,
                        reference: local(*reference),
                    },
                    OwnershipOperation::ReadPlace { place, mode } => {
                        let (root, fields, reborrow) = place_path(place);
                        if fields.is_empty() && !reborrow {
                            if *mode == ValueTransfer::Move {
                                MirInstruction::Move {
                                    dst,
                                    src: local(root),
                                }
                            } else {
                                MirInstruction::Copy {
                                    dst,
                                    src: local(root),
                                }
                            }
                        } else if !reborrow && *mode == ValueTransfer::Move {
                            MirInstruction::TakeProjection {
                                dst,
                                base: local(root),
                                fields,
                            }
                        } else if reborrow && fields.is_empty() {
                            if *mode == ValueTransfer::Move {
                                MirInstruction::DerefMove {
                                    dst,
                                    reference: local(root),
                                }
                            } else {
                                MirInstruction::DerefCopy {
                                    dst,
                                    reference: local(root),
                                }
                            }
                        } else {
                            let reference = MirLocal(u32::try_from(locals.len()).ok()?);
                            locals.push(MirLocalDecl {
                                source: CoreId(u32::MAX),
                                ty: Type::Reference {
                                    mutability: if *mode == ValueTransfer::Move {
                                        crate::Mutability::Unique
                                    } else {
                                        crate::Mutability::Shared
                                    },
                                    lifetime: crate::Lifetime::Elided,
                                    referent: Box::new(ty.clone()),
                                },
                            });
                            instructions.push(MirInstruction::Borrow {
                                dst: reference,
                                src: local(root),
                                fields,
                                unique: *mode == ValueTransfer::Move,
                                reborrow,
                            });
                            if *mode == ValueTransfer::Move {
                                MirInstruction::DerefMove { dst, reference }
                            } else {
                                MirInstruction::DerefCopy { dst, reference }
                            }
                        }
                    }
                    OwnershipOperation::Project {
                        place,
                        base,
                        index,
                        field_count,
                        mode,
                    } => {
                        let (root, fields, reborrow) = place_path(place);
                        if *mode == ValueTransfer::Move && !reborrow {
                            MirInstruction::TakeProjection {
                                dst,
                                base: local(root),
                                fields,
                            }
                        } else if reborrow {
                            let reference = MirLocal(u32::try_from(locals.len()).ok()?);
                            locals.push(MirLocalDecl {
                                source: CoreId(u32::MAX),
                                ty: Type::Reference {
                                    mutability: if *mode == ValueTransfer::Move {
                                        crate::Mutability::Unique
                                    } else {
                                        crate::Mutability::Shared
                                    },
                                    lifetime: crate::Lifetime::Elided,
                                    referent: Box::new(ty.clone()),
                                },
                            });
                            instructions.push(MirInstruction::Borrow {
                                dst: reference,
                                src: local(root),
                                fields,
                                unique: *mode == ValueTransfer::Move,
                                reborrow: true,
                            });
                            if *mode == ValueTransfer::Move {
                                MirInstruction::DerefMove { dst, reference }
                            } else {
                                MirInstruction::DerefCopy { dst, reference }
                            }
                        } else {
                            match &self.values[base.0 as usize].ty {
                                Type::Tuple(_) => MirInstruction::ProjectTuple {
                                    dst,
                                    base: local(*base),
                                    index: *index,
                                    field_count: *field_count,
                                    field_type: ty.clone(),
                                },
                                Type::Array(_) | Type::FixedArray { .. } => MirInstruction::ProjectArray {
                                    dst,
                                    base: local(*base),
                                    index: *index,
                                    field_count: *field_count,
                                    element_type: ty.clone(),
                                },
                                _ => MirInstruction::ProjectRecord {
                                    dst,
                                    base: local(*base),
                                    index: *index,
                                    field_count: *field_count,
                                    field_type: ty.clone(),
                                },
                            }
                        }
                    }
                    OwnershipOperation::MovePlace(place) => {
                        let (root, fields, reborrow) = place_path(place);
                        if reborrow && fields.is_empty() {
                            MirInstruction::DerefMove {
                                dst,
                                reference: local(root),
                            }
                        } else if !reborrow && fields.is_empty() {
                            MirInstruction::Move {
                                dst,
                                src: local(root),
                            }
                        } else if !reborrow {
                            MirInstruction::TakeProjection {
                                dst,
                                base: local(root),
                                fields,
                            }
                        } else {
                            let reference = MirLocal(u32::try_from(locals.len()).ok()?);
                            locals.push(MirLocalDecl {
                                source: CoreId(u32::MAX),
                                ty: Type::Reference {
                                    mutability: crate::Mutability::Unique,
                                    lifetime: crate::Lifetime::Elided,
                                    referent: Box::new(ty.clone()),
                                },
                            });
                            instructions.push(MirInstruction::Borrow {
                                dst: reference,
                                src: local(root),
                                fields,
                                unique: true,
                                reborrow: true,
                            });
                            MirInstruction::DerefMove { dst, reference }
                        }
                    }
                    OwnershipOperation::Replace { place, value, mode } => {
                        let replacement = emit_operand(
                            OwnershipOperand {
                                value: *value,
                                mode: *mode,
                            },
                            local(*value),
                            &self.values[value.0 as usize].ty,
                            &mut locals,
                            &mut instructions,
                        )?;
                        let (root, fields, reborrow) = place_path(place);
                        if fields.is_empty() {
                            instructions.push(if reborrow {
                                MirInstruction::DerefStore {
                                    reference: local(root),
                                    src: replacement,
                                }
                            } else {
                                MirInstruction::Store {
                                    dst: local(root),
                                    src: replacement,
                                }
                            });
                        } else {
                            let reference = MirLocal(u32::try_from(locals.len()).ok()?);
                            locals.push(MirLocalDecl {
                                source: CoreId(u32::MAX),
                                ty: Type::Reference {
                                    mutability: crate::Mutability::Unique,
                                    lifetime: crate::Lifetime::Elided,
                                    referent: Box::new(self.values[value.0 as usize].ty.clone()),
                                },
                            });
                            instructions.push(MirInstruction::Borrow {
                                dst: reference,
                                src: local(root),
                                fields,
                                unique: true,
                                reborrow,
                            });
                            instructions.push(MirInstruction::DerefStore {
                                reference,
                                src: replacement,
                            });
                        }
                        MirInstruction::ConstUnit { dst }
                    }
                    OwnershipOperation::Capture { closure, captures } => {
                        let closure = &self.closures[closure.0 as usize];
                        let Type::Callable { result, .. } = ty else {
                            return None;
                        };
                        let callee = closure.body.definition;
                        if let std::collections::btree_map::Entry::Vacant(entry) =
                            lifted.entry(callee)
                        {
                            let (function, nested) = closure.body.emit_legacy_values(
                                (**result).clone(),
                                u32::try_from(captures.len()).ok()?,
                                primitives,
                                retain_destruction,
                                signatures,
                            )?;
                            entry.insert(function);
                            for (definition, function) in nested {
                                if lifted.insert(definition, function).is_some() {
                                    return None;
                                }
                            }
                        }
                        let mut captured = Vec::with_capacity(captures.len());
                        for ((value, mode), slot) in
                            captures.iter().zip(&closure.environment.captures)
                        {
                            let source = local(*value);
                            let value = match mode {
                                crate::CaptureMode::Copy | crate::CaptureMode::Move => {
                                    let destination = MirLocal(u32::try_from(locals.len()).ok()?);
                                    locals.push(MirLocalDecl {
                                        source: CoreId(u32::MAX),
                                        ty: slot.ty.clone(),
                                    });
                                    instructions.push(if *mode == crate::CaptureMode::Move {
                                        MirInstruction::Move {
                                            dst: destination,
                                            src: source,
                                        }
                                    } else {
                                        MirInstruction::Copy {
                                            dst: destination,
                                            src: source,
                                        }
                                    });
                                    destination
                                }
                                crate::CaptureMode::SharedBorrow
                                | crate::CaptureMode::UniqueBorrow => source,
                            };
                            captured.push(value);
                        }
                        MirInstruction::MakeCallable {
                            dst,
                            callee,
                            captures: captured,
                            generic_arguments: vec![],
                            trait_instance: None,
                            environment: Some(crate::MirCaptureEnvironment {
                                brand: closure.environment.brand,
                                destructor: None,
                                captures: closure
                                    .environment
                                    .captures
                                    .iter()
                                    .map(|capture| crate::MirCapture {
                                        mode: capture.mode,
                                        ty: capture.ty.clone(),
                                    })
                                    .collect(),
                            }),
                        }
                    }
                    OwnershipOperation::Compute(_)
                        if symbols.contains(&instruction.destination) =>
                    {
                        continue;
                    }
                    OwnershipOperation::Compute(computation) => match computation {
                        // Compile-time terms must cross Specialization before
                        // the legacy concrete ABI can represent their value.
                        OwnershipComputation::ConstValue(_) => return None,
                        OwnershipComputation::Unit => MirInstruction::ConstUnit { dst },
                        OwnershipComputation::Function {
                            definition,
                            arguments,
                        } => {
                            if primitives
                                .is_some_and(|primitives| primitives.contains_key(definition))
                            {
                                continue;
                            }
                            MirInstruction::MakeCallable {
                                dst,
                                callee: *definition,
                                captures: vec![],
                                generic_arguments: arguments.clone(),
                                trait_instance: None,
                                environment: None,
                            }
                        }
                        OwnershipComputation::Literal(text) => match ty {
                            Type::Unit => MirInstruction::ConstUnit { dst },
                            Type::Scalar(ScalarType::Bool)
                                if matches!(text.as_str(), "true" | "false") =>
                            {
                                MirInstruction::ConstBool {
                                    dst,
                                    value: text == "true",
                                }
                            }
                            Type::Scalar(ScalarType::Char) => MirInstruction::ConstChar {
                                dst,
                                value: crate::mir::parse_char_literal(text).ok()?,
                            },
                            Type::Scalar(ScalarType::Text) => MirInstruction::ConstText {
                                dst,
                                value: crate::mir::parse_text_literal(text).ok()?,
                            },
                            Type::Scalar(ScalarType::Bytes) => return None,
                            Type::StaticData {
                                tag,
                                alignment,
                                element,
                            } if matches!(element.as_ref(), Type::Scalar(ScalarType::U8)) => {
                                let bytes = if text.starts_with("b\"") {
                                    crate::mir::parse_byte_literal(text).ok()?
                                } else {
                                    crate::mir::parse_text_literal(text).ok()?.into_bytes()
                                };
                                MirInstruction::ConstStaticData {
                                    dst,
                                    tag: *tag,
                                    alignment: *alignment,
                                    bytes,
                                }
                            }
                            Type::Generic(_) if crate::core::literal_is_numeric(text) => {
                                MirInstruction::DeferredLiteral {
                                    dst,
                                    text: text.clone(),
                                }
                            }
                            Type::Scalar(scalar) => {
                                crate::mir::materialize_numeric_literal(dst, text, *scalar).ok()?
                            }
                            _ => return None,
                        },
                        OwnershipComputation::Intrinsic {
                            operator,
                            arguments,
                        } => {
                            crate::mir::atomic::AtomicEmitter {
                                locals: &mut locals,
                                instructions: &mut instructions,
                                nominal_copy_descriptors: &mut nominal_copy_descriptors,
                                building_nominal_copy_descriptors:
                                    &mut building_nominal_copy_descriptors,
                                diagnostics: &mut diagnostics,
                                signatures,
                                runtime_primitives: primitives,
                            }
                            .intrinsic(
                                self.values[instruction.destination.0 as usize].source,
                                dst,
                                operator.clone(),
                                arguments.iter().copied().map(local).collect(),
                            )?;
                            continue;
                        }
                        OwnershipComputation::Test { subject, pattern } => {
                            MirInstruction::PatternTest {
                                dst,
                                subject: local(*subject),
                                pattern: crate::mir::lower_pattern(pattern.clone())?,
                            }
                        }
                        OwnershipComputation::Label(label) => {
                            let label = &self.labels[label.0 as usize];
                            MirInstruction::MakeLabel {
                                label: crate::MirLabelId::UNASSIGNED,
                                dst,
                                brand: label.brand,
                                target: MirBlockId(label.target.0),
                                destination: local(label.result),
                            }
                        }
                        OwnershipComputation::Resumption { .. } => {
                            MirInstruction::CaptureResumption {
                                site: crate::MirResumptionSiteId::UNASSIGNED,
                                dst,
                            }
                        }
                        OwnershipComputation::HostFunction { .. } => continue,
                        OwnershipComputation::TraitMethod {
                            method,
                            evidence,
                            trait_arguments,
                            method_arguments,
                            deferred,
                        } => MirInstruction::MakeCallable {
                            dst,
                            callee: *method,
                            captures: vec![],
                            generic_arguments: vec![],
                            environment: None,
                            trait_instance: Some(crate::MirTraitMethodInstance {
                                evidence: *evidence,
                                trait_arguments: trait_arguments.clone(),
                                method_arguments: method_arguments.clone(),
                                deferred: deferred.clone(),
                            }),
                        },
                        OwnershipComputation::Constant {
                            definition,
                            arguments,
                        } => MirInstruction::Call {
                            dst,
                            callee: *definition,
                            generic_arguments: arguments.clone(),
                            trait_instance: None,
                            arguments: vec![],
                        },
                    },
                };
                instructions.push(operation);
            }
            let mut routes = vec![];
            for edge in &block.terminator.successors {
                let mut copies = vec![];
                let arguments = edge_arguments(
                    edge,
                    &self.blocks[edge.target.0 as usize],
                    &self.values,
                    &local,
                    &mut locals,
                    &mut copies,
                )?;
                if matches!(
                    block.terminator.control,
                    ControlTerminator::SwitchBool { .. }
                ) && !copies.is_empty()
                {
                    // Copies belong to the selected edge, not to both sides
                    // of a branch. The temporary owner is moved at its exit.
                    let bridge =
                        MirBlockId(u32::try_from(self.blocks.len() + edge_blocks.len()).ok()?);
                    edge_blocks.push(MirBlock {
                        scope: MirScopeId::ROOT,
                        parameters: vec![],
                        instructions: copies,
                        terminator: MirTerminator::Goto {
                            target: MirBlockId(edge.target.0),
                            arguments,
                        },
                    });
                    routes.push((bridge, vec![]));
                } else {
                    instructions.extend(copies);
                    routes.push((MirBlockId(edge.target.0), arguments));
                }
            }
            let returned = if let ControlTerminator::Return(value) = block.terminator.control {
                if block.terminator.operands[0].mode == ValueTransfer::Copy {
                    let destination = MirLocal(u32::try_from(locals.len()).ok()?);
                    locals.push(MirLocalDecl {
                        source: CoreId(u32::MAX),
                        ty: self.values[value.0 as usize].ty.clone(),
                    });
                    instructions.push(MirInstruction::Copy {
                        dst: destination,
                        src: local(value),
                    });
                    Some(destination)
                } else {
                    Some(local(value))
                }
            } else {
                None
            };
            if retain_destruction {
                for (owner, disposition) in block.terminator.dispositions.iter().rev() {
                    if *disposition == OwnerDisposition::Abandon
                        && !symbols.contains(&ControlValue(owner.0))
                        && !matches!(
                            self.owners[owner.0 as usize].kind,
                            OwnerKind::View | OwnerKind::Continuation | OwnerKind::Capture(_)
                        )
                    {
                        instructions.push(MirInstruction::Drop {
                            local: local(self.owners[owner.0 as usize].value),
                        });
                    }
                }
            }
            let terminator = match &block.terminator.control {
                ControlTerminator::Goto(_) => MirTerminator::Goto {
                    target: routes[0].0,
                    arguments: routes[0].1.clone(),
                },
                ControlTerminator::SwitchBool { condition, .. } => MirTerminator::SwitchBool {
                    condition: local(*condition),
                    then_target: routes[0].0,
                    then_arguments: routes[0].1.clone(),
                    else_target: routes[1].0,
                    else_arguments: routes[1].1.clone(),
                },
                ControlTerminator::Invoke {
                    callee,
                    arguments,
                    result,
                    continuation,
                    ..
                } => {
                    let arguments = arguments
                        .iter()
                        .zip(block.terminator.operands.iter().skip(1))
                        .map(|(value, operand)| {
                            let operand = *operand;
                            emit_operand(
                                operand,
                                local(*value),
                                &self.values[value.0 as usize].ty,
                                &mut locals,
                                &mut instructions,
                            )
                        })
                        .collect::<Option<Vec<_>>>()?;
                    if resumptions.contains_key(callee) {
                        if arguments.len() != 1 {
                            return None;
                        }
                        instructions.push(MirInstruction::ResumeReturn {
                            site: crate::MirResumptionSiteId::UNASSIGNED,
                            dst: local(*result),
                            value: arguments[0],
                        });
                    } else if direct_functions.contains(callee) {
                        let (definition, generic_arguments) = functions.get(callee)?;
                        crate::mir::atomic::AtomicEmitter {
                            locals: &mut locals,
                            instructions: &mut instructions,
                            nominal_copy_descriptors: &mut nominal_copy_descriptors,
                            building_nominal_copy_descriptors:
                                &mut building_nominal_copy_descriptors,
                            diagnostics: &mut diagnostics,
                            signatures,
                            runtime_primitives: primitives,
                        }
                        .call(
                            self.values[result.0 as usize].source,
                            local(*result),
                            *definition,
                            generic_arguments.clone(),
                            host_imports.get(callee).cloned(),
                            arguments,
                        )?;
                    } else if let Some((method, instance)) = trait_methods.get(callee) {
                        instructions.push(MirInstruction::Call {
                            dst: local(*result),
                            callee: *method,
                            generic_arguments: vec![],
                            trait_instance: Some(instance.clone()),
                            arguments,
                        });
                    } else {
                        instructions.push(MirInstruction::CallIndirect {
                            dst: local(*result),
                            callee: local(*callee),
                            arguments,
                        });
                    }
                    match continuation {
                        Some(target) => MirTerminator::Goto {
                            target: MirBlockId(target.0),
                            arguments: vec![local(*result)],
                        },
                        None => MirTerminator::Unreachable,
                    }
                }
                ControlTerminator::Return(_) => MirTerminator::Return { value: returned? },
                ControlTerminator::Unreachable => MirTerminator::Unreachable,
                ControlTerminator::Transfer(transfer) => {
                    let edge = match transfer {
                        ControlTransfer::Leave { label, .. } => {
                            let label = &self.labels[label.0 as usize];
                            blocks.push(MirBlock {
                                scope: MirScopeId::ROOT,
                                parameters: block.parameters.iter().copied().map(local).collect(),
                                instructions,
                                terminator: MirTerminator::Leave {
                                    label: crate::MirLabelId::UNASSIGNED,
                                    brand: label.brand,
                                    target: routes[0].0,
                                    arguments: routes[0].1.clone(),
                                    cleanup: crate::MirCleanupPlan {
                                        source_storage_scope: crate::MirSourceStorageScopeId::ROOT,
                                        target_storage_scope: crate::MirSourceStorageScopeId::ROOT,
                                        moved_paths: vec![],
                                        moved_places: vec![],
                                        active_loans: vec![],
                                        drop_flags: vec![],
                                        actions: vec![],
                                        protected_values: vec![],
                                    },
                                },
                            });
                            continue;
                        }
                        ControlTransfer::EnterHandler {
                            handler,
                            computation,
                            ..
                        } => {
                            for clause in self.handlers[handler.0 as usize].clauses.iter().rev() {
                                let (resume_type, continuation) = match &clause.contract {
                                    Some(contract) => (
                                        contract.parameter.clone(),
                                        if contract.invocation.lower >= 2
                                            && contract.invocation.upper
                                                == Some(contract.invocation.lower)
                                        {
                                            crate::MirContinuationPolicy::Replay {
                                                uses: u32::try_from(contract.invocation.lower)
                                                    .ok()?,
                                            }
                                        } else {
                                            crate::MirContinuationPolicy::Consume
                                        },
                                    ),
                                    None => (Type::Never, crate::MirContinuationPolicy::Terminal),
                                };
                                instructions.push(MirInstruction::InstallHandler {
                                    site: crate::MirHandlerSiteId::UNASSIGNED,
                                    effect: clause.effect.definition,
                                    effect_arguments: clause.effect.arguments.clone(),
                                    operation: clause.operation,
                                    payload_destinations: clause
                                        .payloads
                                        .iter()
                                        .copied()
                                        .map(local)
                                        .collect(),
                                    resume_type,
                                    continuation,
                                    target: MirBlockId(clause.entry.0),
                                });
                            }
                            Some(computation)
                        }
                        ControlTransfer::CompleteHandler {
                            handler,
                            value,
                            edge,
                        } => {
                            for _ in &self.handlers[handler.0 as usize].clauses {
                                instructions.push(MirInstruction::CompleteHandler {
                                    value: local(*value),
                                });
                                instructions.push(MirInstruction::UninstallHandler);
                            }
                            Some(edge)
                        }
                        ControlTransfer::FinishClause {
                            handler,
                            clause,
                            edge,
                            ..
                        } => {
                            let owner = &self.handlers[handler.0 as usize];
                            let selected = &owner.clauses[*clause as usize];
                            if matches!(
                                selected.resumption,
                                crate::CoreHandlerResumption::Discard { .. }
                                    | crate::CoreHandlerResumption::Terminal
                            ) || selected
                                .contract
                                .as_ref()
                                .is_some_and(|contract| contract.invocation.lower >= 2)
                            {
                                instructions.push(MirInstruction::Cancel {
                                    site: crate::MirResumptionSiteId::UNASSIGNED,
                                });
                            } else {
                                // A deep performance can re-enter this same
                                // clause while an older resumption call waits.
                                // Its clause result completes that delimiter,
                                // before the enclosing lexical suffix runs.
                                instructions.push(MirInstruction::CompleteHandler {
                                    value: local(match transfer {
                                        ControlTransfer::FinishClause { value, .. } => *value,
                                        _ => unreachable!(),
                                    }),
                                });
                                instructions.push(MirInstruction::UninstallHandler);
                            }
                            for _ in (*clause as usize + 1)..owner.clauses.len() {
                                instructions.push(MirInstruction::UninstallHandler);
                            }
                            Some(edge)
                        }
                        ControlTransfer::TailResume { value, .. } => {
                            instructions.push(MirInstruction::Resume {
                                site: crate::MirResumptionSiteId::UNASSIGNED,
                                value: local(*value),
                            });
                            None
                        }
                        ControlTransfer::Forward { .. } => {
                            instructions.push(MirInstruction::Forward {
                                site: crate::MirResumptionSiteId::UNASSIGNED,
                            });
                            None
                        }
                        ControlTransfer::Perform {
                            effect,
                            operation,
                            arguments,
                            result,
                            continuation,
                            ..
                        } => {
                            let arguments = arguments
                                .iter()
                                .zip(&block.terminator.operands)
                                .map(|(value, operand)| {
                                    let operand = *operand;
                                    emit_operand(
                                        operand,
                                        local(*value),
                                        &self.values[value.0 as usize].ty,
                                        &mut locals,
                                        &mut instructions,
                                    )
                                })
                                .collect::<Option<Vec<_>>>()?;
                            instructions.push(MirInstruction::Perform {
                                site: crate::MirPerformSiteId::UNASSIGNED,
                                dst: local(*result),
                                effect: effect.definition,
                                effect_arguments: effect.arguments.clone(),
                                operation: *operation,
                                arguments,
                            });
                            blocks.push(MirBlock {
                                scope: MirScopeId::ROOT,
                                parameters: block.parameters.iter().copied().map(local).collect(),
                                instructions,
                                terminator: match continuation {
                                    Some(target) => MirTerminator::Goto {
                                        target: MirBlockId(target.0),
                                        arguments: vec![local(*result)],
                                    },
                                    None => MirTerminator::Unreachable,
                                },
                            });
                            continue;
                        }
                    };
                    match edge {
                        Some(_) => MirTerminator::Goto {
                            target: routes[0].0,
                            arguments: routes[0].1.clone(),
                        },
                        None => MirTerminator::Unreachable,
                    }
                }
            };
            blocks.push(MirBlock {
                scope: MirScopeId::ROOT,
                parameters: block.parameters.iter().copied().map(local).collect(),
                instructions,
                terminator,
            });
        }
        blocks.extend(edge_blocks);
        // Legacy MIR's function ABI is separate from block parameters.
        blocks[self.entry.0 as usize].parameters.clear();
        for handler in &self.handlers {
            for clause in &handler.clauses {
                blocks[clause.entry.0 as usize].parameters.clear();
            }
        }
        let function = MirFunction {
            safety: self.safety,
            unsafe_execution: self.unsafe_execution,
            definition: self.definition,
            nominal_copy_descriptors,
            captures: capture_count,
            parameters: self.parameters.iter().copied().map(local).collect(),
            locals,
            result: declared_result,
            control: MirControlTables::default(),
            entry: MirBlockId(self.entry.0),
            blocks,
        };
        let bindings = self
            .source_bindings
            .iter()
            .map(|(origin, value)| (origin.clone(), local(*value)))
            .collect();
        Some((
            crate::MirLowering::freeze(function, &self.source_flow, &bindings),
            lifted,
        ))
    }
}
