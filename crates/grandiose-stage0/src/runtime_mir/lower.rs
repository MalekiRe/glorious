use super::*;
use crate::cleanup_mir::*;
use crate::control_mir::*;
use crate::ownership_mir::{
    OwnershipAggregate, OwnershipOperand, OwnershipSuccessor, ValueTransfer,
};
use crate::specialized_mir::{SpecializedCallTarget, SpecializedComputation};
use crate::{PrimitiveRole, ScalarType};

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
    instructions: &mut Vec<RuntimeOperation>,
) -> Option<MirLocal> {
    if operand.mode == ValueTransfer::Reborrow {
        return Some(source);
    }
    let dst = MirLocal(u32::try_from(locals.len()).ok()?);
    locals.push(MirLocalDecl {
        source: CoreId(u32::MAX),
        ty: ty.clone(),
    });
    instructions.push(if operand.mode == ValueTransfer::RetainResumption {
        RuntimeOperation::RetainResumption { dst, src: source, fields: vec![] }
    } else if operand.mode == ValueTransfer::Copy {
        RuntimeOperation::Copy { dst, src: source }
    } else {
        RuntimeOperation::Move { dst, src: source }
    });
    Some(dst)
}

// Concrete CFG arguments always move into their target registers. Honor an
// Ownership MIR copy by creating the independent outgoing owner first.
fn edge_arguments(
    edge: &OwnershipSuccessor,
    target: &CleanupBlock,
    values: &[ControlValueDecl],
    local: &impl Fn(ControlValue) -> MirLocal,
    locals: &mut Vec<MirLocalDecl>,
    instructions: &mut Vec<RuntimeOperation>,
) -> Option<Vec<MirLocal>> {
    edge.arguments
        .iter()
        .zip(&target.parameters)
        .map(|(operand, parameter)| {
            let source = local(operand.value);
            if !matches!(operand.mode, ValueTransfer::Copy | ValueTransfer::RetainResumption) || source == local(*parameter) {
                return Some(source);
            }
            let destination = MirLocal(u32::try_from(locals.len()).ok()?);
            locals.push(MirLocalDecl {
                source: CoreId(u32::MAX),
                ty: values[operand.value.0 as usize].ty.clone(),
            });
            instructions.push(if operand.mode == ValueTransfer::RetainResumption {
                RuntimeOperation::RetainResumption { dst: destination, src: source, fields: vec![] }
            } else { RuntimeOperation::Copy { dst: destination, src: source } });
            Some(destination)
        })
        .collect()
}

impl CleanupMir {
    /// No type substitution, trait selection, or call-target discovery occurs here.
    pub(crate) fn lower_runtime_values(
        &self,
        declared_result: Type,
        capture_count: u32,
        primitives: Option<&BTreeMap<DefKey, PrimitiveRole>>,
        signatures: Option<&crate::ElaboratedInterface>,
    ) -> Option<(RuntimeMir, BTreeMap<DefKey, RuntimeMir>)> {
        if !plain(&declared_result)
            || self
                .parameters
                .iter()
                .any(|value| !plain(&self.values[value.0 as usize].ty))
        {
            return None;
        }
        let aliases = self
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter_map(|instruction| match instruction.operation {
                CleanupOperation::Read(value) => Some((instruction.destination, value)),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let unused_optional_resumptions = self.unused_optional_resumptions();
        let symbols = &self.symbols;
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
        let mut nominal_copy_descriptors = self
            .layouts
            .iter()
            .filter_map(|layout| {
                let Type::Nominal {
                    definition,
                    arguments,
                } = &layout.ty
                else {
                    return None;
                };
                Some(crate::MirNominalCopyDescriptor {
                    definition: *definition,
                    arguments: arguments.clone(),
                    source_contract: layout.source_contract,
                    is_enum: layout.is_enum,
                    variants: layout.variants.clone(),
                })
            })
            .collect::<Vec<_>>();
        let mut building_nominal_copy_descriptors = vec![];
        let mut diagnostics = vec![];
        let local = |mut value: ControlValue| {
            for _ in 0..aliases.len() {
                let Some(source) = aliases.get(&value) else {
                    break;
                };
                value = *source;
            }
            MirLocal(value.0)
        };
        let mut pending = vec![];
        let mut blocks = vec![];
        let mut edge_blocks = vec![];
        let mut label_landings = BTreeMap::new();
        for id in self.blocks.iter().flat_map(|block| &block.instructions).filter_map(|instruction| {
            match instruction.operation {
                CleanupOperation::Compute(SpecializedComputation::Label(label)) => Some(label),
                _ => None,
            }
        }).collect::<std::collections::BTreeSet<_>>() {
            let label = &self.labels[id.0 as usize];
            let landing = MirBlockId(u32::try_from(self.blocks.len() + edge_blocks.len()).ok()?);
            self.record_runtime_plan(self.label_cleanup[id.0 as usize], landing.0 as usize, 0, &local, &mut pending);
            edge_blocks.push(RuntimeBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![local(label.result)],
                instructions: vec![],
                terminator: RuntimeTerminator::Goto {
                    target: MirBlockId(label.target.0),
                    arguments: vec![local(label.result)],
                },
            });
            label_landings.insert(id, landing);
        }
        let mut lifted = BTreeMap::new();
        let mut leave_handler_prefixes = BTreeMap::new();
        // Preserve the source handler identity through its clause expansion.
        // Freezing remaps these builder identities together with the leaves.
        let mut next_handler_site = 0u32;
        let handler_storage = (0..self.handlers.len()).map(|index|
            self.handler_storage_roots(ControlHandlerId(index as u32))).collect::<Vec<_>>();
        let handler_sites = self.handlers.iter().map(|handler| {
            handler.clauses.iter().map(|_| {
                let site = crate::MirHandlerSiteId(next_handler_site);
                next_handler_site += 1;
                site
            }).collect::<Vec<_>>()
        }).collect::<Vec<_>>();
        for (block_index, block) in self.blocks.iter().enumerate() {
            let mut instructions = vec![];
            for clause in self.handlers.iter().flat_map(|handler| &handler.clauses) {
                if clause.accepted.0 as usize == block_index {
                    instructions.push(RuntimeOperation::ClaimEffectPayloads {
                        payloads: clause.payloads.iter().copied().map(local).collect(),
                    });
                }
            }
            for instruction in &block.instructions {
                let dst = local(instruction.destination);
                let ty = &self.values[instruction.destination.0 as usize].ty;
                let operation = match &instruction.operation {
                    CleanupOperation::Construct { aggregate, fields } => {
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
                                RuntimeOperation::ConstUnit { dst }
                            }
                            OwnershipAggregate::Tuple => {
                                RuntimeOperation::MakeTuple { dst, fields }
                            }
                            OwnershipAggregate::Array => RuntimeOperation::MakeArray {
                                dst,
                                fields,
                                element_type: match ty {
                                    Type::Array(element) | Type::FixedArray { element, .. } => (**element).clone(),
                                    _ => return None,
                                },
                            },
                            OwnershipAggregate::Record(definition) => {
                                RuntimeOperation::MakeRecord {
                                    dst,
                                    definition: *definition,
                                    fields,
                                    field_types,
                                }
                            }
                            OwnershipAggregate::Enum {
                                definition,
                                variant,
                            } => RuntimeOperation::MakeEnum {
                                dst,
                                definition: *definition,
                                variant: *variant,
                                fields,
                                field_types,
                            },
                        }
                    }
                    CleanupOperation::Destroy(plan) => {
                        self.record_runtime_plan(
                            *plan,
                            block_index,
                            instructions.len(),
                            &local,
                            &mut pending,
                        );
                        RuntimeOperation::ConstUnit { dst }
                    }
                    CleanupOperation::Read(_) => continue,
                    CleanupOperation::Transfer { .. }
                        if symbols.contains(&instruction.destination) =>
                    {
                        continue;
                    }
                    CleanupOperation::Transfer { value, mode } => {
                        if *mode == ValueTransfer::RetainResumption {
                            RuntimeOperation::RetainResumption { dst, src: local(*value), fields: vec![] }
                        } else if *mode == ValueTransfer::Move {
                            RuntimeOperation::Move {
                                dst,
                                src: local(*value),
                            }
                        } else {
                            RuntimeOperation::Copy {
                                dst,
                                src: local(*value),
                            }
                        }
                    }
                    CleanupOperation::RunCleanup {
                        result, mode, plan, ..
                    } => {
                        if !symbols.contains(&instruction.destination) {
                            instructions.push(if *mode == ValueTransfer::RetainResumption {
                                RuntimeOperation::RetainResumption { dst, src: local(*result), fields: vec![] }
                            } else if *mode == ValueTransfer::Move {
                                RuntimeOperation::Move {
                                    dst,
                                    src: local(*result),
                                }
                            } else {
                                RuntimeOperation::Copy {
                                    dst,
                                    src: local(*result),
                                }
                            });
                        }
                        self.record_runtime_plan(
                            *plan,
                            block_index,
                            instructions.len(),
                            &local,
                            &mut pending,
                        );
                        continue;
                    }
                    CleanupOperation::Borrow(loan) => {
                        let loan = &self.loans[loan.0 as usize];
                        let (root, fields, reborrow) = place_path(&loan.place);
                        RuntimeOperation::Borrow {
                            dst,
                            src: local(root),
                            fields,
                            unique: loan.unique,
                            reborrow,
                        }
                    }
                    CleanupOperation::ReadReference(reference) => RuntimeOperation::DerefCopy {
                        dst,
                        reference: local(*reference),
                    },
                    CleanupOperation::PrepareInvocation(place) => {
                        if self.symbols.contains(&instruction.destination) { continue; }
                        let (root, fields, reborrow) = place_path(place);
                        RuntimeOperation::PrepareInvocation { dst, src: local(root), fields, reborrow }
                    }
                    CleanupOperation::ReadPlace { place, mode } => {
                        let (root, fields, reborrow) = place_path(place);
                        if *mode == ValueTransfer::RetainResumption {
                            if reborrow { return None; }
                            RuntimeOperation::RetainResumption { dst, src: local(root), fields }
                        } else if fields.is_empty() && !reborrow {
                            if *mode == ValueTransfer::Move {
                                RuntimeOperation::Move {
                                    dst,
                                    src: local(root),
                                }
                            } else {
                                RuntimeOperation::Copy {
                                    dst,
                                    src: local(root),
                                }
                            }
                        } else if !reborrow && *mode == ValueTransfer::Move {
                            RuntimeOperation::TakeProjection {
                                dst,
                                base: local(root),
                                fields,
                            }
                        } else if reborrow && fields.is_empty() {
                            if *mode == ValueTransfer::Move {
                                RuntimeOperation::DerefMove {
                                    dst,
                                    reference: local(root),
                                }
                            } else {
                                RuntimeOperation::DerefCopy {
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
                            instructions.push(RuntimeOperation::Borrow {
                                dst: reference,
                                src: local(root),
                                fields,
                                unique: *mode == ValueTransfer::Move,
                                reborrow,
                            });
                            if *mode == ValueTransfer::Move {
                                RuntimeOperation::DerefMove { dst, reference }
                            } else {
                                RuntimeOperation::DerefCopy { dst, reference }
                            }
                        }
                    }
                    CleanupOperation::Project {
                        place,
                        base,
                        index,
                        field_count,
                        mode,
                    } => {
                        let (root, fields, reborrow) = place_path(place);
                        if *mode == ValueTransfer::RetainResumption {
                            if reborrow { return None; }
                            RuntimeOperation::RetainResumption { dst, src: local(root), fields }
                        } else if *mode == ValueTransfer::Move && !reborrow {
                            RuntimeOperation::TakeProjection {
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
                            instructions.push(RuntimeOperation::Borrow {
                                dst: reference,
                                src: local(root),
                                fields,
                                unique: *mode == ValueTransfer::Move,
                                reborrow: true,
                            });
                            if *mode == ValueTransfer::Move {
                                RuntimeOperation::DerefMove { dst, reference }
                            } else {
                                RuntimeOperation::DerefCopy { dst, reference }
                            }
                        } else {
                            match &self.values[base.0 as usize].ty {
                                Type::Tuple(_) => RuntimeOperation::ProjectTuple {
                                    dst,
                                    base: local(*base),
                                    index: *index,
                                    field_count: *field_count,
                                    field_type: ty.clone(),
                                },
                                Type::Array(_) | Type::FixedArray { .. } => RuntimeOperation::ProjectArray {
                                    dst,
                                    base: local(*base),
                                    index: *index,
                                    field_count: *field_count,
                                    element_type: ty.clone(),
                                },
                                _ => RuntimeOperation::ProjectRecord {
                                    dst,
                                    base: local(*base),
                                    index: *index,
                                    field_count: *field_count,
                                    field_type: ty.clone(),
                                },
                            }
                        }
                    }
                    CleanupOperation::MovePlace(place) => {
                        let (root, fields, reborrow) = place_path(place);
                        if reborrow && fields.is_empty() {
                            RuntimeOperation::DerefMove {
                                dst,
                                reference: local(root),
                            }
                        } else if !reborrow && fields.is_empty() {
                            RuntimeOperation::Move {
                                dst,
                                src: local(root),
                            }
                        } else if !reborrow {
                            RuntimeOperation::TakeProjection {
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
                            instructions.push(RuntimeOperation::Borrow {
                                dst: reference,
                                src: local(root),
                                fields,
                                unique: true,
                                reborrow: true,
                            });
                            RuntimeOperation::DerefMove { dst, reference }
                        }
                    }
                    CleanupOperation::Replace {
                        place,
                        value,
                        mode,
                        cleanup,
                    } => {
                        let replacement = if *mode == ValueTransfer::Copy {
                            let replacement = MirLocal(u32::try_from(locals.len()).ok()?);
                            locals.push(MirLocalDecl {
                                source: CoreId(u32::MAX),
                                ty: self.values[value.0 as usize].ty.clone(),
                            });
                            instructions.push(RuntimeOperation::Copy {
                                dst: replacement,
                                src: local(*value),
                            });
                            replacement
                        } else {
                            emit_operand(
                                OwnershipOperand {
                                    value: *value,
                                    mode: *mode,
                                },
                                local(*value),
                                &self.values[value.0 as usize].ty,
                                &mut locals,
                                &mut instructions,
                            )?
                        };
                        self.record_runtime_plan(
                            *cleanup,
                            block_index,
                            instructions.len(),
                            &local,
                            &mut pending,
                        );
                        let (root, fields, reborrow) = place_path(place);
                        if fields.is_empty() {
                            instructions.push(if reborrow {
                                RuntimeOperation::DerefStore {
                                    reference: local(root),
                                    src: replacement,
                                }
                            } else {
                                RuntimeOperation::Store {
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
                            instructions.push(RuntimeOperation::Borrow {
                                dst: reference,
                                src: local(root),
                                fields,
                                unique: true,
                                reborrow,
                            });
                            instructions.push(RuntimeOperation::DerefStore {
                                reference,
                                src: replacement,
                            });
                        }
                        RuntimeOperation::ConstUnit { dst }
                    }
                    CleanupOperation::Capture { closure, captures } => {
                        let closure = &self.closures[closure.0 as usize];
                        let Type::Callable { .. } = ty else {
                            return None;
                        };
                        let callee = closure.body.definition;
                        if let std::collections::btree_map::Entry::Vacant(entry) =
                            lifted.entry(callee)
                        {
                            let (function, nested) = closure.body.lower_runtime_values(
                                closure.body.result.clone(),
                                u32::try_from(captures.len()).ok()?,
                                primitives,
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
                                        RuntimeOperation::Move {
                                            dst: destination,
                                            src: source,
                                        }
                                    } else {
                                        RuntimeOperation::Copy {
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
                        RuntimeOperation::MakeCallable {
                            dst,
                            callee,
                            captures: captured,
                            environment: Some(crate::MirCaptureEnvironment {
                                brand: closure.environment.brand,
                                destructor: closure.destructor,
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
                    CleanupOperation::Compute(_) if symbols.contains(&instruction.destination) => {
                        continue;
                    }
                    CleanupOperation::Compute(computation) => match computation {
                        SpecializedComputation::Unit => RuntimeOperation::ConstUnit { dst },
                        SpecializedComputation::Function {
                            definition,
                            arguments,
                        } => {
                            if primitives
                                .is_some_and(|primitives| primitives.contains_key(definition))
                            {
                                continue;
                            }
                            if !arguments.is_empty() {
                                return None;
                            }
                            RuntimeOperation::MakeCallable {
                                dst,
                                callee: *definition,
                                captures: vec![],
                                environment: None,
                            }
                        }
                        SpecializedComputation::Literal(text) => match ty {
                            Type::Unit => RuntimeOperation::ConstUnit { dst },
                            Type::Scalar(ScalarType::Bool)
                                if matches!(text.as_str(), "true" | "false") =>
                            {
                                RuntimeOperation::ConstBool {
                                    dst,
                                    value: text == "true",
                                }
                            }
                            Type::Scalar(ScalarType::Char) => RuntimeOperation::ConstChar {
                                dst,
                                value: crate::mir::parse_char_literal(text).ok()?,
                            },
                            Type::Scalar(ScalarType::Text) => RuntimeOperation::ConstText {
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
                                RuntimeOperation::ConstStaticData {
                                    dst,
                                    tag: *tag,
                                    alignment: *alignment,
                                    bytes,
                                }
                            }
                            Type::Scalar(scalar) => RuntimeOperation::from_atomic(
                                crate::mir::materialize_numeric_literal(dst, text, *scalar).ok()?,
                            )
                            .ok()?,
                            _ => return None,
                        },
                        SpecializedComputation::Intrinsic {
                            operator,
                            arguments,
                        } => {
                            let mut atomic_instructions = vec![];
                            crate::mir::atomic::AtomicEmitter {
                                locals: &mut locals,
                                instructions: &mut atomic_instructions,
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
                            instructions.extend(
                                atomic_instructions
                                    .into_iter()
                                    .map(RuntimeOperation::from_atomic)
                                    .collect::<Result<Vec<_>, _>>()
                                    .ok()?,
                            );
                            continue;
                        }
                        SpecializedComputation::Test { subject, pattern } => {
                            RuntimeOperation::PatternTest {
                                dst,
                                subject: local(*subject),
                                pattern: crate::mir::lower_pattern(pattern.clone())?,
                            }
                        }
                        SpecializedComputation::Label(label) => {
                            let landing = *label_landings.get(label)?;
                            let label = &self.labels[label.0 as usize];
                            RuntimeOperation::MakeLabel {
                                label: crate::MirLabelId::UNASSIGNED,
                                dst,
                                brand: label.brand,
                                target: landing,
                                destination: local(label.result),
                            }
                        }
                        SpecializedComputation::Resumption { .. } => {
                            RuntimeOperation::CaptureResumption {
                                site: crate::MirResumptionSiteId::UNASSIGNED,
                                dst,
                            }
                        }
                        SpecializedComputation::HostFunction { .. } => continue,
                        SpecializedComputation::Constant { definition } => RuntimeOperation::Call {
                            dst,
                            callee: *definition,
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
                if matches!(block.terminator.control, CleanupControl::SwitchBool { .. })
                    && !copies.is_empty()
                {
                    // Copies belong to the selected edge, not to both sides
                    // of a branch. The temporary owner is moved at its exit.
                    let bridge =
                        MirBlockId(u32::try_from(self.blocks.len() + edge_blocks.len()).ok()?);
                    edge_blocks.push(RuntimeBlock {
                        scope: MirScopeId::ROOT,
                        parameters: vec![],
                        instructions: copies,
                        terminator: RuntimeTerminator::Goto {
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
            let returned = if let CleanupControl::Return(value) = block.terminator.control {
                if matches!(block.terminator.operands[0].mode, ValueTransfer::Copy | ValueTransfer::RetainResumption) {
                    let destination = MirLocal(u32::try_from(locals.len()).ok()?);
                    locals.push(MirLocalDecl {
                        source: CoreId(u32::MAX),
                        ty: self.values[value.0 as usize].ty.clone(),
                    });
                    instructions.push(if block.terminator.operands[0].mode == ValueTransfer::RetainResumption {
                        RuntimeOperation::RetainResumption { dst: destination, src: local(value), fields: vec![] }
                    } else { RuntimeOperation::Copy { dst: destination, src: local(value) } });
                    Some(destination)
                } else {
                    Some(local(value))
                }
            } else {
                None
            };
            // Copies must also be protected BEFORE ending the activation.
            // Their source owners still need their own destruction; the new
            // carriers do not belong to the ending source-storage inventory.
            let prepared_tail = if let CleanupControl::Invoke { arguments, contract, .. } = &block.terminator.control
                && contract.mandatory_tail {
                Some(arguments.iter().zip(block.terminator.operands.iter().skip(1))
                    .map(|(value, operand)| emit_operand(*operand, local(*value),
                        &self.values[value.0 as usize].ty, &mut locals, &mut instructions))
                    .collect::<Option<Vec<_>>>()?)
            } else { None };
            self.record_runtime_plan(
                block.terminator.cleanup,
                block_index,
                instructions.len(),
                &local,
                &mut pending,
            );
            let terminator = match &block.terminator.control {
                CleanupControl::Goto(_) => RuntimeTerminator::Goto {
                    target: routes[0].0,
                    arguments: routes[0].1.clone(),
                },
                CleanupControl::SwitchBool { condition, .. } => RuntimeTerminator::SwitchBool {
                    condition: local(*condition),
                    then_target: routes[0].0,
                    then_arguments: routes[0].1.clone(),
                    else_target: routes[1].0,
                    else_arguments: routes[1].1.clone(),
                },
                CleanupControl::Invoke {
                    callee,
                    target,
                    arguments,
                    result,
                    continuation,
                    contract,
                } => {
                    if let Some(arguments) = &prepared_tail
                        && let SpecializedCallTarget::Direct(callee) = target {
                        blocks.push(RuntimeBlock {
                            scope: MirScopeId::ROOT,
                            parameters: block.parameters.iter().copied().map(local).collect(),
                            instructions,
                            terminator: RuntimeTerminator::TailCall { callee: *callee, arguments: arguments.clone() },
                        });
                        continue;
                    }
                    // Manifest machine leaves inline after the same protected
                    // cleanup boundary, so they need no activation at all.
                    if contract.mandatory_tail && !matches!(target, SpecializedCallTarget::Primitive { .. }) {
                        return None;
                    }
                    let arguments = if let Some(arguments) = prepared_tail { arguments } else { arguments
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
                        .collect::<Option<Vec<_>>>()? };
                    match target {
                        SpecializedCallTarget::Resumption { .. } => {
                            if arguments.len() != 1 {
                                return None;
                            }
                            instructions.push(if contract.prepared_receiver { RuntimeOperation::CallPrepared {
                                dst: local(*result), callee: local(*callee), arguments,
                            } } else { RuntimeOperation::CallIndirect {
                                dst: local(*result),
                                callee: local(*callee),
                                arguments,
                            } });
                        }
                        SpecializedCallTarget::Indirect => {
                            instructions.push(if contract.prepared_receiver { RuntimeOperation::CallPrepared {
                                dst: local(*result), callee: local(*callee), arguments,
                            } } else { RuntimeOperation::CallIndirect {
                                dst: local(*result),
                                callee: local(*callee),
                                arguments,
                            } })
                        }
                        target => {
                            let (definition, generic_arguments, host_import) = match target {
                                SpecializedCallTarget::Direct(definition) => {
                                    (*definition, vec![], None)
                                }
                                SpecializedCallTarget::Primitive {
                                    definition,
                                    arguments,
                                } => (*definition, arguments.clone(), None),
                                SpecializedCallTarget::Host {
                                    definition,
                                    arguments,
                                    import,
                                } => (*definition, arguments.clone(), Some(import.clone())),
                                _ => unreachable!(),
                            };
                            let mut atomic_instructions = vec![];
                            crate::mir::atomic::AtomicEmitter {
                                locals: &mut locals,
                                instructions: &mut atomic_instructions,
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
                                definition,
                                generic_arguments,
                                host_import,
                                arguments,
                            )?;
                            instructions.extend(
                                atomic_instructions
                                    .into_iter()
                                    .map(RuntimeOperation::from_atomic)
                                    .collect::<Result<Vec<_>, _>>()
                                    .ok()?,
                            );
                            if let Some(operations) = self
                                .native_operations
                                .get(&ControlBlockId(block_index as u32))
                            {
                                let Some(RuntimeOperation::HostCall {
                                    resident_operations,
                                    ..
                                }) = instructions.last_mut()
                                else {
                                    return None;
                                };
                                *resident_operations = operations.clone();
                            }
                        }
                    }
                    if contract.mandatory_tail {
                        RuntimeTerminator::Return { value: local(*result) }
                    } else { match continuation {
                        Some(target) => RuntimeTerminator::Goto {
                            target: MirBlockId(target.0),
                            arguments: vec![local(*result)],
                        },
                        None => RuntimeTerminator::Unreachable,
                    } }
                }
                CleanupControl::Return(_) => RuntimeTerminator::Return { value: returned? },
                CleanupControl::Unreachable => RuntimeTerminator::Unreachable,
                CleanupControl::Transfer(transfer) => {
                    let edge = match transfer {
                        ControlTransfer::Leave { label, .. } => {
                            let target = label_landings.get(label).copied().unwrap_or(routes[0].0);
                            let label = &self.labels[label.0 as usize];
                            leave_handler_prefixes.insert(MirBlockId(block_index as u32),
                                label.handler_prefix.iter().map(|(handler, clause)|
                                    handler_sites[handler.0 as usize][*clause as usize]).collect());
                            blocks.push(RuntimeBlock {
                                scope: MirScopeId::ROOT,
                                parameters: block.parameters.iter().copied().map(local).collect(),
                                instructions,
                                terminator: RuntimeTerminator::Leave {
                                    label: crate::MirLabelId::UNASSIGNED,
                                    brand: label.brand,
                                    target,
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
                            for (clause_index, clause) in self.handlers[handler.0 as usize].clauses.iter().enumerate().rev() {
                                let (resume_type, continuation) = match &clause.contract {
                                    Some(contract) => (
                                        contract.parameter.clone(),
                                        crate::MirContinuationPolicy::from_quantity(contract.invocation)?,
                                    ),
                                    None => (Type::Never, crate::MirContinuationPolicy::Terminal),
                                };
                                instructions.push(RuntimeOperation::InstallHandler {
                                    site: handler_sites[handler.0 as usize][clause_index],
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
                                    continuation_owned: handler_storage[handler.0 as usize].continuation.iter().copied().map(local)
                                        .collect::<BTreeSet<_>>().into_iter().collect(),
                                    clause_owned: handler_storage[handler.0 as usize].clauses[clause_index].iter().copied().map(local)
                                        .collect::<BTreeSet<_>>().into_iter().collect(),
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
                                instructions.push(RuntimeOperation::CompleteHandler {
                                    value: local(*value),
                                });
                                instructions.push(RuntimeOperation::UninstallHandler);
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
                            ) || unused_optional_resumptions.contains(&(*handler, *clause))
                                || selected
                                .contract
                                .as_ref()
                                .is_some_and(|contract| contract.invocation.lower >= 2)
                            {
                                instructions.push(RuntimeOperation::Cancel {
                                    site: crate::MirResumptionSiteId::UNASSIGNED,
                                });
                                // Cancel first unwinds retained deeper frames.
                                // Then dispose of protected locals in this
                                // surviving frame before the clause rejoins.
                                self.record_runtime_plan(
                                    *self.clause_cleanup.get(&ControlBlockId(block_index as u32))?,
                                    block_index, instructions.len(), &local, &mut pending,
                                );
                            } else {
                                // A deep performance can re-enter this same
                                // clause while an older resumption call waits.
                                // Its clause result completes that delimiter,
                                // before the enclosing lexical suffix runs.
                                instructions.push(RuntimeOperation::CompleteHandler {
                                    value: local(match transfer {
                                        ControlTransfer::FinishClause { value, .. } => *value,
                                        _ => unreachable!(),
                                    }),
                                });
                                instructions.push(RuntimeOperation::UninstallHandler);
                            }
                            for _ in (*clause as usize + 1)..owner.clauses.len() {
                                instructions.push(RuntimeOperation::UninstallHandler);
                            }
                            Some(edge)
                        }
                        ControlTransfer::TailResume { value, .. } => {
                            instructions.push(RuntimeOperation::Resume {
                                site: crate::MirResumptionSiteId::UNASSIGNED,
                                value: local(*value),
                            });
                            None
                        }
                        ControlTransfer::Forward { .. } => {
                            instructions.push(RuntimeOperation::Forward {
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
                            instructions.push(RuntimeOperation::Perform {
                                site: crate::MirPerformSiteId::UNASSIGNED,
                                dst: local(*result),
                                effect: effect.definition,
                                effect_arguments: effect.arguments.clone(),
                                operation: *operation,
                                arguments,
                            });
                            blocks.push(RuntimeBlock {
                                scope: MirScopeId::ROOT,
                                parameters: block.parameters.iter().copied().map(local).collect(),
                                instructions,
                                terminator: match continuation {
                                    Some(target) => RuntimeTerminator::Goto {
                                        target: MirBlockId(target.0),
                                        arguments: vec![local(*result)],
                                    },
                                    None => RuntimeTerminator::Unreachable,
                                },
                            });
                            continue;
                        }
                    };
                    match edge {
                        Some(_) => RuntimeTerminator::Goto {
                            target: routes[0].0,
                            arguments: routes[0].1.clone(),
                        },
                        None => RuntimeTerminator::Unreachable,
                    }
                }
            };
            blocks.push(RuntimeBlock {
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
        let function = RuntimeMir {
            safety: self.safety,
            unsafe_execution: self.unsafe_execution,
            definition: self.definition,
            nominal_copy_descriptors,
            captures: capture_count,
            parameters: self.parameters.iter().copied().map(local).collect(),
            locals,
            result: declared_result,
            control: MirControlTables { leave_handler_prefixes, ..MirControlTables::default() },
            frame: RuntimeFrame::default(),
            entry: MirBlockId(self.entry.0),
            blocks,
        };
        let bindings = self
            .source_bindings
            .iter()
            .map(|(origin, value)| (origin.clone(), local(*value)))
            .collect();
        // Site offsets refer to this instruction stream. Storage freezing
        // inserts lifecycle instructions, so expand selected sites first.
        let mut function = function;
        destruction::expand(&mut function, pending, &self.destruction).ok()?;
        let mut function = function
            .with_frozen_move_paths(&self.source_flow)
            .with_frozen_source_storage_bindings(&self.source_flow, &bindings)
            .with_frozen_control_tables();
        function.control.cleanup_owners = Some(
            self.plans[self.frame_cleanup.0 as usize]
                .actions
                .iter()
                .filter_map(|action| {
                    let CleanupAction::StorageDead(flag) = action else {
                        return None;
                    };
                    Some(local(self.flags[flag.0 as usize].place.root()))
                })
                .collect(),
        );
        function.control.frame_cleanup = self.plans[self.frame_cleanup.0 as usize]
            .actions
            .iter()
            .filter_map(|action| {
                let CleanupAction::Destroy { flag, destructor } = action else {
                    return None;
                };
                Some(crate::mir::MirFrameDrop {
                    owner: local(self.flags[flag.0 as usize].place.root()),
                    destructor: *destructor,
                })
            })
            .collect();
        destruction::expand(&mut function, vec![], &self.destruction).ok()?;
        Some((function, lifted))
    }
}
