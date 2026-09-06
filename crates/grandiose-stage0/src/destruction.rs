//! Concrete, source-type-directed destruction. Selection and traversal belong
//! to the compiler: executable glue consists of ordinary MIR calls and CFGs.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    CoreId, DefKey, Digest, ElaboratedHeader, ElaboratedInterface, ElaboratedNominalLayout,
    ElaboratedTraitReference, GenericArgument, GenericKind, InstanceKey, MirBlock, MirBlockId,
    MirControlTables, MirFunction, MirInstruction, MirLocal, MirLocalDecl, MirPattern, MirScopeId,
    MirTerminator, Mutability, Safety, ScalarType, TraitAnswer, TraitGoal, TraitSolver, Type,
};

fn glue_definition() -> DefKey {
    DefKey(Digest::of_bytes(b"grandiose-owned-destruction-glue-v1"))
}

pub(crate) fn is_glue(key: &InstanceKey) -> bool {
    key.callable == glue_definition()
}

#[derive(Clone)]
struct Field {
    ty: Type,
    glue: Option<InstanceKey>,
}

#[derive(Clone)]
enum Shape {
    Leaf,
    Tuple(Vec<Field>),
    Nominal {
        definition: DefKey,
        is_enum: bool,
        variants: Vec<Vec<Field>>,
    },
    Array {
        element: Type,
        glue: InstanceKey,
    },
}

#[derive(Clone)]
struct Plan {
    ty: Type,
    hook: Option<InstanceKey>,
    shape: Shape,
}

pub(crate) struct Planner<'a> {
    signatures: &'a ElaboratedInterface,
    solver: TraitSolver,
    plans: BTreeMap<InstanceKey, Plan>,
    trivial: BTreeSet<InstanceKey>,
    active: BTreeSet<InstanceKey>,
}

impl<'a> Planner<'a> {
    pub(crate) fn new(signatures: &'a ElaboratedInterface) -> Self {
        Self {
            signatures,
            solver: TraitSolver::new(signatures),
            plans: BTreeMap::new(),
            trivial: BTreeSet::new(),
            active: BTreeSet::new(),
        }
    }

    /// Open source templates have no executable destruction identity yet.
    /// They are visited again under the caller's concrete substitution.
    pub(crate) fn discover(&mut self, ty: &Type) -> Result<Option<InstanceKey>, String> {
        let key = match InstanceKey::new(
            glue_definition(),
            &[GenericKind::Type],
            vec![GenericArgument::Type(ty.clone())],
        ) {
            Ok(key) => key,
            Err(
                crate::InstanceKeyError::NonConcreteType { .. }
                | crate::InstanceKeyError::UnresolvedType { .. }
                | crate::InstanceKeyError::OpenEffectRow { .. }
                | crate::InstanceKeyError::NonConcreteLifetime { .. }
                | crate::InstanceKeyError::NonConcreteConst { .. },
            ) => return Ok(None),
            Err(error) => return Err(format!("invalid destruction instance: {error:?}")),
        };
        if self.trivial.contains(&key) {
            return Ok(None);
        }
        if self.plans.contains_key(&key) {
            return Ok(Some(key));
        }
        if !self.active.insert(key.clone()) {
            return Err("destruction encountered a recursive by-value layout".into());
        }
        let hook = match self.solver.solve(TraitGoal {
            relation: ElaboratedTraitReference {
                definition: crate::resolution::language_drop_trait_definition(),
                arguments: vec![],
            },
            subject: ty.clone(),
        }) {
            TraitAnswer::Proven { evidence } => {
                let Some(ElaboratedHeader::Implementation(implementation)) =
                    self.signatures.definitions.get(&evidence)
                else {
                    return Err("Drop evidence does not identify a source implementation".into());
                };
                if !implementation.methods.contains_key("drop") {
                    return Err("Drop implementation has no destructor method".into());
                }
                Some(
                    crate::service::trait_method_instance_key(
                        evidence,
                        crate::implementation_method_key(evidence, "drop"),
                        &[],
                        &[],
                        Some(ty),
                    )
                    .map_err(|error| format!("Drop method is not concrete: {error:?}"))?,
                )
            }
            TraitAnswer::NoSolution | TraitAnswer::Refuted { .. } => None,
            TraitAnswer::Ambiguous => return Err("concrete Drop selection is ambiguous".into()),
            TraitAnswer::Overflow => {
                return Err("concrete Drop selection exceeded its solver budget".into());
            }
        };
        let shape = match ty {
            Type::Tuple(fields) => Shape::Tuple(self.fields(fields)?),
            Type::Nominal {
                definition,
                arguments,
            } => match self.signatures.definitions.get(definition) {
                Some(ElaboratedHeader::Nominal { layout, .. }) => {
                    let is_enum = matches!(layout, ElaboratedNominalLayout::Enum(_));
                    match crate::mir::instantiate_nominal_copy_layout(layout, arguments) {
                        Some(variants) => Shape::Nominal {
                            definition: *definition,
                            is_enum,
                            variants: variants
                                .iter()
                                .map(|fields| self.fields(fields))
                                .collect::<Result<_, _>>()?,
                        },
                        None => Shape::Leaf,
                    }
                }
                _ => return Err("destruction nominal has no declaration-owned layout".into()),
            },
            Type::Array(element) => match self.discover(element)? {
                Some(glue) => Shape::Array {
                    element: (**element).clone(),
                    glue,
                },
                None => Shape::Leaf,
            },
            // References/raw pointers do not own their referents. Callable
            // environments require their separate sealed capture descriptor,
            // never traversal of the callable's argument or result types.
            _ => Shape::Leaf,
        };
        let has_fields = match &shape {
            Shape::Tuple(fields) => fields.iter().any(|field| field.glue.is_some()),
            Shape::Nominal { variants, .. } => {
                variants.iter().flatten().any(|field| field.glue.is_some())
            }
            Shape::Array { .. } => true,
            Shape::Leaf => false,
        };
        self.active.remove(&key);
        if hook.is_none() && !has_fields {
            self.trivial.insert(key);
            return Ok(None);
        }
        self.plans.insert(
            key.clone(),
            Plan {
                ty: ty.clone(),
                hook,
                shape,
            },
        );
        Ok(Some(key))
    }

    fn fields(&mut self, types: &[Type]) -> Result<Vec<Field>, String> {
        types
            .iter()
            .map(|ty| {
                Ok(Field {
                    ty: ty.clone(),
                    glue: self.discover(ty)?,
                })
            })
            .collect()
    }

    pub(crate) fn callees(&self, key: &InstanceKey) -> Result<Vec<InstanceKey>, String> {
        let plan = self
            .plans
            .get(key)
            .ok_or("missing discovered destruction plan")?;
        let mut callees = plan.hook.iter().cloned().collect::<Vec<_>>();
        match &plan.shape {
            Shape::Tuple(fields) => {
                callees.extend(fields.iter().filter_map(|field| field.glue.clone()))
            }
            Shape::Nominal { variants, .. } => callees.extend(
                variants
                    .iter()
                    .flatten()
                    .filter_map(|field| field.glue.clone()),
            ),
            Shape::Array { glue, .. } => callees.push(glue.clone()),
            Shape::Leaf => {}
        }
        Ok(callees)
    }

    pub(crate) fn materialize(&self, key: &InstanceKey) -> Result<MirFunction, String> {
        let plan = self
            .plans
            .get(key)
            .ok_or("missing materialized destruction plan")?;
        let mut builder = Builder::new(DefKey(key.fingerprint()), plan.ty.clone());
        if let Some(hook) = &plan.hook {
            let reference = builder.local(Type::Reference {
                mutability: Mutability::Unique,
                lifetime: crate::Lifetime::Elided,
                referent: Box::new(plan.ty.clone()),
            });
            builder.emit(MirInstruction::Borrow {
                dst: reference,
                src: MirLocal(0),
                fields: vec![],
                unique: true,
                reborrow: false,
            });
            builder.call(hook, reference);
        }
        match &plan.shape {
            Shape::Tuple(fields) => builder.fields(fields),
            Shape::Nominal {
                definition,
                is_enum: false,
                variants,
            } => {
                let _ = definition;
                builder.fields(&variants[0]);
            }
            Shape::Nominal {
                definition,
                is_enum: true,
                variants,
            } => {
                let finish = builder.block();
                for (variant, fields) in variants.iter().enumerate() {
                    if !fields.iter().any(|field| field.glue.is_some()) {
                        continue;
                    }
                    let matched = builder.local(Type::Scalar(ScalarType::Bool));
                    builder.emit(MirInstruction::PatternTest {
                        dst: matched,
                        subject: MirLocal(0),
                        pattern: MirPattern::Enum {
                            definition: *definition,
                            variant: variant as u32,
                            field_count: fields.len() as u32,
                            field_types: fields.iter().map(|field| field.ty.clone()).collect(),
                            fields: vec![],
                        },
                    });
                    let selected = builder.block();
                    let next = builder.block();
                    builder.branch(matched, selected, next);
                    builder.current = selected;
                    builder.fields(fields);
                    builder.goto(finish);
                    builder.current = next;
                }
                builder.goto(finish);
                builder.current = finish;
            }
            Shape::Array { element, .. } => {
                return Err(format!(
                    "dynamic array destruction is not yet lowered for {element:?}"
                ));
            }
            Shape::Leaf => {}
        }
        let result = builder.local(Type::Unit);
        builder.emit(MirInstruction::ConstUnit { dst: result });
        builder.function.blocks[builder.current.0 as usize].terminator =
            MirTerminator::Return { value: result };
        crate::service::register_specialized_nominal_copy_descriptors(
            &mut builder.function,
            self.signatures,
        );
        Ok(builder.function.with_frozen_control_tables())
    }

    /// Expand lexical, replacement, parameter, and nonlocal boundaries only
    /// after concrete instance discovery. Every cleanup call must already be
    /// in the demand graph; this phase cannot smuggle in an undiscovered hook.
    pub(crate) fn elaborate(&mut self, function: &mut MirFunction) -> Result<(), String> {
        let original_blocks = function.blocks.len();
        for block in &mut function.blocks {
            if let MirTerminator::Return { value } = block.terminator {
                for parameter in function
                    .parameters
                    .iter()
                    .skip(function.captures as usize)
                    .rev()
                {
                    if *parameter != value {
                        block
                            .instructions
                            .push(MirInstruction::Drop { local: *parameter });
                    }
                }
            }
            if let MirTerminator::Leave { cleanup, .. } = &block.terminator {
                for action in &cleanup.actions {
                    if let crate::MirCleanupAction::Drop { binding, .. } = action
                        && let Some(local) = function.control.source_storage.binding_local(*binding)
                    {
                        block.instructions.push(MirInstruction::Drop { local });
                    }
                }
            }
            let mut instructions = Vec::new();
            for instruction in std::mem::take(&mut block.instructions) {
                if let MirInstruction::DestroyIf { local, .. } = instruction {
                    instructions.push(MirInstruction::Drop { local });
                }
                instructions.push(instruction);
            }
            block.instructions = instructions;
        }
        for block_index in 0..original_blocks {
            let instructions = std::mem::take(&mut function.blocks[block_index].instructions);
            let terminator = std::mem::replace(
                &mut function.blocks[block_index].terminator,
                MirTerminator::Unreachable,
            );
            let mut current = block_index;
            for instruction in instructions {
                let (local, indirect, ty) = match &instruction {
                    MirInstruction::Drop { local } => {
                        (*local, false, function.locals[local.0 as usize].ty.clone())
                    }
                    MirInstruction::DerefStore { reference, .. } => {
                        let Type::Reference { referent, .. } =
                            &function.locals[reference.0 as usize].ty
                        else {
                            return Err("replacement target is not a reference".into());
                        };
                        (*reference, true, (**referent).clone())
                    }
                    _ => {
                        function.blocks[current].instructions.push(instruction);
                        continue;
                    }
                };
                let Some(key) = self.discover(&ty)? else {
                    if indirect {
                        function.blocks[current].instructions.push(instruction);
                    }
                    continue;
                };
                // All checked source templates are retained for diagnostics,
                // including unused concrete bodies. Their absent call target
                // must remain an unresolved edge if they become reachable.
                // Do not instantiate an unrequested destructor here.
                let target = DefKey(key.fingerprint());
                let condition = MirLocal(function.locals.len() as u32);
                function.locals.push(MirLocalDecl {
                    ty: Type::Scalar(ScalarType::Bool),
                    source: CoreId(u32::MAX),
                });
                let owned = MirLocal(function.locals.len() as u32);
                function.locals.push(MirLocalDecl {
                    ty,
                    source: CoreId(u32::MAX),
                });
                let result = MirLocal(function.locals.len() as u32);
                function.locals.push(MirLocalDecl {
                    ty: Type::Unit,
                    source: CoreId(u32::MAX),
                });
                let selected = MirBlockId(function.blocks.len() as u32);
                let next = MirBlockId(selected.0 + 1);
                function.blocks[current].instructions.push(if indirect {
                    MirInstruction::DerefIsInitialized {
                        dst: condition,
                        reference: local,
                    }
                } else {
                    MirInstruction::IsInitialized {
                        dst: condition,
                        base: local,
                        fields: vec![],
                    }
                });
                function.blocks[current].terminator = MirTerminator::SwitchBool {
                    condition,
                    then_target: selected,
                    then_arguments: vec![],
                    else_target: next,
                    else_arguments: vec![],
                };
                let scope = function.blocks[current].scope;
                function.blocks.push(MirBlock {
                    scope,
                    parameters: vec![],
                    instructions: vec![
                        if indirect {
                            MirInstruction::DerefMove {
                                dst: owned,
                                reference: local,
                            }
                        } else {
                            MirInstruction::Move {
                                dst: owned,
                                src: local,
                            }
                        },
                        MirInstruction::Call {
                            dst: result,
                            callee: target,
                            generic_arguments: vec![],
                            trait_instance: None,
                            arguments: vec![owned],
                        },
                    ],
                    terminator: MirTerminator::Goto {
                        target: next,
                        arguments: vec![],
                    },
                });
                function.blocks.push(MirBlock {
                    scope,
                    parameters: vec![],
                    instructions: vec![],
                    terminator: MirTerminator::Unreachable,
                });
                current = next.0 as usize;
                if indirect {
                    function.blocks[current].instructions.push(instruction);
                }
            }
            function.blocks[current].terminator = terminator;
            if current != block_index
                && let Some(depth) = function
                    .control
                    .leave_handler_depths
                    .remove(&MirBlockId(block_index as u32))
            {
                function
                    .control
                    .leave_handler_depths
                    .insert(MirBlockId(current as u32), depth);
            }
        }
        *function = function.clone().with_frozen_control_tables();
        Ok(())
    }
}

struct Builder {
    function: MirFunction,
    current: MirBlockId,
}

impl Builder {
    fn new(definition: DefKey, ty: Type) -> Self {
        Self {
            function: MirFunction {
                safety: Safety::Safe,
                unsafe_execution: false,
                definition,
                nominal_copy_descriptors: vec![],
                captures: 0,
                parameters: vec![MirLocal(0)],
                locals: vec![MirLocalDecl {
                    ty,
                    source: CoreId(u32::MAX),
                }],
                result: Type::Unit,
                control: MirControlTables::default(),
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    scope: MirScopeId::ROOT,
                    parameters: vec![],
                    instructions: vec![],
                    terminator: MirTerminator::Unreachable,
                }],
            },
            current: MirBlockId(0),
        }
    }
    fn local(&mut self, ty: Type) -> MirLocal {
        let local = MirLocal(self.function.locals.len() as u32);
        self.function.locals.push(MirLocalDecl {
            ty,
            source: CoreId(u32::MAX),
        });
        local
    }
    fn block(&mut self) -> MirBlockId {
        let block = MirBlockId(self.function.blocks.len() as u32);
        self.function.blocks.push(MirBlock {
            scope: MirScopeId::ROOT,
            parameters: vec![],
            instructions: vec![],
            terminator: MirTerminator::Unreachable,
        });
        block
    }
    fn emit(&mut self, instruction: MirInstruction) {
        self.function.blocks[self.current.0 as usize]
            .instructions
            .push(instruction);
    }
    fn goto(&mut self, target: MirBlockId) {
        self.function.blocks[self.current.0 as usize].terminator = MirTerminator::Goto {
            target,
            arguments: vec![],
        };
    }
    fn branch(&mut self, condition: MirLocal, then_target: MirBlockId, else_target: MirBlockId) {
        self.function.blocks[self.current.0 as usize].terminator = MirTerminator::SwitchBool {
            condition,
            then_target,
            then_arguments: vec![],
            else_target,
            else_arguments: vec![],
        };
    }
    fn call(&mut self, key: &InstanceKey, argument: MirLocal) {
        let dst = self.local(Type::Unit);
        self.emit(MirInstruction::Call {
            dst,
            callee: DefKey(key.fingerprint()),
            generic_arguments: vec![],
            trait_instance: None,
            arguments: vec![argument],
        });
    }
    fn fields(&mut self, fields: &[Field]) {
        for (index, field) in fields.iter().enumerate() {
            let Some(key) = &field.glue else {
                continue;
            };
            let condition = self.local(Type::Scalar(ScalarType::Bool));
            self.emit(MirInstruction::IsInitialized {
                dst: condition,
                base: MirLocal(0),
                fields: vec![index as u32],
            });
            let selected = self.block();
            let next = self.block();
            self.branch(condition, selected, next);
            self.current = selected;
            let owned = self.local(field.ty.clone());
            self.emit(MirInstruction::TakeProjection {
                dst: owned,
                base: MirLocal(0),
                fields: vec![index as u32],
            });
            self.call(key, owned);
            self.goto(next);
            self.current = next;
        }
    }
}
