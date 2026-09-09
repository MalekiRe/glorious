//! Concrete, source-type-directed destruction. Selection and traversal belong
//! to the compiler: executable glue consists of ordinary MIR calls and CFGs.

use std::collections::{BTreeMap, BTreeSet};

use crate::{DefKey, Digest, ElaboratedHeader, ElaboratedInterface, ElaboratedNominalLayout,
    ElaboratedTraitReference, GenericArgument, GenericKind, InstanceKey, TraitAnswer, TraitGoal, TraitSolver, Type};
mod selection;
pub(crate) use selection::custom_drop_may_apply;
#[cfg(test)]
use crate::{CoreId, MirBlock, MirBlockId, MirControlTables, MirFunction, MirInstruction,
    MirLocal, MirLocalDecl, MirPattern, MirScopeId, MirTerminator, Mutability, Safety, ScalarType};

fn glue_definition() -> DefKey {
    DefKey(Digest::of_bytes(b"grandiose-owned-destruction-glue-v1"))
}

pub(crate) fn is_glue(key: &InstanceKey) -> bool {
    key.callable == glue_definition()
}

pub(crate) use crate::cleanup_mir::{DestructionField as Field, DestructionShape as Shape, DestructionProgram as Plan};

pub(crate) struct Planner<'a> {
    signatures: &'a ElaboratedInterface,
    solver: TraitSolver,
    plans: BTreeMap<InstanceKey, Plan>,
    trivial: BTreeSet<InstanceKey>,
    active: BTreeSet<InstanceKey>,
}

impl<'a> Planner<'a> {
    /// Snapshot the already-demanded concrete destruction language. Cleanup
    /// cannot resolve new trait evidence or extend executable demand.
    pub(crate) fn frozen_plans(&self) -> BTreeMap<InstanceKey, Plan> {
        self.plans.clone()
    }
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
        // The payload is the destination's type, not a resident owned by the
        // proof-only label. Ending a label value runs no payload destructor.
        if crate::types::label::payload(ty).is_some() { return Ok(None); }
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
            Type::Nominal { definition, .. } if *definition == crate::refinement::bindings_definition() => {
                let fields = crate::refinement::binding_pack_fields(ty)
                    .ok_or_else(|| "destruction binding pack has no canonical sealed layout".to_string())?;
                Shape::Nominal { definition: *definition, is_enum: false, variants: vec![self.fields(fields)?] }
            }
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
            Type::FixedArray { .. } if ty.fixed_array_length() == Some(0) => Shape::Leaf,
            Type::Array(element) | Type::FixedArray { element, .. } => match self.discover(element)? {
                Some(glue) => Shape::Array {
                    element: (**element).clone(),
                    glue,
                },
                None => Shape::Leaf,
            },
            Type::Callable { .. } => Shape::Callable,
            // References/raw pointers do not own their referents. Callable
            // capture traversal is selected by its separate sealed descriptor.
            _ => Shape::Leaf,
        };
        let has_fields = match &shape {
            Shape::Tuple(fields) => fields.iter().any(|field| field.glue.is_some()),
            Shape::Nominal { variants, .. } => {
                variants.iter().flatten().any(|field| field.glue.is_some())
            }
            Shape::Array { .. } | Shape::Callable => true,
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
                // A concrete nominal may still spell its fields using
                // associated projections. Seal those before deciding that a
                // field is trivial; an unresolved projection is not no-Drop.
                let ty = self.solver.normalize_type(ty.clone())
                    .map_err(|error| format!("destruction field projection: {error:?}"))?;
                let ty = crate::service::normalize_materialized_type(&ty, &mut self.solver)?;
                Ok(Field {
                    ty: ty.clone(),
                    glue: self.discover(&ty)?,
                })
            })
            .collect()
    }

    /// Preserve the compiler's concrete selection on each native boundary,
    /// including referent/pointee residents that are not owned by this frame.
    #[cfg(test)]
    pub(crate) fn seal_native_operations(&mut self, function: &mut MirFunction) -> Result<(), String> {
        for instruction in function.blocks.iter_mut().flat_map(|block| &mut block.instructions) {
            let MirInstruction::HostCall { parameters, result, resident_operations, .. } = instruction else { continue; };
            let roots = parameters.iter().chain(std::iter::once(&*result)).cloned().collect::<Vec<_>>();
            let mut residents = crate::mir::native_contract_residents(&roots, self.signatures)?;
            residents.sort_by_key(crate::types::canonical_type_encoding);
            *resident_operations = residents.into_iter().map(|ty| {
                let glue = self.discover(&ty)?.map(|key| DefKey(key.fingerprint()));
                Ok((ty, glue))
            }).collect::<Result<_, String>>()?;
        }
        Ok(())
    }

    /// Give each concrete, branded environment ordinary executable cleanup
    /// glue. Borrowed captures are not owners, and invocation arguments/results
    /// never participate in the environment's structural layout.
    #[cfg(test)]
    pub(crate) fn seal_callable_environments(
        &mut self,
        functions: &mut BTreeMap<DefKey, MirFunction>,
    ) -> Result<BTreeSet<DefKey>, String> {
        let mut generated = BTreeMap::new();
        for function in functions.values_mut() {
            for instruction in function.blocks.iter_mut().flat_map(|block| &mut block.instructions) {
                let MirInstruction::MakeCallable { callee, environment: Some(environment), .. } = instruction else { continue; };
                let types = environment.captures.iter().map(|capture| capture.ty.clone()).collect::<Vec<_>>();
                // Open templates are retained for diagnostics. Their concrete
                // materialized producers receive distinct executable glue.
                if InstanceKey::new(glue_definition(), &[GenericKind::Type],
                    vec![GenericArgument::Type(Type::Tuple(types.clone()))]).is_err() {
                    continue;
                }
                let mut owned = Vec::new();
                for (index, capture) in environment.captures.iter().enumerate() {
                    if matches!(capture.mode, crate::CaptureMode::Copy | crate::CaptureMode::Move)
                        && self.discover(&capture.ty)?.is_some()
                    {
                        owned.push(index);
                    }
                }
                if owned.is_empty() { continue; }
                let target = crate::mir::callable_environment_destructor_definition(*callee);
                environment.destructor = Some(target);
                let mut glue = Builder::function(target, Type::Unit);
                glue.locals = types.into_iter().map(|ty| MirLocalDecl { ty, source: CoreId(u32::MAX) }).collect();
                glue.parameters = (0..glue.locals.len()).map(|index| MirLocal(index as u32)).collect();
                glue.blocks[0].instructions = owned.into_iter().rev()
                    .map(|index| MirInstruction::Drop { local: MirLocal(index as u32) }).collect();
                let result = MirLocal(glue.locals.len() as u32);
                glue.locals.push(MirLocalDecl { ty: Type::Unit, source: CoreId(u32::MAX) });
                glue.blocks[0].instructions.push(MirInstruction::ConstUnit { dst: result });
                glue.blocks[0].terminator = MirTerminator::Return { value: result };
                crate::service::register_specialized_nominal_copy_descriptors(&mut glue, self.signatures)?;
                self.elaborate_with_frame_cleanup(&mut glue, false)?;
                if let Some(previous) = generated.insert(target, glue.clone())
                    && previous != glue {
                    return Err("callable producers disagree on environment destruction".into());
                }
            }
        }
        let keys = generated.keys().copied().collect();
        for (key, function) in generated {
            if functions.insert(key, function).is_some() {
                return Err("callable environment destructor identity collision".into());
            }
        }
        Ok(keys)
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
            Shape::Leaf | Shape::Callable => {}
        }
        Ok(callees)
    }

    #[cfg(test)]
    pub(crate) fn materialize(&self, key: &InstanceKey) -> Result<MirFunction, String> {
        let plan = self
            .plans
            .get(key)
            .ok_or("missing materialized destruction plan")?;
        let mut function = Builder::function(DefKey(key.fingerprint()), plan.ty.clone());
        let mut builder = Builder {
            function: &mut function,
            current: MirBlockId(0),
        };
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
        builder.structural_fields(MirLocal(0), &plan.shape)?;
        let result = builder.local(Type::Unit);
        builder.emit(MirInstruction::ConstUnit { dst: result });
        builder.function.blocks[builder.current.0 as usize].terminator =
            MirTerminator::Return { value: result };
        crate::service::register_specialized_nominal_copy_descriptors(
            builder.function,
            self.signatures,
        )?;
        Ok(function.with_frozen_control_tables())
    }

    /// Expand lexical, replacement, parameter, and nonlocal boundaries only
    /// after concrete instance discovery. Every cleanup call must already be
    /// in the demand graph; this phase cannot smuggle in an undiscovered hook.
    #[cfg(test)]
    pub(crate) fn elaborate(&mut self, function: &mut MirFunction) -> Result<(), String> {
        self.elaborate_with_frame_cleanup(function, true)
    }

    #[cfg(test)]
    fn elaborate_with_frame_cleanup(&mut self, function: &mut MirFunction, frame_cleanup: bool) -> Result<(), String> {
        let original_blocks = function.blocks.len();
        let ownership = crate::ownership::FrameOwnership::for_function(function);
        function.control.frame_cleanup.clear();
        if frame_cleanup {
            for owner in ownership.exiting(None) {
                if let Some(key) = self.discover(&function.locals[owner.0 as usize].ty)? {
                    function.control.frame_cleanup.push(crate::mir::MirFrameDrop {
                        owner, destructor: DefKey(key.fingerprint()),
                    });
                }
            }
        }
        for block in &mut function.blocks {
            if frame_cleanup && let MirTerminator::Return { value } = block.terminator {
                for local in ownership.exiting(Some(value)) {
                    block.instructions.push(MirInstruction::Drop { local });
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
                    instructions: vec![],
                    terminator: MirTerminator::Unreachable,
                });
                function.blocks.push(MirBlock {
                    scope,
                    parameters: vec![],
                    instructions: vec![],
                    terminator: MirTerminator::Unreachable,
                });
                let plan = self
                    .plans
                    .get(&key)
                    .ok_or("missing elaborated destruction plan")?;
                let mut builder = Builder {
                    function,
                    current: selected,
                };
                let owned = builder.local(ty);
                if !indirect && plan.hook.is_none() {
                    // A structural wrapper has no root hook. Inspect its
                    // actual residual fields here instead of allocating a
                    // call frame merely to discover an already-moved payload.
                    // Child glue remains an ordinary demanded call, in field
                    // order, and active hooks are never elided.
                    builder.structural_fields(local, &plan.shape)?;
                    if !matches!(plan.shape, Shape::Callable) {
                        builder.emit(MirInstruction::Move {
                            dst: owned,
                            src: local,
                        });
                    }
                } else {
                    builder.emit(if indirect {
                        MirInstruction::DerefMove {
                            dst: owned,
                            reference: local,
                        }
                    } else {
                        MirInstruction::Move {
                            dst: owned,
                            src: local,
                        }
                    });
                    let result = builder.local(Type::Unit);
                    builder.emit(MirInstruction::Call {
                        dst: result,
                        callee: target,
                        generic_arguments: vec![],
                        trait_instance: None,
                        arguments: vec![owned],
                    });
                }
                builder.goto(next);
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

#[cfg(test)]
struct Builder<'a> {
    function: &'a mut MirFunction,
    current: MirBlockId,
}

#[cfg(test)]
impl Builder<'_> {
    fn function(definition: DefKey, ty: Type) -> MirFunction {
        MirFunction {
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
        let scope = self.function.blocks[self.current.0 as usize].scope;
        self.function.blocks.push(MirBlock {
            scope,
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
    fn structural_fields(&mut self, local: MirLocal, shape: &Shape) -> Result<(), String> {
        match shape {
            Shape::Callable => {
                let dst = self.local(Type::Unit);
                self.emit(MirInstruction::DestroyCallable { dst, value: local });
            }
            Shape::Tuple(fields) => self.fields(local, fields),
            Shape::Nominal {
                is_enum: false,
                variants,
                ..
            } => self.fields(local, &variants[0]),
            Shape::Nominal {
                definition,
                is_enum: true,
                variants,
            } => {
                let finish = self.block();
                for (variant, fields) in variants.iter().enumerate() {
                    if !fields.iter().any(|field| field.glue.is_some()) {
                        continue;
                    }
                    let matched = self.local(Type::Scalar(ScalarType::Bool));
                    self.emit(MirInstruction::PatternTest {
                        dst: matched,
                        subject: local,
                        pattern: MirPattern::Enum {
                            definition: *definition,
                            variant: variant as u32,
                            field_count: fields.len() as u32,
                            field_types: fields.iter().map(|field| field.ty.clone()).collect(),
                            fields: vec![],
                        },
                    });
                    let selected = self.block();
                    let next = self.block();
                    self.branch(matched, selected, next);
                    self.current = selected;
                    self.fields(local, fields);
                    self.goto(finish);
                    self.current = next;
                }
                self.goto(finish);
                self.current = finish;
            }
            Shape::Array { element, .. } => {
                return Err(format!(
                    "dynamic array destruction is not yet lowered for {element:?}"
                ));
            }
            Shape::Leaf => {}
        }
        Ok(())
    }
    fn fields(&mut self, local: MirLocal, fields: &[Field]) {
        for (index, field) in fields.iter().enumerate() {
            let Some(key) = &field.glue else {
                continue;
            };
            let condition = self.local(Type::Scalar(ScalarType::Bool));
            self.emit(MirInstruction::IsInitialized {
                dst: condition,
                base: local,
                fields: vec![index as u32],
            });
            let selected = self.block();
            let next = self.block();
            self.branch(condition, selected, next);
            self.current = selected;
            let owned = self.local(field.ty.clone());
            self.emit(MirInstruction::TakeProjection {
                dst: owned,
                base: local,
                fields: vec![index as u32],
            });
            self.call(key, owned);
            self.goto(next);
            self.current = next;
        }
    }
}
