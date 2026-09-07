//! Storage expansion of preselected concrete destruction; no trait solver.
use super::*;
use crate::cleanup_mir::*;
use crate::control_mir::{ControlPlace, ControlValue};
use crate::destruction::{Field, Plan, Shape};
use crate::{Mutability, ScalarType};

#[derive(Clone, Debug)]
pub(crate) struct PendingDestroy {
    block: usize,
    instruction: usize,
    local: MirLocal,
    fields: Vec<u32>,
    indirect: bool,
    destructor: DefKey,
}
impl CleanupMir {
    pub(crate) fn record_runtime_plan(
        &self,
        plan: CleanupPlanId,
        block: usize,
        instruction: usize,
        local: &impl Fn(ControlValue) -> MirLocal,
        pending: &mut Vec<PendingDestroy>,
    ) {
        for action in &self.plans[plan.0 as usize].actions {
            let CleanupAction::Destroy { flag, destructor } = action else {
                continue;
            };
            fn path(place: &ControlPlace) -> (ControlValue, Vec<u32>, bool) {
                match place {
                    ControlPlace::Local(value) | ControlPlace::Temporary(value) => {
                        (*value, vec![], false)
                    }
                    ControlPlace::Deref { reference, .. } => (*reference, vec![], true),
                    ControlPlace::Field { base, index, .. } => {
                        let (root, mut fields, indirect) = path(base);
                        fields.push(*index);
                        (root, fields, indirect)
                    }
                }
            }
            let (root, fields, indirect) = path(&self.flags[flag.0 as usize].place);
            pending.push(PendingDestroy {
                block,
                instruction,
                local: local(root),
                fields,
                indirect,
                destructor: *destructor,
            });
        }
    }
}
pub(crate) fn materialize(
    key: &InstanceKey,
    plan: &Plan,
    signatures: &crate::ElaboratedInterface,
) -> Result<RuntimeMir, String> {
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
        builder.emit(RuntimeOperation::Borrow {
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
    builder.emit(RuntimeOperation::ConstUnit { dst: result });
    builder.function.blocks[builder.current.0 as usize].terminator =
        RuntimeTerminator::Return { value: result };
    builder.function.register_layouts(signatures)?;
    Ok(function.with_frozen_control_tables())
}

/// Expand only the explicit plan sites. The old untyped Drop instruction is
/// deliberately not accepted here.
pub(super) fn expand(
    function: &mut RuntimeMir,
    pending: Vec<PendingDestroy>,
    plans: &BTreeMap<DefKey, Plan>,
) -> Result<(), String> {
    let original_blocks = function.blocks.len();
    let mut sites = BTreeMap::<(usize, usize), Vec<PendingDestroy>>::new();
    for site in pending {
        sites
            .entry((site.block, site.instruction))
            .or_default()
            .push(site);
    }
    // Storage freezing may add guarded root disarms. Indirect replacements
    // already have their exact Cleanup plan; adding disposal at DerefStore
    // would repeat it through a fresh reference to the same native address.
    for (block_index, block) in function.blocks.iter().enumerate() {
        for (index, instruction) in block.instructions.iter().enumerate() {
            let (local, indirect, ty) = match instruction {
                RuntimeOperation::DestroyIf { local, .. } => {
                    (*local, false, &function.locals[local.0 as usize].ty)
                }
                _ => continue,
            };
            if let Some((destructor, _)) = plans.iter().find(|(_, plan)| &plan.ty == ty) {
                sites
                    .entry((block_index, index))
                    .or_default()
                    .push(PendingDestroy {
                        block: block_index,
                        instruction: index,
                        local,
                        fields: vec![],
                        indirect,
                        destructor: *destructor,
                    });
            }
        }
    }
    for block_index in 0..original_blocks {
        let instructions = std::mem::take(&mut function.blocks[block_index].instructions);
        let terminator = std::mem::replace(
            &mut function.blocks[block_index].terminator,
            RuntimeTerminator::Unreachable,
        );
        let mut current = MirBlockId(block_index as u32);
        for index in 0..=instructions.len() {
            for site in sites.remove(&(block_index, index)).unwrap_or_default() {
                let plan = plans
                    .get(&site.destructor)
                    .ok_or("cleanup destructor was not selected")?;
                let mut builder = Builder { function, current };
                let mut local = site.local;
                let indirect = site.indirect || !site.fields.is_empty();
                if !site.fields.is_empty() {
                    let reference = builder.local(Type::Reference {
                        mutability: Mutability::Unique,
                        lifetime: crate::Lifetime::Elided,
                        referent: Box::new(plan.ty.clone()),
                    });
                    builder.emit(RuntimeOperation::Borrow {
                        dst: reference,
                        src: local,
                        fields: site.fields,
                        unique: true,
                        reborrow: site.indirect,
                    });
                    local = reference;
                }
                let condition = builder.local(Type::Scalar(ScalarType::Bool));
                builder.emit(if indirect {
                    RuntimeOperation::DerefIsInitialized {
                        dst: condition,
                        reference: local,
                    }
                } else {
                    RuntimeOperation::IsInitialized {
                        dst: condition,
                        base: local,
                        fields: vec![],
                    }
                });
                let selected = builder.block();
                let next = builder.block();
                builder.branch(condition, selected, next);
                builder.current = selected;
                let owned = builder.local(plan.ty.clone());
                if !indirect && plan.hook.is_none() {
                    builder.structural_fields(local, &plan.shape)?;
                    if !matches!(plan.shape, Shape::Callable) {
                        builder.emit(RuntimeOperation::Move {
                            dst: owned,
                            src: local,
                        });
                    }
                } else {
                    builder.emit(if indirect {
                        RuntimeOperation::DerefMove {
                            dst: owned,
                            reference: local,
                        }
                    } else {
                        RuntimeOperation::Move {
                            dst: owned,
                            src: local,
                        }
                    });
                    let dst = builder.local(Type::Unit);
                    builder.emit(RuntimeOperation::Call {
                        dst,
                        callee: site.destructor,
                        arguments: vec![owned],
                    });
                }
                builder.goto(next);
                current = next;
            }
            if let Some(instruction) = instructions.get(index) {
                function.blocks[current.0 as usize]
                    .instructions
                    .push(instruction.clone());
            }
        }
        function.blocks[current.0 as usize].terminator = terminator;
        if current.0 as usize != block_index
            && let Some(depth) = function
                .control
                .leave_handler_depths
                .remove(&MirBlockId(block_index as u32))
        {
            function.control.leave_handler_depths.insert(current, depth);
        }
    }
    if !sites.is_empty() {
        return Err("cleanup site lies outside its block".into());
    }
    *function = function.clone().with_frozen_control_tables();
    Ok(())
}

pub(super) fn environment(
    closure: &CleanupClosure,
    signatures: &crate::ElaboratedInterface,
    plans: &BTreeMap<DefKey, Plan>,
) -> Result<Option<RuntimeMir>, String> {
    let Some(definition) = closure.destructor else {
        return Ok(None);
    };
    let mut function = Builder::function(definition, Type::Unit);
    function.locals = closure
        .environment
        .captures
        .iter()
        .map(|capture| MirLocalDecl {
            ty: capture.ty.clone(),
            source: CoreId(u32::MAX),
        })
        .collect();
    function.parameters = (0..function.locals.len())
        .map(|index| MirLocal(index as u32))
        .collect();
    let mut pending = vec![];
    for capture in &closure.cleanup {
        pending.push(PendingDestroy {
            block: 0,
            instruction: 0,
            local: MirLocal(capture.index),
            fields: vec![],
            indirect: false,
            destructor: capture.destructor,
        });
    }
    let mut builder = Builder {
        function: &mut function,
        current: MirBlockId(0),
    };
    let result = builder.local(Type::Unit);
    builder.emit(RuntimeOperation::ConstUnit { dst: result });
    builder.function.blocks[0].terminator = RuntimeTerminator::Return { value: result };
    function.register_layouts(signatures)?;
    expand(&mut function, pending, plans)?;
    Ok(Some(function))
}

struct Builder<'a> {
    function: &'a mut RuntimeMir,
    current: MirBlockId,
}

impl Builder<'_> {
    fn function(definition: DefKey, ty: Type) -> RuntimeMir {
        RuntimeMir {
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
            frame: RuntimeFrame::default(),
            entry: MirBlockId(0),
            blocks: vec![RuntimeBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![],
                terminator: RuntimeTerminator::Unreachable,
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
        self.function.blocks.push(RuntimeBlock {
            scope,
            parameters: vec![],
            instructions: vec![],
            terminator: RuntimeTerminator::Unreachable,
        });
        block
    }
    fn emit(&mut self, instruction: RuntimeOperation) {
        self.function.blocks[self.current.0 as usize]
            .instructions
            .push(instruction);
    }
    fn goto(&mut self, target: MirBlockId) {
        self.function.blocks[self.current.0 as usize].terminator = RuntimeTerminator::Goto {
            target,
            arguments: vec![],
        };
    }
    fn branch(&mut self, condition: MirLocal, then_target: MirBlockId, else_target: MirBlockId) {
        self.function.blocks[self.current.0 as usize].terminator = RuntimeTerminator::SwitchBool {
            condition,
            then_target,
            then_arguments: vec![],
            else_target,
            else_arguments: vec![],
        };
    }
    fn call(&mut self, key: &InstanceKey, argument: MirLocal) {
        let dst = self.local(Type::Unit);
        self.emit(RuntimeOperation::Call {
            dst,
            callee: DefKey(key.fingerprint()),
            arguments: vec![argument],
        });
    }
    fn structural_fields(&mut self, local: MirLocal, shape: &Shape) -> Result<(), String> {
        match shape {
            Shape::Callable => {
                let dst = self.local(Type::Unit);
                self.emit(RuntimeOperation::DestroyCallable { dst, value: local });
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
                    self.emit(RuntimeOperation::PatternTest {
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
            Shape::Array { element, glue } => {
                let length = self.local(Type::Scalar(ScalarType::Usize));
                let zero = self.local(Type::Scalar(ScalarType::Usize));
                let one = self.local(Type::Scalar(ScalarType::Usize));
                let truth = self.local(Type::Scalar(ScalarType::U32));
                self.emit(RuntimeOperation::ArrayLen {
                    dst: length,
                    value: local,
                });
                self.emit(RuntimeOperation::ConstUsize {
                    dst: zero,
                    value: 0,
                });
                self.emit(RuntimeOperation::ConstUsize { dst: one, value: 1 });
                self.emit(RuntimeOperation::ConstU32 {
                    dst: truth,
                    value: 1,
                });
                let head = self.block();
                let probe = self.block();
                let destroy = self.block();
                let next = self.block();
                let finish = self.block();
                let remaining = self.local(Type::Scalar(ScalarType::Usize));
                self.emit(RuntimeOperation::StoreUsize {
                    dst: remaining,
                    value: length,
                });
                self.goto(head);
                self.current = head;
                let comparison = self.local(Type::Scalar(ScalarType::U32));
                let empty = self.local(Type::Scalar(ScalarType::Bool));
                self.emit(RuntimeOperation::IntIntrinsic {
                    dst: comparison,
                    primitive: PrimitiveRole::IntEqual,
                    scalar: ScalarType::Usize,
                    arguments: vec![remaining, zero],
                });
                self.emit(RuntimeOperation::U32Eq {
                    dst: empty,
                    left: comparison,
                    right: truth,
                });
                self.branch(empty, finish, probe);
                self.current = probe;
                let index = self.local(Type::Scalar(ScalarType::Usize));
                self.emit(RuntimeOperation::IntIntrinsic {
                    dst: index,
                    primitive: PrimitiveRole::IntWrappingSub,
                    scalar: ScalarType::Usize,
                    arguments: vec![remaining, one],
                });
                let initialized = self.local(Type::Scalar(ScalarType::Bool));
                self.emit(RuntimeOperation::ArrayElementIsInitialized {
                    dst: initialized,
                    value: local,
                    index,
                });
                self.branch(initialized, destroy, next);
                self.current = destroy;
                let owned = self.local(element.clone());
                self.emit(RuntimeOperation::TakeArrayElement {
                    dst: owned,
                    value: local,
                    index,
                });
                self.call(glue, owned);
                self.goto(next);
                self.current = next;
                self.emit(RuntimeOperation::StoreUsize {
                    dst: remaining,
                    value: index,
                });
                self.goto(head);
                self.current = finish;
            }
            Shape::Leaf => {}
        }
        Ok(())
    }
    fn fields(&mut self, local: MirLocal, fields: &[Field]) {
        for (index, field) in fields.iter().enumerate().rev() {
            let Some(key) = &field.glue else {
                continue;
            };
            let condition = self.local(Type::Scalar(ScalarType::Bool));
            self.emit(RuntimeOperation::IsInitialized {
                dst: condition,
                base: local,
                fields: vec![index as u32],
            });
            let selected = self.block();
            let next = self.block();
            self.branch(condition, selected, next);
            self.current = selected;
            let owned = self.local(field.ty.clone());
            self.emit(RuntimeOperation::TakeProjection {
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
