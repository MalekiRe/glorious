//! Physical erasure of resolved proof carriers in a closed executable batch.
//! This pass does not infer destinations: all executable label uses must
//! already have become control edges. Unsupported consumers retain their old
//! representation, together with every proof-bearing ABI dependency.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
enum Retained {
    Representation,
    Consumer,
    Boundary,
    Dependency(DefKey),
}

#[derive(Clone, Debug)]
pub(super) struct ProofErasurePlan {
    input: BTreeMap<DefKey, RuntimeMir>,
    replacements: BTreeMap<DefKey, RuntimeMir>,
    retained: BTreeMap<DefKey, Retained>,
}

impl ProofErasurePlan {
    pub(super) fn derive(input: &BTreeMap<DefKey, RuntimeMir>) -> Self {
        let mut replacements = BTreeMap::new();
        let mut retained = BTreeMap::new();
        let mut dependencies = BTreeMap::<DefKey, BTreeSet<DefKey>>::new();
        for (&definition, body) in input {
            match erase_body(body) {
                Ok(body) => {
                    replacements.insert(definition, body);
                }
                Err(reason) => {
                    retained.insert(definition, reason);
                }
            }
            let mut connect = |callee: DefKey, arguments: &[MirLocal], result: Option<MirLocal>| {
                let actual = arguments
                    .iter()
                    .map(|local| &body.locals[local.0 as usize].ty)
                    .chain(result.map(|local| &body.locals[local.0 as usize].ty));
                let Some(target) = input.get(&callee) else {
                    if actual.into_iter().any(has_label) {
                        retained.insert(definition, Retained::Boundary);
                    }
                    return;
                };
                let formal = target
                    .parameters
                    .iter()
                    .map(|local| &target.locals[local.0 as usize].ty)
                    .chain(std::iter::once(&target.result));
                if actual.chain(formal).any(has_label) {
                    dependencies.entry(definition).or_default().insert(callee);
                    dependencies.entry(callee).or_default().insert(definition);
                    // Directional Label -> Fn views are semantic invocation
                    // permissions, not interchangeable physical representations.
                    let compatible = arguments.len() == target.parameters.len()
                        && arguments
                            .iter()
                            .zip(&target.parameters)
                            .all(|(actual, formal)| {
                                match (
                                    physical(&body.locals[actual.0 as usize].ty),
                                    physical(&target.locals[formal.0 as usize].ty),
                                ) {
                                    (Some(actual), Some(formal)) => {
                                        crate::control_mir::call_type_matches(&formal, &actual)
                                    }
                                    _ => false,
                                }
                            })
                        && result.is_none_or(|local| {
                            target.result == Type::Never || {
                                match (
                                    physical(&body.locals[local.0 as usize].ty),
                                    physical(&target.result),
                                ) {
                                    (Some(actual), Some(formal)) => {
                                        crate::control_mir::call_type_matches(&formal, &actual)
                                    }
                                    _ => false,
                                }
                            }
                        });
                    if !compatible {
                        retained.insert(definition, Retained::Boundary);
                    }
                }
            };
            for action in &body.control.frame_cleanup {
                connect(action.destructor, &[action.owner], None);
            }
            for block in &body.blocks {
                if let RuntimeTerminator::TailCall { callee, arguments } = &block.terminator {
                    connect(*callee, arguments, None);
                }
                for operation in &block.instructions {
                    match operation {
                        RuntimeOperation::Call {
                            callee,
                            arguments,
                            dst,
                        } => connect(*callee, arguments, Some(*dst)),
                        // A lifted target can be invoked outside this body.
                        // Until callable contracts/environments are erased as
                        // one product, its proof ABI keeps the whole component.
                        RuntimeOperation::MakeCallable {
                            callee,
                            captures,
                            dst,
                            environment,
                        } => {
                            connect(*callee, captures, Some(*dst));
                            if let Some(destructor) = environment
                                .as_ref()
                                .and_then(|environment| environment.destructor)
                            {
                                // Environment erasure is not yet supported;
                                // retain proof-bearing cleanup signatures too.
                                connect(destructor, &[], None);
                            }
                        }
                        RuntimeOperation::HostCall {
                            resident_operations,
                            ..
                        } => {
                            for (_, destructor) in resident_operations {
                                if let Some(destructor) = destructor {
                                    connect(*destructor, &[], None);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        let mut pending = retained.keys().copied().collect::<VecDeque<_>>();
        while let Some(definition) = pending.pop_front() {
            for &dependent in dependencies.get(&definition).into_iter().flatten() {
                if let std::collections::btree_map::Entry::Vacant(entry) = retained.entry(dependent)
                {
                    entry.insert(Retained::Dependency(definition));
                    pending.push_back(dependent);
                }
            }
        }
        replacements.retain(|definition, body| {
            !retained.contains_key(definition) && input.get(definition) != Some(body)
        });
        Self {
            input: input.clone(),
            replacements,
            retained,
        }
    }

    pub(super) fn apply(
        self,
        input: &mut BTreeMap<DefKey, RuntimeMir>,
    ) -> Result<(), RuntimeError> {
        if *input != self.input {
            return Err(RuntimeError(
                "proof erasure plan does not match its frozen runtime batch".into(),
            ));
        }
        for (definition, body) in self.replacements {
            if self.retained.contains_key(&definition) {
                return Err(RuntimeError(
                    "proof erasure crosses a retained ABI component".into(),
                ));
            }
            input.insert(definition, body);
        }
        Ok(())
    }
}

fn argument_has_label(argument: &crate::GenericArgument) -> bool {
    match argument {
        crate::GenericArgument::Type(ty) => has_label(ty),
        crate::GenericArgument::EffectRow(row) => row
            .effects
            .iter()
            .any(|effect| effect.arguments.iter().any(argument_has_label)),
        crate::GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => has_label(subject) || trait_arguments.iter().any(argument_has_label),
        _ => false,
    }
}

fn has_label(ty: &Type) -> bool {
    if crate::types::label::payload(ty).is_some() {
        return true;
    }
    match ty {
        Type::Tuple(fields) => fields.iter().any(has_label),
        Type::Array(element)
        | Type::FixedArray { element, .. }
        | Type::StaticData { element, .. }
        | Type::Reference {
            referent: element, ..
        }
        | Type::RawPointer {
            pointee: element, ..
        } => has_label(element),
        Type::Nominal { arguments, .. } => arguments.iter().any(argument_has_label),
        Type::Callable {
            parameters,
            result,
            contract,
            effects,
            ..
        } => {
            parameters.iter().any(has_label)
                || has_label(result)
                || contract
                    .terms()
                    .iter()
                    .any(|(argument, _)| argument_has_label(argument))
                || effects
                    .effects
                    .iter()
                    .any(|effect| effect.arguments.iter().any(argument_has_label))
        }
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            has_label(subject)
                || trait_arguments
                    .iter()
                    .chain(item_arguments)
                    .any(argument_has_label)
        }
        _ => false,
    }
}

/// Only value-position products are mapped. Nominal identities, effect
/// families, foreign signatures and callable authority are never mapped by
/// recursively replacing their generic arguments with unit.
fn physical(ty: &Type) -> Option<Type> {
    if crate::types::label::payload(ty).is_some() {
        return Some(Type::Unit);
    }
    Some(match ty {
        Type::Tuple(fields) => Type::Tuple(fields.iter().map(physical).collect::<Option<_>>()?),
        Type::Array(element) => Type::Array(Box::new(physical(element)?)),
        Type::FixedArray { element, length } => Type::FixedArray {
            element: Box::new(physical(element)?),
            length: length.clone(),
        },
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability: *mutability,
            lifetime: *lifetime,
            referent: Box::new(physical(referent)?),
        },
        _ if !has_label(ty) => ty.clone(),
        _ => return None,
    })
}

fn erase_body(source: &RuntimeMir) -> Result<RuntimeMir, Retained> {
    let mut body = source.clone();
    for local in &mut body.locals {
        local.ty = physical(&local.ty).ok_or(Retained::Representation)?;
    }
    body.result = physical(&body.result).ok_or(Retained::Representation)?;
    if body.locals == source.locals && body.result == source.result {
        return Ok(body);
    }
    // Nominal layout identity is not a value position. Keep the old component
    // until a separate layout specialization establishes its physical key.
    if body.nominal_copy_descriptors.iter().any(|descriptor| {
        descriptor.arguments.iter().any(argument_has_label)
            || descriptor.variants.iter().flatten().any(has_label)
    }) {
        return Err(Retained::Representation);
    }
    for block in &mut body.blocks {
        for operation in &mut block.instructions {
            let changed = operation.references().iter().any(|local| {
                body.locals[local.0 as usize].ty != source.locals[local.0 as usize].ty
            });
            if !changed {
                continue;
            }
            match operation {
                RuntimeOperation::MakeLabel { dst, .. } => {
                    *operation = RuntimeOperation::ConstUnit { dst: *dst }
                }
                RuntimeOperation::MakeArray { element_type, .. }
                | RuntimeOperation::ProjectArray { element_type, .. }
                | RuntimeOperation::ArrayEmpty { element_type, .. }
                | RuntimeOperation::ArrayGetBorrowShared { element_type, .. }
                | RuntimeOperation::ArrayPushMove { element_type, .. } => {
                    *element_type = physical(element_type).ok_or(Retained::Representation)?;
                }
                RuntimeOperation::ProjectTuple { field_type, .. } => {
                    *field_type = physical(field_type).ok_or(Retained::Representation)?;
                }
                RuntimeOperation::PatternTest { pattern, .. } => erase_pattern(pattern)?,
                RuntimeOperation::MakeTuple { .. }
                | RuntimeOperation::Copy { .. }
                | RuntimeOperation::Move { .. }
                | RuntimeOperation::Store { .. }
                | RuntimeOperation::Borrow { .. }
                | RuntimeOperation::DerefCopy { .. }
                | RuntimeOperation::DerefMove { .. }
                | RuntimeOperation::DerefStore { .. }
                | RuntimeOperation::DerefIsInitialized { .. }
                | RuntimeOperation::TakeProjection { .. }
                | RuntimeOperation::IsInitialized { .. }
                | RuntimeOperation::StorageLive { .. }
                | RuntimeOperation::StorageDead { .. }
                | RuntimeOperation::DestroyIf { .. }
                | RuntimeOperation::Call { .. }
                | RuntimeOperation::ArrayLen { .. }
                | RuntimeOperation::ArrayElementIsInitialized { .. }
                | RuntimeOperation::TakeArrayElement { .. } => {}
                // This includes indirect invocation, operation payloads and
                // foreign calls. A missing transformation is not permission
                // to discard the control carrier used by that consumer.
                _ => return Err(Retained::Consumer),
            }
        }
    }
    // Re-freeze executable control sites after removing MakeLabel witnesses;
    // direct Leave brands and their exact payload destinations remain intact.
    Ok(body.with_frozen_control_tables())
}

fn erase_pattern(pattern: &mut MirPattern) -> Result<(), Retained> {
    match pattern {
        MirPattern::Any | MirPattern::Literal(_) => {}
        MirPattern::Tuple(fields) => {
            for field in fields {
                erase_pattern(field)?;
            }
        }
        MirPattern::Array {
            element, elements, ..
        } => {
            *element = physical(element).ok_or(Retained::Representation)?;
            for field in elements {
                erase_pattern(field)?;
            }
        }
        MirPattern::Record {
            field_types,
            fields,
            ..
        }
        | MirPattern::Enum {
            field_types,
            fields,
            ..
        } => {
            if field_types.iter().any(has_label) || fields.iter().any(|field| has_label(&field.ty))
            {
                return Err(Retained::Representation);
            }
            for field in fields {
                erase_pattern(&mut field.pattern)?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn label() -> Type {
        crate::types::label::new(
            crate::LabelBrand {
                owner: DefKey(crate::Digest::of_bytes(b"proof-erasure-test")),
                label: 0,
            },
            Type::Scalar(crate::ScalarType::I64),
        )
    }

    #[test]
    fn physical_mapping_preserves_identity_positions() {
        let label = label();
        assert_eq!(physical(&label), Some(Type::Unit));
        assert_eq!(
            physical(&Type::Tuple(vec![
                label.clone(),
                Type::Scalar(crate::ScalarType::I64)
            ])),
            Some(Type::Tuple(vec![
                Type::Unit,
                Type::Scalar(crate::ScalarType::I64)
            ]))
        );
        let nominal = Type::Nominal {
            definition: DefKey(crate::Digest::of_bytes(b"wrapper")),
            arguments: vec![crate::GenericArgument::Type(label.clone())],
        };
        assert_eq!(physical(&nominal), None);
        let mut callable = crate::types::label::callable(&label).unwrap();
        if let Type::Callable { parameters, .. } = &mut callable {
            parameters.push(label);
        }
        assert_eq!(physical(&callable), None);
    }

    #[test]
    fn erasure_plan_rejects_stale_input_without_mutation() {
        let body =
            super::super::tests::fixture("pub fn main() -> i64 { let destination = @main; 42 }");
        let mut functions = BTreeMap::from([(body.definition, body)]);
        let plan = ProofErasurePlan::derive(&functions);
        assert!(!plan.replacements.is_empty(), "{plan:#?}");
        functions.values_mut().next().unwrap().safety = Safety::Unsafe;
        let stale = functions.clone();
        assert!(
            plan.apply(&mut functions)
                .unwrap_err()
                .0
                .contains("frozen runtime batch")
        );
        assert_eq!(functions, stale);
    }

    #[test]
    fn erased_values_do_not_merge_label_indexed_effect_identities() {
        let mut body = super::super::tests::fixture("effect Ask { [0,1] ask() -> i64; }
            pub fn main() -> i64 { let destination = @main; handle Ask::ask() { Ask::ask() with _ => 42 } }");
        let arguments = vec![crate::GenericArgument::Type(label())];
        for operation in body
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.instructions)
        {
            if let RuntimeOperation::Perform {
                effect_arguments, ..
            }
            | RuntimeOperation::InstallHandler {
                effect_arguments, ..
            } = operation
            {
                *effect_arguments = arguments.clone();
            }
        }
        body = body.with_frozen_control_tables();
        body.frame = body.derive_frame().unwrap();
        body.validate().unwrap();
        let definition = body.definition;
        let mut functions = BTreeMap::from([(definition, body)]);
        let plan = ProofErasurePlan::derive(&functions);
        assert!(plan.replacements.contains_key(&definition));
        plan.apply(&mut functions).unwrap();
        let body = functions.get_mut(&definition).unwrap();
        body.frame = body.derive_frame().unwrap();
        body.validate().unwrap();
        assert!(!body.locals.iter().any(|local| has_label(&local.ty)));
        assert!(
            !body
                .blocks
                .iter()
                .flat_map(|block| &block.instructions)
                .any(|operation| matches!(operation, RuntimeOperation::MakeLabel { .. }))
        );
        assert!(!body.control.handlers.is_empty());
        assert!(
            body.control
                .handlers
                .iter()
                .all(|handler| handler.effect_arguments == arguments)
        );
        assert!(
            body.control
                .performs
                .iter()
                .all(|perform| perform.effect_arguments == arguments)
        );
    }

    #[test]
    fn unresolved_invocation_retains_the_entire_proof_abi_component() {
        let mut callee =
            super::super::tests::fixture("pub fn main(action: (i64) -> !) -> ! { action(42) }");
        let callee_key = DefKey(crate::Digest::of_bytes(b"retained-callee"));
        callee.definition = callee_key;
        let mut caller =
            super::super::tests::fixture("pub fn main() -> i64 { let destination = @main; 42 }");
        let source = caller
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .find_map(|op| {
                if let RuntimeOperation::MakeLabel { dst, .. } = op {
                    Some(*dst)
                } else {
                    None
                }
            })
            .unwrap();
        let proof = caller.locals[source.0 as usize].ty.clone();
        for local in &mut callee.locals {
            if matches!(local.ty, Type::Callable { .. }) {
                local.ty = proof.clone();
            }
        }
        // The synthetic receiver is now a proof label, not the fixture's
        // independently owned callable environment with its old destructor.
        callee.control.frame_cleanup.clear();
        let mut cleanup = super::super::tests::fixture("pub fn main(value: i64) {}");
        let cleanup_key = DefKey(crate::Digest::of_bytes(b"retained-cleanup"));
        cleanup.definition = cleanup_key;
        for local in &mut cleanup.locals {
            if local.ty == Type::Scalar(crate::ScalarType::I64) {
                local.ty = proof.clone();
            }
        }
        caller.control.frame_cleanup.push(MirFrameDrop {
            owner: source,
            destructor: cleanup_key,
        });
        // The dependency graph consumes frozen executable calls, independent
        // of source spelling. The unresolved receiver retains the caller and
        // its abandonment cleanup, not just ordinary named-call edges.
        let dst = MirLocal(caller.locals.len() as u32);
        caller.locals.push(MirLocalDecl {
            ty: Type::Never,
            source: CoreId(u32::MAX),
        });
        caller.blocks[0].instructions.push(RuntimeOperation::Call {
            dst,
            callee: callee_key,
            arguments: vec![source],
        });
        let mut functions = BTreeMap::from([
            (caller.definition, caller),
            (callee_key, callee),
            (cleanup_key, cleanup),
        ]);
        let original = functions.clone();
        let plan = ProofErasurePlan::derive(&functions);
        assert_eq!(plan.retained.get(&callee_key), Some(&Retained::Consumer));
        assert!(plan.replacements.is_empty());
        assert_eq!(plan.retained.len(), 3);
        plan.apply(&mut functions).unwrap();
        assert_eq!(functions, original);
    }
}
