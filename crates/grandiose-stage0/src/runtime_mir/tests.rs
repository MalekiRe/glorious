use super::*;

pub(crate) fn finalize_fixture(mut body: RuntimeMir) -> RuntimeMir {
    body.frame = body.derive_frame().unwrap();
    body.validate().unwrap();
    body
}

pub(crate) fn fixture(source: &str) -> RuntimeMir {
    let cleanup = crate::cleanup_mir::tests::fixture(source);
    let (mut body, _) = cleanup
        .lower_runtime_values(
            cleanup.result.clone(),
            0,
            None,
            Some(&crate::ElaboratedInterface::default()),
        )
        .unwrap();
    body.frame = body.derive_frame().unwrap();
    body.validate().unwrap();
    body
}
const CALL: &str = "pub fn main(action: () -> i64) -> i64 { action() }";
const PERFORM: &str = "effect Ask { [0, 1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask(42) { Ask::ask(value) with _ => value } }";

#[test]
fn prepared_nominal_label_retains_its_brand_without_address_authority() {
    let mut body = fixture("pub fn main(target: (i64) -> !) -> ! { target(42) }");
    let brand = crate::LabelBrand { owner: body.definition, label: 0 };
    let label = crate::types::label::new(brand, Type::Scalar(crate::ScalarType::I64));
    for local in &mut body.locals {
        if matches!(local.ty, Type::Callable { .. }) { local.ty = label.clone(); }
    }
    // Labels have no callable-owned environment to destroy.
    body.control.frame_cleanup.clear();
    body.frame = body.derive_frame().unwrap();
    body.validate().unwrap();
    let (dst, src) = body.blocks.iter().flat_map(|block| &block.instructions).find_map(|op|
        match op { RuntimeOperation::PrepareInvocation { dst, src, .. } => Some((*dst, *src)), _ => None }).unwrap();

    let mut wrong_brand = body.clone();
    wrong_brand.locals[dst.0 as usize].ty = crate::types::label::new(
        crate::LabelBrand { label: 1, ..brand }, Type::Scalar(crate::ScalarType::I64));
    wrong_brand.frame = wrong_brand.derive_frame().unwrap();
    assert!(wrong_brand.validate().unwrap_err().contains("projection destination type"));

    let mut addressed = body.clone();
    addressed.locals[src.0 as usize].ty = Type::Reference {
        mutability: Mutability::Shared, lifetime: crate::Lifetime::Static, referent: Box::new(label.clone()),
    };
    for op in addressed.blocks.iter_mut().flat_map(|block| &mut block.instructions) {
        if let RuntimeOperation::PrepareInvocation { reborrow, .. } = op { *reborrow = true; }
    }
    addressed.frame = addressed.derive_frame().unwrap();
    assert!(addressed.validate().unwrap_err().contains("preparation requires a callable receiver"));

    let mut noncallable = body;
    for local in &mut noncallable.locals {
        if local.ty == label { local.ty = Type::Unit; }
    }
    noncallable.frame = noncallable.derive_frame().unwrap();
    assert!(noncallable.validate().unwrap_err().contains("preparation requires a callable receiver"));
}

#[test]
fn a_stored_reference_can_change_its_body_local_loan_without_changing_its_type() {
    let body = fixture("pub fn main() -> i64 {let first = 41; let second = 42; let mut pointer = &first; pointer = &second; *pointer}");
    assert!(body.blocks.iter().flat_map(|block| &block.instructions).any(|operation|
        matches!(operation, RuntimeOperation::Store { dst, src }
            if matches!(body.locals[dst.0 as usize].ty, Type::Reference { .. })
                && body.locals[dst.0 as usize].ty != body.locals[src.0 as usize].ty)));
}

#[test]
fn handler_candidate_order_follows_scopes_not_arena_numbers() {
    let mut body = fixture("effect Ask { [1, 1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(1) { Ask::ask(0) => 0 } } { Ask::ask(value) => value } }");
    assert_eq!(body.control.handlers.len(), 2);
    assert!(body.control.performs.iter().any(|site| site.handler_candidates.len() == 2));
    let rename = |id: &mut MirHandlerSiteId| { id.0 = 1 - id.0; };
    body.control.handlers.swap(0, 1);
    for scope in &mut body.control.scopes {
        if let Some(id) = &mut scope.entered_handler { rename(id); }
    }
    for perform in &mut body.control.performs {
        for id in &mut perform.handler_candidates { rename(id); }
    }
    for resumption in &mut body.control.resumptions {
        if let Some(id) = &mut resumption.originating_handler { rename(id); }
    }
    for block in &mut body.blocks {
        for operation in &mut block.instructions {
            if let RuntimeOperation::InstallHandler { site, .. } = operation { rename(site); }
        }
    }
    body.frame = body.derive_frame().unwrap();
    body.validate().unwrap();
    let site = body.control.performs.iter_mut().find(|site| site.handler_candidates.len() == 2).unwrap();
    site.handler_candidates.reverse();
    assert!(body.validate().unwrap_err().contains("lexical handler candidates"),
        "renumbering is harmless, but reversing lexical precedence must be rejected");
}

#[test]
fn runtime_rejects_reading_a_consumed_effect_argument() {
    let mut body = fixture(PERFORM);
    let dst = MirLocal(body.locals.len() as u32);
    body.locals.push(MirLocalDecl {
        ty: Type::Scalar(crate::ScalarType::I64),
        source: CoreId(u32::MAX),
    });
    let mut inserted = false;
    for block in &mut body.blocks {
        if let Some((offset, src)) =
            block
                .instructions
                .iter()
                .enumerate()
                .find_map(|(offset, op)| {
                    if let RuntimeOperation::Perform { arguments, .. } = op {
                        Some((offset, arguments[0]))
                    } else {
                        None
                    }
                })
        {
            block
                .instructions
                .insert(offset + 1, RuntimeOperation::Copy { dst, src });
            inserted = true;
            break;
        }
    }
    assert!(inserted);
    body.frame = body.derive_frame().unwrap();
    assert!(body.validate().unwrap_err().contains("dead/uninitialized"));
}

#[test]
fn runtime_rejects_reading_a_consumed_resumption_argument() {
    let mut body = fixture(
        "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => k(42) } }",
    );
    let dst = MirLocal(body.locals.len() as u32);
    body.locals.push(MirLocalDecl {
        ty: Type::Scalar(crate::ScalarType::I64),
        source: CoreId(u32::MAX),
    });
    let mut inserted = false;
    for block in &mut body.blocks {
        if let Some((offset, src)) =
            block
                .instructions
                .iter()
                .enumerate()
                .find_map(|(offset, op)| {
                    if let RuntimeOperation::CallIndirect { arguments, .. } = op {
                        Some((offset, arguments[0]))
                    } else {
                        None
                    }
                })
        {
            block
                .instructions
                .insert(offset + 1, RuntimeOperation::Copy { dst, src });
            inserted = true;
            break;
        }
    }
    assert!(inserted);
    body.frame = body.derive_frame().unwrap();
    assert!(body.validate().unwrap_err().contains("dead/uninitialized"));
}

#[test]
fn runtime_saved_frame_excludes_handed_off_effect_owners() {
    let mut body = fixture(PERFORM);
    let argument = body
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|op| {
            if let RuntimeOperation::Perform { arguments, .. } = op {
                Some(arguments[0])
            } else {
                None
            }
        })
        .unwrap();
    let owners = body.control.cleanup_owners.get_or_insert_with(Vec::new);
    if !owners.contains(&argument) {
        owners.push(argument);
    }
    body.frame = body.derive_frame().unwrap();
    body.validate().unwrap();
    let site = body
        .frame
        .transfers
        .iter_mut()
        .find(|site| matches!(site.kind, RuntimeTransferKind::Perform(_)))
        .unwrap();
    assert!(!site.retained.contains(&argument));
    site.retained.push(argument);
    assert!(body.validate().unwrap_err().contains("transfer inventory"));
}

#[test]
fn runtime_requires_an_explicit_leave_handler_depth() {
    let mut body = fixture("pub fn main() -> i64 { label done { transfer done 42 } }");
    assert!(!body.control.leave_handler_depths.is_empty());
    body.control.leave_handler_depths.clear();
    assert!(
        body.validate()
            .unwrap_err()
            .contains("retained-handler contract")
    );
}

#[test]
fn runtime_array_cleanup_is_an_explicit_loop_with_a_private_counter() {
    let body = fixture("pub fn main(value: Array<() -> i64>) -> { let owned = move value; () }");
    let operations = body
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    assert!(
        operations
            .iter()
            .any(|op| matches!(op, RuntimeOperation::ArrayLen { .. }))
    );
    assert!(
        operations
            .iter()
            .any(|op| matches!(op, RuntimeOperation::ArrayElementIsInitialized { .. }))
    );
    assert!(
        operations
            .iter()
            .any(|op| matches!(op, RuntimeOperation::TakeArrayElement { .. }))
    );
    let counter = operations
        .iter()
        .find_map(|op| {
            if let RuntimeOperation::StoreUsize { dst, .. } = op {
                Some(*dst)
            } else {
                None
            }
        })
        .unwrap();
    assert_eq!(
        body.frame.slots[counter.0 as usize].class,
        RuntimeSlotClass::Counter
    );
    assert!(
        !body
            .control
            .source_storage
            .binding_locals
            .contains(&Some(counter))
    );
    let mut forged = body.clone();
    forged.frame.slots[counter.0 as usize].class = RuntimeSlotClass::Temporary;
    assert!(
        forged
            .validate()
            .unwrap_err()
            .contains("transfer inventory")
    );
}

#[test]
fn runtime_array_storage_rejects_a_forged_index_type() {
    let mut body =
        fixture("pub fn main(value: Array<() -> i64>) -> { let owned = move value; () }");
    let array = body.parameters[0];
    for operation in body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
    {
        if let RuntimeOperation::TakeArrayElement { index, .. } = operation {
            *index = array;
            break;
        }
    }
    body.frame = body.derive_frame().unwrap();
    assert!(body.validate().unwrap_err().contains("array index"));
}

#[test]
fn runtime_prepares_an_independent_copy_argument() {
    let body = fixture("pub fn main(action: (i64) -> i64, value: i64) -> i64 { action(value) }");
    let argument = body
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|op| {
            if let RuntimeOperation::CallIndirect { arguments, .. } = op {
                Some(arguments[0])
            } else {
                None
            }
        })
        .unwrap();
    let value = body.parameters[1];
    assert_ne!(argument, value);
    assert!(body.blocks.iter().flat_map(|block| &block.instructions)
        .any(|op| matches!(op, RuntimeOperation::Copy { dst, src } if *dst == argument && *src == value)));
}

#[test]
fn runtime_rejects_reading_a_consumed_call_argument() {
    let mut body =
        fixture("pub fn main(action: (i64) -> i64, value: i64) -> i64 { action(value) }");
    let dst = MirLocal(body.locals.len() as u32);
    body.locals.push(MirLocalDecl {
        ty: Type::Scalar(crate::ScalarType::I64),
        source: CoreId(u32::MAX),
    });
    for block in &mut body.blocks {
        if let Some((offset, argument)) =
            block
                .instructions
                .iter()
                .enumerate()
                .find_map(|(offset, op)| {
                    if let RuntimeOperation::CallIndirect { arguments, .. } = op {
                        Some((offset, arguments[0]))
                    } else {
                        None
                    }
                })
        {
            block
                .instructions
                .insert(offset + 1, RuntimeOperation::Copy { dst, src: argument });
            break;
        }
    }
    body.frame = body.derive_frame().unwrap();
    assert!(body.validate().unwrap_err().contains("dead/uninitialized"));
}

#[test]
fn runtime_has_closed_storage_and_invocation_contracts() {
    let body = fixture(CALL);
    assert_eq!(body.frame.slots.len(), body.locals.len());
    assert_eq!(body.frame.invocation_parameters.len(), 1);
    let invocation = body
        .frame
        .transfers
        .iter()
        .find(|transfer| matches!(transfer.kind, RuntimeTransferKind::IndirectCall))
        .unwrap();
    assert_eq!(invocation.arguments[0].passing, RuntimePassing::Receiver);
    assert!(
        body.frame
            .transfers
            .iter()
            .any(|site| matches!(site.kind, RuntimeTransferKind::IndirectCall))
    );
    assert!(
        body.frame
            .transfers
            .iter()
            .any(|site| matches!(site.kind, RuntimeTransferKind::Return))
    );
}
#[test]
fn runtime_rejects_a_missing_suspension_contract() {
    let mut body = fixture(CALL);
    body.frame
        .transfers
        .retain(|site| !matches!(site.kind, RuntimeTransferKind::IndirectCall));
    assert!(body.validate().unwrap_err().contains("transfer inventory"));
}
#[test]
fn runtime_rejects_forged_retained_owner_inventory() {
    let mut body = fixture(CALL);
    let site = body
        .frame
        .transfers
        .iter_mut()
        .find(|site| matches!(site.kind, RuntimeTransferKind::IndirectCall))
        .unwrap();
    assert!(!site.retained.is_empty());
    site.retained.clear();
    assert!(body.validate().unwrap_err().contains("transfer inventory"));
}
#[test]
fn runtime_rejects_forged_cancellation_cleanup() {
    let mut body = fixture(CALL);
    let site = body
        .frame
        .transfers
        .iter_mut()
        .find(|site| matches!(site.kind, RuntimeTransferKind::IndirectCall))
        .unwrap();
    assert!(!site.cancellation.is_empty());
    site.cancellation.clear();
    assert!(body.validate().unwrap_err().contains("transfer inventory"));
}
#[test]
fn runtime_rejects_a_forged_argument_passing_mode() {
    let mut body = fixture(CALL);
    let site = body
        .frame
        .transfers
        .iter_mut()
        .find(|site| matches!(site.kind, RuntimeTransferKind::IndirectCall))
        .unwrap();
    site.arguments[0].passing = RuntimePassing::Unique;
    assert!(body.validate().unwrap_err().contains("transfer inventory"));
}
#[test]
fn runtime_rejects_a_forged_capture_prefix() {
    let mut body = fixture(CALL);
    body.frame.capture_parameters.push(body.parameters[0]);
    assert!(body.validate().unwrap_err().contains("transfer inventory"));
}
#[test]
fn runtime_rejects_a_changed_storage_class() {
    let mut body = fixture(CALL);
    body.frame.slots[0].class = RuntimeSlotClass::Flag;
    assert!(body.validate().unwrap_err().contains("transfer inventory"));
}
#[test]
fn runtime_rejects_deferred_atomic_inputs() {
    assert!(
        RuntimeOperation::from_atomic(MirInstruction::DeferredLiteral {
            dst: MirLocal(0),
            text: "42".into()
        })
        .is_err()
    );
    assert!(RuntimeOperation::from_atomic(MirInstruction::Drop { local: MirLocal(0) }).is_err());
}
#[test]
fn runtime_checks_operand_slots_before_inventory() {
    let mut body = fixture(CALL);
    for operation in body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
    {
        if let RuntimeOperation::CallIndirect { callee, .. } = operation {
            *callee = MirLocal(u32::MAX);
            break;
        }
    }
    assert!(body.validate().unwrap_err().contains("invalid local"));
}
#[test]
fn runtime_rejects_an_unresolved_storage_type() {
    let mut body = fixture("pub fn main() -> i64 { 42 }");
    body.locals[0].ty = Type::Error;
    assert!(body.validate().is_err());
}
