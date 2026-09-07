use super::*;
use crate::*;

pub(crate) fn fixture(source: &str) -> CleanupMir {
    let package = PackageKey("cleanup-validator@0.1.0".into());
    let lexed = LexedFile::lex(FileKey::new(&package, "src/main.glorious"), source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let syntax = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &syntax,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze_with_interface(&core, &signatures);
    let (ownership, result) =
        ownership_mir::OwnershipMir::from_typed(definition.key, &core, &flow, Some(&signatures))
            .unwrap();
    let key = InstanceKey::new(definition.key, &[], vec![]).unwrap();
    let specialized =
        specialized_mir::SpecializedMir::lower(&ownership, &result, key, &signatures, None)
            .unwrap();
    let mut planner = crate::destruction::Planner::new(&signatures);
    fn discover(
        body: &specialized_mir::SpecializedMir,
        planner: &mut crate::destruction::Planner<'_>,
    ) {
        for value in body.values() {
            planner.discover(&value.ty).unwrap();
        }
        planner.discover(body.result()).unwrap();
        for closure in body.closures() {
            discover(&closure.body, planner);
        }
    }
    discover(&specialized, &mut planner);
    let plans = std::sync::Arc::new(
        planner
            .frozen_plans()
            .into_iter()
            .map(|(key, plan)| (DefKey(key.fingerprint()), plan))
            .collect(),
    );
    CleanupMir::lower(&specialized, &signatures, &plans).unwrap()
}

const OWNED: &str = "pub fn main(value: () -> i64) -> { let owned = move value; () }";

#[test]
fn cleanup_owns_concrete_destroy_and_complete_frame_plans() {
    let body = fixture(OWNED);
    assert!(body.plans.iter().any(|plan| {
        plan.actions
            .iter()
            .any(|action| matches!(action, CleanupAction::Destroy { .. }))
    }));
    assert!(!body.plans[body.frame_cleanup.0 as usize].actions.is_empty());
    assert!(
        body.blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(
                instruction.operation,
                CleanupOperation::RunCleanup { .. }
            ))
    );
}

#[test]
fn cleanup_rejects_an_omitted_move_flag_clear() {
    let mut body = fixture(OWNED);
    let instruction = body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .find(|instruction| !instruction.flags.before.is_empty())
        .unwrap();
    instruction.flags.before.clear();
    assert!(body.validate().unwrap_err().0.contains("flag transitions"));
}

#[test]
fn cleanup_rejects_an_omitted_initialization_flag_write() {
    let mut body = fixture(OWNED);
    let instruction = body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .find(|instruction| !instruction.flags.after.is_empty())
        .unwrap();
    instruction.flags.after.clear();
    assert!(body.validate().unwrap_err().0.contains("flag transitions"));
}

#[test]
fn cleanup_rejects_a_forged_concrete_destructor() {
    let mut body = fixture(OWNED);
    let action = body
        .plans
        .iter_mut()
        .flat_map(|plan| &mut plan.actions)
        .find(|action| matches!(action, CleanupAction::Destroy { .. }))
        .unwrap();
    let CleanupAction::Destroy { destructor, .. } = action else {
        unreachable!()
    };
    *destructor = DefKey(Digest::of_bytes(b"not-a-destructor"));
    assert!(body.validate().unwrap_err().0.contains("destroy target"));
}

#[test]
fn cleanup_rejects_a_missing_cancellation_owner() {
    let mut body = fixture(OWNED);
    body.frame_cleanup = CleanupPlanId(0);
    assert!(
        body.validate()
            .unwrap_err()
            .0
            .contains("complete reverse owner inventory")
    );
}

#[test]
fn cleanup_rejects_return_bypassing_its_plan() {
    let mut body = fixture(OWNED);
    let terminator = body
        .blocks
        .iter_mut()
        .map(|block| &mut block.terminator)
        .find(|term| matches!(term.control, CleanupControl::Return(_)))
        .unwrap();
    terminator.cleanup = CleanupPlanId(0);
    assert!(body.validate().unwrap_err().0.contains("return bypasses"));
}

#[test]
fn cleanup_protects_the_transferred_return_owner() {
    let body = fixture("pub fn main(value: () -> i64) -> () -> i64 { move value }");
    let term = body
        .blocks
        .iter()
        .map(|block| &block.terminator)
        .find(|term| matches!(term.control, CleanupControl::Return(_)))
        .unwrap();
    let plan = &body.plans[term.cleanup.0 as usize];
    assert!(!plan.protected.is_empty());
    for action in &plan.actions {
        if let CleanupAction::Destroy { flag, .. } = action {
            assert!(
                !plan
                    .protected
                    .contains(&body.flags[flag.0 as usize].place.root())
            );
        }
    }
}

#[test]
fn cleanup_seals_capture_destruction_separately_from_invocation() {
    let body =
        fixture("pub fn main(value: () -> i64) -> { let action = move(value) { value() }; () }");
    let closure = &body.closures[0];
    assert!(closure.destructor.is_some());
    let plan = &closure.body.plans[closure.body.frame_cleanup.0 as usize];
    let captures = closure.environment.captures.len();
    assert!(plan.actions.iter().all(|action| match action {
        CleanupAction::Destroy { flag, .. } | CleanupAction::StorageDead(flag) =>
            closure.body.flags[flag.0 as usize].place.root().0 as usize >= captures,
        _ => true,
    }));
}

#[test]
fn cleanup_structural_glue_visits_fields_in_reverse_order() {
    let body =
        fixture("pub fn main(value: (() -> i64, () -> i64)) -> { let owned = move value; () }");
    let (definition, plan) = body
        .destruction
        .iter()
        .find(|(_, plan)| matches!(plan.shape, crate::destruction::Shape::Tuple(_)))
        .unwrap();
    let signatures = ElaboratedInterface::default();
    let key = InstanceKey::new(
        DefKey(Digest::of_bytes(b"fixture-glue")),
        &[GenericKind::Type],
        vec![GenericArgument::Type(plan.ty.clone())],
    )
    .unwrap();
    let glue = crate::runtime_mir::destruction::materialize(&key, plan, &signatures).unwrap();
    let _ = definition;
    let fields = glue
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction {
            crate::runtime_mir::RuntimeOperation::TakeProjection { fields, .. } => Some(fields.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(fields, vec![vec![1], vec![0]]);
}

#[test]
fn cleanup_normalizes_associated_fields_before_selecting_destruction() {
    let body = fixture(
        "trait Family { type Item; } impl Family for i64 { type Item = () -> i64; } struct Holder { callback: <i64 as Family>::Item } pub fn main(value: Holder) -> { let owned = move value; () }",
    );
    let fields = body
        .destruction
        .values()
        .find_map(|plan| match &plan.shape {
            crate::destruction::Shape::Nominal { variants, .. } => Some(&variants[0]),
            _ => None,
        })
        .unwrap();
    assert!(matches!(fields[0].ty, Type::Callable { .. }));
    assert!(fields[0].glue.is_some());
}

#[test]
fn cleanup_rejects_an_omitted_environment_capture_drop() {
    let mut body =
        fixture("pub fn main(value: () -> i64) -> { let action = move(value) { value() }; () }");
    body.closures[0].cleanup.clear();
    assert!(
        body.validate()
            .unwrap_err()
            .0
            .contains("reverse owning capture plan")
    );
}

#[test]
fn cleanup_rejects_an_omitted_suspended_owner() {
    let mut body = fixture(
        "effect Ask { [0,1] ask() -> i64; } pub fn main(value: () -> i64) -> i64 / Ask { let answer = Ask::ask(); value() }",
    );
    let terminator = body
        .blocks
        .iter_mut()
        .map(|block| &mut block.terminator)
        .find(|term| {
            matches!(
                term.control,
                CleanupControl::Transfer(ControlTransfer::Perform { .. })
            )
        })
        .unwrap();
    terminator.cancellation = CleanupPlanId(0);
    assert!(
        body.validate()
            .unwrap_err()
            .0
            .contains("exact residual inventory")
    );
}

#[test]
fn cleanup_rejects_lexical_scope_bypassing_its_plan() {
    let mut body = fixture(OWNED);
    let operation = body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .map(|instruction| &mut instruction.operation)
        .find(|operation| matches!(operation, CleanupOperation::RunCleanup { .. }))
        .unwrap();
    let CleanupOperation::RunCleanup { plan, .. } = operation else {
        unreachable!()
    };
    *plan = CleanupPlanId(0);
    assert!(
        body.validate()
            .unwrap_err()
            .0
            .contains("lexical scope cleanup")
    );
}

#[test]
fn cleanup_rejects_replacement_without_old_resident_cleanup() {
    let mut body = fixture(
        "pub fn main(first: () -> i64, second: () -> i64) -> { let slot = move first; slot = second; () }",
    );
    let operation = body
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .map(|instruction| &mut instruction.operation)
        .find(|operation| matches!(operation, CleanupOperation::Replace { .. }))
        .unwrap();
    let CleanupOperation::Replace { cleanup, .. } = operation else {
        unreachable!()
    };
    *cleanup = CleanupPlanId(0);
    assert!(
        body.validate()
            .unwrap_err()
            .0
            .contains("old resident destruction")
    );
}

#[test]
fn cleanup_rejects_cyclic_scope_metadata() {
    let mut body = fixture(OWNED);
    body.scopes[0].parent = Some(ControlScopeId(0));
    assert!(body.validate().unwrap_err().0.contains("scope ancestry"));
}
