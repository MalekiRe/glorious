use grandiose_stage0::control_mir::{ControlMir, ControlTerminator};
use grandiose_stage0::evaluation_mir::EvaluationMir;
use grandiose_stage0::ownership_mir::{
    OwnerDisposition, OwnerId, OwnerKind, OwnershipMir, OwnershipOperation, ValueTransfer,
};
use grandiose_stage0::*;

fn ownership(source: &str) -> (OwnershipMir, TypedBody) {
    let package = PackageKey("ownership-mir@0.1.0".into());
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
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    let control = ControlMir::lower(&EvaluationMir::lower(definition.key, &core).unwrap()).unwrap();
    (
        OwnershipMir::lower(control, &flow, Some(&signatures)).unwrap(),
        core,
    )
}

#[test]
fn suspended_inventory_contains_unread_owners_but_not_future_bindings() {
    let (mir, core) = ownership(
        "fn identity(value: i64) -> i64 { value } pub fn main(input: i64) -> i64 { let before = 1; let after = identity(input); after }",
    );
    let binding = |name: &str| {
        let expression = core.expressions.iter().position(|expression| matches!(&expression.kind, CoreKind::Let { name: actual, .. } if actual == name)).unwrap();
        let value = mir.source_bindings()[&PlaceBindingOrigin::Let {
            expression: CoreId(expression as u32),
        }];
        OwnerId(value.0)
    };
    let call = mir
        .blocks()
        .iter()
        .find(|block| matches!(block.terminator.control, ControlTerminator::Invoke { .. }))
        .unwrap();
    assert!(
        call.terminator
            .dispositions
            .contains(&(binding("before"), OwnerDisposition::Suspend))
    );
    assert!(
        !call
            .terminator
            .dispositions
            .iter()
            .any(|(owner, _)| *owner == binding("after"))
    );
}

#[test]
fn a_copied_call_argument_preserves_the_original_suspended_owner() {
    let (mir, _) = ownership(
        "fn identity(value: i64) -> i64 { value } pub fn main(input: i64) -> i64 { identity(input); input }",
    );
    let parameter = OwnerId(mir.parameters()[0].0);
    let call = mir
        .blocks()
        .iter()
        .find(|block| matches!(block.terminator.control, ControlTerminator::Invoke { .. }))
        .unwrap();
    assert!(
        call.terminator
            .dispositions
            .contains(&(parameter, OwnerDisposition::Suspend))
    );
    assert!(
        !call
            .terminator
            .dispositions
            .contains(&(parameter, OwnerDisposition::Transfer))
    );
}

#[test]
fn a_moved_call_argument_acquires_then_transfers_the_owner() {
    let (mir, _) = ownership(
        "pub struct Ticket {} impl Use<[0, 1]> for Ticket {} fn consume(ticket: Ticket) -> i64 { 42 } pub fn main(ticket: Ticket) -> i64 { consume(ticket) }",
    );
    let parameter = OwnerId(mir.parameters()[0].0);
    let acquired = mir.blocks().iter().flat_map(|block| &block.instructions)
        .find_map(|instruction| match instruction.operation {
            OwnershipOperation::Transfer { value, mode: ValueTransfer::Move }
                if mir.owners()[value.0 as usize].kind == OwnerKind::View => Some(OwnerId(instruction.destination.0)),
            _ => None,
        }).expect("the argument must move out of its source view before invocation");
    let call = mir
        .blocks()
        .iter()
        .find(|block| matches!(block.terminator.control, ControlTerminator::Invoke { .. }))
        .unwrap();
    assert!(
        call.terminator
            .dispositions
            .contains(&(acquired, OwnerDisposition::Transfer))
    );
    assert!(
        !call
            .terminator
            .dispositions
            .contains(&(parameter, OwnerDisposition::Suspend))
    );
    assert!(!call.terminator.dispositions.contains(&(parameter, OwnerDisposition::Transfer)));
    assert!(mir.blocks().iter().flat_map(|block| &block.instructions).all(|instruction|
        match &instruction.operation {
            OwnershipOperation::ExitScope { owners, .. } => !owners.contains(&parameter),
            _ => true,
        }));
}

#[test]
fn scope_cleanup_includes_unnamed_initialized_temporaries() {
    let (mir, _) = ownership("pub fn main() -> i64 { let value = 1; 42 }");
    let cleanup = mir
        .blocks()
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match &instruction.operation {
            OwnershipOperation::ExitScope { owners, .. } => Some(owners),
            _ => None,
        })
        .unwrap();
    assert!(
        cleanup
            .iter()
            .any(|id| mir.owners()[id.0 as usize].kind == OwnerKind::Binding)
    );
    assert!(
        cleanup
            .iter()
            .any(|id| mir.owners()[id.0 as usize].kind == OwnerKind::Temporary)
    );
    assert!(
        cleanup
            .iter()
            .all(|id| mir.owners()[id.0 as usize].kind != OwnerKind::View)
    );
}

#[test]
fn returning_an_owned_parameter_moves_it_before_scope_cleanup() {
    let (mir, _) = ownership(
        "pub struct Ticket {} impl Use<[0, 1]> for Ticket {} pub fn main(ticket: Ticket) -> Ticket { ticket }",
    );
    let parameter = OwnerId(mir.parameters()[0].0);
    let (mode, owners) = mir
        .blocks()
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match &instruction.operation {
            OwnershipOperation::ExitScope { mode, owners, .. } => Some((*mode, owners)),
            _ => None,
        })
        .unwrap();
    assert_eq!(mode, ValueTransfer::Move);
    assert!(!owners.contains(&parameter));
}

#[test]
fn aggregate_fields_have_explicit_owned_transfer_modes() {
    let (mir, _) = ownership(
        "pub struct Ticket {} impl Use<[0, 1]> for Ticket {} pub fn main(ticket: Ticket) -> (Ticket, i64) { (ticket, 42) }",
    );
    let fields = mir
        .blocks()
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match &instruction.operation {
            OwnershipOperation::Construct { fields, .. } => Some(fields),
            _ => None,
        })
        .unwrap();
    assert_eq!(fields[0].mode, ValueTransfer::Move);
    // The literal already produced an owner. It is transferred, unlike a
    // read of an independently live duplicable place.
    assert_eq!(fields[1].mode, ValueTransfer::Move);
    let parameter = OwnerId(mir.parameters()[0].0);
    assert!(
        mir.blocks()
            .iter()
            .flat_map(|block| &block.instructions)
            .all(|instruction| match &instruction.operation {
                OwnershipOperation::ExitScope { owners, .. } => !owners.contains(&parameter),
                _ => true,
            })
    );
}
