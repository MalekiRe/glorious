//! Source-driven conformance contract for the eventual executable
//! source-storage MIR representation.
//!
//! `source_storage_cleanup.rs` tests hostile hand-built MIR.  This fixture
//! instead starts with ordinary source and checks that every lexical binding
//! class reaches frozen MIR with enough identity and lifecycle information to
//! become executable `StorageLive`/initialization/drop-flag/`StorageDead`
//! statements.  It intentionally remains red while payload and completion
//! bindings are represented only by side-table events rather than executable
//! storage locals.

mod support;

use grandiose_stage0::{
    MirLowering, MirStorageEventKind, PlaceBindingOrigin,
    PlaceFlow, TypedBody,
};
use std::collections::BTreeSet;

fn lower_main(source: &str) -> (TypedBody, PlaceFlow, grandiose_stage0::MirLowering) {
    let (definition, core, signatures) = support::frontend("source-storage-lowering@0.1.0", source, "main");
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        definition, &core, &flow, &Default::default(), Some(&signatures));
    (core, flow, lowered)
}

#[test]
fn borrowed_rvalues_retain_exact_storage_identity_through_mir() {
    let (core, flow, lowered) = lower_main("pub fn main() -> i64 { let value = &42; *value }");
    let binding = flow.bindings.iter().find(|binding|
        matches!(binding.origin, PlaceBindingOrigin::Temporary { .. }))
        .expect("the borrowed rvalue owns frozen source storage");
    let PlaceBindingOrigin::Temporary { expression } = binding.origin else { unreachable!() };
    assert_eq!(core.expression(expression).ty, grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::I64));
    let mir = lowered.function.unwrap_or_else(|| panic!("{:#?}", lowered.diagnostics));
    let local = mir.control.source_storage.binding_locals[binding.id.0 as usize]
        .expect("temporary identity must map to its actual MIR resident");
    assert_eq!(mir.locals[local.0 as usize].ty, core.expression(expression).ty);
    assert!(mir.blocks.iter().flat_map(|block| &block.instructions).any(|instruction|
        matches!(instruction, grandiose_stage0::MirInstruction::Borrow { src, .. } if *src == local)),
        "the borrow must address the frozen temporary, not a Unit lifecycle marker");
    mir.validate().unwrap();
}

/// The current side table is already useful evidence: normal source lowering
/// must preserve lexical origins, event order, and partial-move identities
/// before the implementation replaces this representation with executable
/// statements.
#[test]
fn source_lowering_preserves_typed_storage_side_table_for_ordinary_lexical_exit() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64; }
        pub struct Pair { left: i64, right: i64 }

        pub fn main(seed: i64) -> i64 {
            label done {
                let seed = seed + 1;
                let pair = Pair { left: 1, right: 2 };
                move pair.left;
                handle Ask::ask() {
                    Ask::ask() => transfer done pair.right + seed
                }
            }
        }
    "#;
    let (_core, flow, lowered) = lower_main(source);
    let mir = lowered
        .function
        .unwrap_or_else(|| panic!("ordinary source must lower: {:#?}", lowered.diagnostics));
    mir.validate()
        .unwrap_or_else(|error| panic!("frozen source MIR must validate: {error}\n{mir:#?}"));

    assert!(
        mir.control
            .move_paths
            .bindings
            .iter()
            .any(|binding| matches!(binding.origin, PlaceBindingOrigin::Parameter { .. }))
            && mir
                .control
                .move_paths
                .bindings
                .iter()
                .any(|binding| matches!(binding.origin, PlaceBindingOrigin::Let { .. })),
        "ordinary parameter/let owners lost Typed Core provenance: {mir:#?}"
    );
    assert!(
        mir.control.source_storage.scopes.iter().all(|scope| {
            let split = scope
                .events
                .iter()
                .position(|event| event.kind == MirStorageEventKind::Dead)
                .unwrap_or(scope.events.len());
            scope.events[..split]
                .iter()
                .all(|event| event.kind == MirStorageEventKind::Live)
                && scope.events[split..]
                    .iter()
                    .all(|event| event.kind == MirStorageEventKind::Dead)
        }),
        "source lowering must preserve live-forward/dead-reverse lexical events"
    );
    assert!(
        flow.move_paths
            .iter()
            .any(|path| path.parent.is_some() && path.field == Some(0)),
        "the partial move must survive source lowering as a typed path even after lexical cleanup: {flow:#?}"
    );
}

/// Parameters, shadowing lets, a partially moved aggregate, a closure capture,
/// handler payload/resumption binders, a completion binder, and a non-local
/// `Leave` all require addressable lifecycle storage.  The final MIR must be
/// able to emit checked statements for each rather than merely carrying a
/// lexical side-table record.
///
/// This is deliberately red until the source-storage lowering slice gives
/// every binding an executable local (or an equally explicit payload-storage
/// instruction) and derives its live/dead/drop-flag transitions from the
/// typed event stream.
#[test]
fn source_lowering_requires_executable_storage_for_payload_and_completion_bindings() {
    let source = r#"
        effect Ask { [1,1] ask(payload: i64) -> i64; }
        pub struct Pair { left: Text, right: i64 }

        pub fn main(seed: i64, incoming: Pair) -> i64 {
            label done {
                let seed = seed + 1;
                let pair = Pair { left: "owned", right: incoming.right };
                move pair.left;
                handle Ask::ask(seed) {
                    completed => transfer done completed + pair.right,
                    Ask::ask(payload) with resume => resume(payload)
                }
            }
        }
    "#;
    let (_core, flow, lowered) = lower_main(source);
    let flow_origins = flow
        .bindings
        .iter()
        .map(|binding| binding.origin.clone())
        .collect::<BTreeSet<_>>();
    assert!(
        flow_origins
            .iter()
            .any(|origin| matches!(origin, PlaceBindingOrigin::Parameter { .. }))
            && flow_origins
                .iter()
                .any(|origin| matches!(origin, PlaceBindingOrigin::Let { .. }))
            && flow_origins
                .iter()
                .any(|origin| matches!(origin, PlaceBindingOrigin::HandlerBinder { .. }))
            && flow_origins
                .iter()
                .any(|origin| matches!(origin, PlaceBindingOrigin::HandlerResumption { .. }))
            && flow_origins
                .iter()
                .any(|origin| matches!(origin, PlaceBindingOrigin::CompletionBinder { .. })),
        "fixture must preserve every source binding provenance into PlaceFlow: {flow_origins:#?}"
    );
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "the handler/completion source shape must lower: {:#?}",
            lowered.diagnostics
        )
    });
    mir.validate()
        .unwrap_or_else(|error| panic!("frozen source MIR must validate: {error}\n{mir:#?}"));

    let origins = mir
        .control
        .move_paths
        .bindings
        .iter()
        .map(|binding| binding.origin.clone())
        .collect::<BTreeSet<_>>();
    assert!(
        origins
            .iter()
            .any(|origin| matches!(origin, PlaceBindingOrigin::Parameter { .. }))
            && origins
                .iter()
                .any(|origin| matches!(origin, PlaceBindingOrigin::Let { .. }))
            && origins
                .iter()
                .any(|origin| matches!(origin, PlaceBindingOrigin::HandlerBinder { .. }))
            && origins
                .iter()
                .any(|origin| matches!(origin, PlaceBindingOrigin::HandlerResumption { .. }))
            && origins
                .iter()
                .any(|origin| matches!(origin, PlaceBindingOrigin::CompletionBinder { .. })),
        "fixture must exercise every source binding provenance: {origins:#?}"
    );

    assert_eq!(
        mir.control.source_storage.binding_scopes.len(),
        mir.control.move_paths.bindings.len(),
        "every frozen source binding needs one lexical storage owner"
    );
    assert!(
        mir.control.source_storage.scopes.iter().all(|scope| {
            let split = scope
                .events
                .iter()
                .position(|event| event.kind == MirStorageEventKind::Dead)
                .unwrap_or(scope.events.len());
            scope.events[..split]
                .iter()
                .all(|event| event.kind == MirStorageEventKind::Live)
                && scope.events[split..]
                    .iter()
                    .all(|event| event.kind == MirStorageEventKind::Dead)
        }),
        "source lowering must preserve live-forward/dead-reverse lexical events"
    );
    assert!(
        flow.move_paths
            .iter()
            .any(|path| path.parent.is_some() && path.field == Some(0)),
        "the partial move must survive source lowering as a typed path: {flow:#?}"
    );

    assert!(
        mir.control
            .source_storage
            .binding_locals
            .iter()
            .all(Option::is_some),
        "source lowering still erases payload/completion storage instead of emitting executable lifecycle locals: {:#?}",
        mir.control.source_storage
    );
}

/// Captured outer storage and typed closure parameters need the same lifecycle
/// treatment as ordinary locals.  The lifted function cannot rely on the
/// parent function's addressable slot after the enclosing handler or label
/// exits, so lowering must make both the capture and the child parameter
/// explicit storage owners.
///
/// This is red while lifted closure lowering is absent for this source shape.
#[test]
fn source_lowering_requires_lifecycle_storage_for_lifted_closure_bindings() {
    let source = r#"
        effect Ask { [1,1] ask(payload: i64) -> i64; }

        pub fn main(seed: i64) -> i64 {
            label done {
                let seed = seed + 1;
                handle Ask::ask(seed) {
                    Ask::ask(payload) with resume => {
                        let delayed = (offset: i64) -> i64 { payload + offset + seed };
                        transfer done delayed(resume(1))
                    }
                }
            }
        }
    "#;
    let (_core, _flow, lowered) = lower_main(source);
    let main = lowered.function.unwrap_or_else(|| {
        panic!(
            "capturing closure source must lower to a parent plus lifted callable: {:#?}",
            lowered.diagnostics
        )
    });
    assert!(
        !lowered.lifted.is_empty(),
        "closure lowering must publish a child MIR body: {main:#?}"
    );
    for function in std::iter::once(&main).chain(lowered.lifted.values()) {
        function.validate().unwrap_or_else(|error| {
            panic!("closure storage body must validate: {error}\n{function:#?}")
        });
        assert!(
            function
                .control
                .source_storage
                .binding_locals
                .iter()
                .all(Option::is_some),
            "captured/parameter storage cannot be implicit in a lifted body: {function:#?}"
        );
    }
}

/// Lifted closures cannot inherit their parent's PlaceFlow table: captures,
/// invocation parameters, and child lets have a fresh ABI-local identity
/// space. An assignment inside the child proves that its table is populated
/// and that its executable storage mapping names the actual store target.
#[test]
fn lifted_closure_assignment_freezes_a_nonvacuous_child_storage_graph() {
    let source = r#"
        pub fn main(seed: i64) -> i64 {
            let delayed = (input: i64) -> i64 {
                let mut value = input;
                value = seed + 1;
                value
            };
            delayed(0)
        }
    "#;
    let (_core, _flow, lowered) = lower_main(source);
    let child = lowered
        .lifted
        .values()
        .find(|function| {
            function.blocks.iter().flat_map(|block| &block.instructions).any(
                |instruction| matches!(instruction, grandiose_stage0::MirInstruction::Store { .. }),
            )
        })
        .unwrap_or_else(|| {
            panic!(
                "assigned closure must publish a lifted MIR body: {:#?}",
                lowered.diagnostics
            )
        });
    child.validate().unwrap_or_else(|error| {
        panic!("lifted assigned closure must validate: {error}\n{child:#?}")
    });
    assert!(
        !child.control.move_paths.bindings.is_empty()
            && child.control.source_storage.binding_locals.len()
                == child.control.move_paths.bindings.len(),
        "lifted child must publish its own nonempty dense storage graph: {child:#?}"
    );
    let stores = child
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction {
            grandiose_stage0::MirInstruction::Store { dst, .. } => Some(*dst),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !stores.is_empty()
            && stores.iter().all(|store| {
                child
                    .control
                    .source_storage
                    .binding_locals
                    .iter()
                    .any(|local| *local == Some(*store))
            }),
        "lifted assignment must target a child-owned mapped storage slot: {child:#?}"
    );
}
