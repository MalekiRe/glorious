//! Source-driven assignment storage contracts.
//!
//! These cases deliberately inspect frozen MIR as well as executing the
//! published VM artifact.  A source owner is a mutable addressable slot; a
//! compiler temporary is still ordinary single-write register state.  The
//! distinction must survive initialisation, replacement, move/reinitialise,
//! and closure lifting.

use grandiose_stage0::{
    BodySyntax, CompilationMode, CompilationRequest, CompilerBuildIdentity, DeclarationScan,
    DefinitionIndex, Digest, ElaboratedInterface, FileKey, InterfaceSet, LexedFile, LogicalPath,
    emit_vm, MirCleanupAction, MirFunction, MirInstruction, MirLocal, MirLowering,
    MirTerminator, PackageKey, PlaceBindingOrigin, PlaceFlow, SourceInput, StageZeroCompiler,
    TypedBody, VmInstruction, VmStorageErasureAction, VmStorageErasureWitness,
};
use std::collections::{BTreeMap, BTreeSet};

fn lower_function(source: &str, function: &str) -> (TypedBody, PlaceFlow, MirLowering) {
    let package = PackageKey("source-assignment-lowering@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious")
            .expect("valid logical path")
            .as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some(function))
        .expect("requested function definition");
    let body = BodySyntax::parse(
        &lexed,
        source,
        definition.body.expect("requested function body"),
    );
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let lowered = MirLowering::lower(definition.key, &core, &flow);
    (core, flow, lowered)
}

fn lower_main(source: &str) -> (TypedBody, PlaceFlow, MirLowering) {
    lower_function(source, "main")
}

fn compile_main(source: &str) -> grandiose_stage0::CompilationOutcome {
    let package = PackageKey("source-assignment-lowering@0.1.0".into());
    StageZeroCompiler::new()
        .compile(CompilationRequest {
            build: CompilerBuildIdentity {
                compiler: Digest::of_bytes(b"source-assignment-lowering"),
                language_generation: 1,
                query_generation: 1,
                interface_generation: 1,
                cache_generation: 1,
                bytecode_generation: 1,
                verifier_generation: 1,
            },
            mode: CompilationMode::Build,
            root_package: package.clone(),
            sources: vec![SourceInput::new(
                package,
                LogicalPath::parse("src/main.glorious").expect("valid logical path"),
                source.as_bytes(),
            )],
            target: "stage0-vm".into(),
            semantic_options: BTreeMap::new(),
            codegen_options: BTreeMap::new(),
            capability_manifest: vec![],
            runtime_manifest: None,
        })
        .unwrap_or_else(|error| panic!("source assignment must compile: {error:#?}"))
}

fn source_slots(function: &MirFunction) -> BTreeSet<MirLocal> {
    function
        .control
        .source_storage
        .binding_locals
        .iter()
        .flatten()
        .copied()
        .collect()
}

fn let_slot(function: &MirFunction) -> MirLocal {
    function
        .control
        .move_paths
        .bindings
        .iter()
        .enumerate()
        .find_map(|(binding, data)| {
            matches!(data.origin, PlaceBindingOrigin::Let { .. })
                .then(|| function.control.source_storage.binding_locals[binding])
                .flatten()
        })
        .expect("source let must retain an executable addressable slot")
}

fn instructions(function: &MirFunction) -> impl Iterator<Item = &MirInstruction> {
    function
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
}

fn assert_only_source_slots_are_stored(function: &MirFunction) {
    let source_slots = source_slots(function);
    let stores = instructions(function)
        .filter_map(|instruction| match instruction {
            MirInstruction::Store { dst, src } => Some((*dst, *src)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !stores.is_empty(),
        "fixture must lower a source Store: {function:#?}"
    );
    assert!(
        stores
            .iter()
            .all(|(destination, _)| source_slots.contains(destination)),
        "Store is reserved for source-addressable slots; an SSA temporary needs an ordinary definition: {function:#?}"
    );
}

/// A `let` initializer is the first store into a `Place` slot.  Its operand
/// must first be materialized in an ordinary temporary, then stored only
/// after the matching `StorageLive`; treating the `let` slot itself as an SSA
/// definition loses the source-storage lifecycle before assignment occurs.
#[test]
fn source_let_initializer_lowers_as_live_temporary_then_first_store() {
    let source = "pub fn main() -> i64 { let value = 41; value }";
    let (_core, _flow, lowered) = lower_main(source);
    let function = lowered
        .function
        .unwrap_or_else(|| panic!("source initializer must lower: {:#?}", lowered.diagnostics));
    function.validate().unwrap_or_else(|error| {
        panic!("source initializer MIR must validate: {error}\n{function:#?}")
    });
    let slot = let_slot(&function);
    let source_slots = source_slots(&function);
    let entry = &function.blocks[function.entry.0 as usize];
    let live = entry.instructions.iter().position(|instruction| {
        matches!(instruction, MirInstruction::StorageLive { local, .. } if *local == slot)
    });
    let first_store = entry.instructions.iter().position(
        |instruction| matches!(instruction, MirInstruction::Store { dst, .. } if *dst == slot),
    );
    assert!(
        live.zip(first_store)
            .is_some_and(|(live, store)| live < store),
        "the first store must follow StorageLive for its exact source slot: {function:#?}"
    );
    let (destination, operand) = entry
        .instructions
        .iter()
        .find_map(|instruction| match instruction {
            MirInstruction::Store { dst, src } if *dst == slot => Some((*dst, *src)),
            _ => None,
        })
        .expect("initial source binding must receive Store");
    assert_eq!(destination, slot);
    assert_ne!(
        operand, slot,
        "Store must consume an already-evaluated operand"
    );
    assert!(
        !source_slots.contains(&operand),
        "initializer operand must be an ordinary temporary, not a second source place: {function:#?}"
    );
    assert_only_source_slots_are_stored(&function);
    assert_eq!(
        compile_main(source)
            .artifact
            .expect("source initializer must publish an artifact")
            .run_i64()
            .expect("source initializer must execute"),
        41
    );
}

/// Replacing an initialized source owner is not a generic register write.
/// The old resident must be conditionally destroyed/disarmed before the
/// second Store, while intermediate arithmetic/literal temporaries remain
/// ordinary one-write locals.
#[test]
fn source_assignment_destroys_an_initialized_place_before_overwrite_store() {
    let source = "pub fn main() -> i64 { let value = 1; value = 42; value }";
    let (_core, _flow, lowered) = lower_main(source);
    let function = lowered
        .function
        .unwrap_or_else(|| panic!("source overwrite must lower: {:#?}", lowered.diagnostics));
    function.validate().unwrap_or_else(|error| {
        panic!("source overwrite MIR must validate: {error}\n{function:#?}")
    });
    let slot = let_slot(&function);
    let linear = instructions(&function).collect::<Vec<_>>();
    let stores = linear
        .iter()
        .enumerate()
        .filter_map(|(index, instruction)| match instruction {
            MirInstruction::Store { dst, .. } if *dst == slot => Some(index),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        stores.len() >= 2,
        "initialization and assignment must be distinct stores into one Place slot: {function:#?}"
    );
    assert!(
        linear[stores[0] + 1..stores[1]].iter().any(|instruction| matches!(
            instruction,
            MirInstruction::DestroyIf { local, .. } if *local == slot
        )),
        "an initialized source place must be destroyed/disarmed before replacement Store: {function:#?}"
    );
    let destroy = linear[stores[0] + 1..stores[1]]
        .iter()
        .position(|instruction| {
            matches!(
                instruction,
                MirInstruction::DestroyIf { local, .. } if *local == slot
            )
        })
        .map(|relative| stores[0] + 1 + relative)
        .expect("replacement must have its exact DestroyIf");
    let MirInstruction::DestroyIf { flag, .. } = linear[destroy] else {
        unreachable!("matched DestroyIf")
    };
    assert!(
        linear[..destroy]
            .iter()
            .rev()
            .find_map(|instruction| match instruction {
                MirInstruction::SetDropFlag {
                    flag: candidate,
                    value,
                } if candidate == flag => Some(*value),
                _ => None,
            })
            == Some(true),
        "DestroyIf must observe an armed drop flag for the old initialized resident: {function:#?}"
    );
    assert!(
        linear[destroy + 1..stores[1]]
            .iter()
            .any(|instruction| matches!(
                instruction,
                MirInstruction::SetDropFlag { flag: candidate, value: false } if candidate == flag
            )),
        "DestroyIf must disarm its old resident before replacement Store: {function:#?}"
    );
    assert_only_source_slots_are_stored(&function);
    assert_eq!(
        compile_main(source)
            .artifact
            .expect("source overwrite must publish an artifact")
            .run_i64()
            .expect("source overwrite must execute"),
        42
    );
}

/// A move disarms the resident value but leaves the lexical source slot live.
/// Reassignment therefore reuses the same `Place` with Store and must *not*
/// emit a second destruction between the move and that first reinitializing
/// store.
#[test]
fn source_assignment_reinitializes_a_moved_place_without_destroying_an_empty_slot() {
    let source = "pub struct Token { number: i64 } pub fn main() -> i64 { let value = Token { number: 1 }; move value; value = Token { number: 42 }; value.number }";
    let (_core, _flow, lowered) = lower_main(source);
    let function = lowered.function.unwrap_or_else(|| {
        panic!(
            "move/reinitialize source program must lower: {:#?}",
            lowered.diagnostics
        )
    });
    function.validate().unwrap_or_else(|error| {
        panic!("move/reinitialize MIR must validate: {error}\n{function:#?}")
    });
    let slot = let_slot(&function);
    let linear = instructions(&function).collect::<Vec<_>>();
    let moved = linear
        .iter()
        .position(
            |instruction| matches!(instruction, MirInstruction::Move { src, .. } if *src == slot),
        )
        .expect("source move must consume the addressable slot");
    let reinitialized = linear
        .iter()
        .enumerate()
        .skip(moved + 1)
        .find_map(|(index, instruction)| match instruction {
            MirInstruction::Store { dst, .. } if *dst == slot => Some(index),
            _ => None,
        })
        .expect("assignment after move must Store into the original slot");
    assert!(
        !linear[moved + 1..reinitialized].iter().any(|instruction| matches!(
            instruction,
            MirInstruction::DestroyIf { local, .. } if *local == slot
        )),
        "a moved source owner is already empty; reinitialization must not destroy it again: {function:#?}"
    );
    assert_only_source_slots_are_stored(&function);
    assert_eq!(
        compile_main(source)
            .artifact
            .expect("move/reinitialize source program must publish an artifact")
            .run_i64()
            .expect("move/reinitialize source program must execute"),
        42
    );
}

/// A lifted callable that mutates a captured source owner needs the same
/// addressable-slot contract as its parent.  The capture parameter is an ABI
/// input, so it need not receive a second `StorageLive`, but its Store target
/// must be recorded in the lifted body's own frozen source-storage mapping;
/// a compiler temporary in that body must never become a Store destination.
#[test]
fn lifted_closure_assignment_preserves_a_mapped_addressable_capture_slot() {
    let source = "pub fn main() -> i64 { let value = 40; let outer = () -> i64 { let inner = () -> i64 { value = value + 2; value }; inner() }; outer() }";
    let (_core, _flow, lowered) = lower_main(source);
    let function = lowered
        .function
        .as_ref()
        .unwrap_or_else(|| panic!("capturing source must lower: {:#?}", lowered.diagnostics));
    function
        .validate()
        .unwrap_or_else(|error| panic!("parent closure MIR must validate: {error}\n{function:#?}"));
    assert!(
        !lowered.lifted.is_empty(),
        "nested closure lowering must publish executable child functions: {function:#?}"
    );
    let mut found_mutating_capture = false;
    for child in lowered.lifted.values() {
        child.validate().unwrap_or_else(|error| {
            panic!("lifted closure MIR must validate: {error}\n{child:#?}")
        });
        let source_slots = source_slots(child);
        for instruction in instructions(child) {
            if let MirInstruction::Store { dst, .. } = instruction {
                assert!(
                    source_slots.contains(dst),
                    "a lifted source assignment must Store to a frozen addressable capture slot, never an untracked temporary: {child:#?}"
                );
                // The outer lifted callable also stores its lexical `inner`
                // binding.  Only the nested callable's Store proves the
                // capture-parameter path; distinguish it by the ABI prefix
                // instead of assuming every lifted Store is a capture write.
                found_mutating_capture |= child.parameters[..child.captures as usize].contains(dst);
            }
        }
        assert_only_source_slots_are_stored(child);
    }
    assert!(
        found_mutating_capture,
        "the nested closure fixture must produce a Store in a lifted child body"
    );
    assert_eq!(
        compile_main(source)
            .artifact
            .expect("lifted source assignment must publish an artifact")
            .run_i64()
            .expect("lifted source assignment must execute"),
        42
    );
}

/// Assignment flags are useful only if the lexical exit consumes them.  After
/// a whole move and reinitialization, leaving the label must use the exact
/// frozen source-storage scope, process its owners in reverse initialization
/// order, clear every flag, and end every addressable lifetime with
/// `StorageDead`.  None of those facts may be inferred later from temporary
/// register lifetimes.
#[test]
fn source_assignment_leave_emits_reverse_storage_dead_cleanup_after_move_and_reinit() {
    let source = "pub struct Token { number: i64 } pub fn main() -> i64 { label done { let owner = Token { number: 1 }; move owner; owner = Token { number: 2 }; let later = 40; transfer done owner.number + later } }";
    let (_core, _flow, lowered) = lower_main(source);
    let function = lowered.function.unwrap_or_else(|| {
        panic!(
            "assigned lexical leave must lower: {:#?}",
            lowered.diagnostics
        )
    });
    function.validate().unwrap_or_else(|error| {
        panic!("assigned lexical leave MIR must validate: {error}\n{function:#?}")
    });
    let cleanup = function
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            MirTerminator::Leave { cleanup, .. } => Some(cleanup),
            _ => None,
        })
        .expect("label transfer must remain a MIR Leave");
    assert_ne!(
        cleanup.source_storage_scope, cleanup.target_storage_scope,
        "the lexical label exit must cross the source-storage boundary: {function:#?}"
    );
    let expected = function
        .control
        .source_storage
        .exited_bindings(cleanup.source_storage_scope, cleanup.target_storage_scope)
        .expect("Leave storage scopes must be valid");
    assert!(
        expected.len() >= 2,
        "fixture must exit both the reinitialized owner and later binding: {function:#?}"
    );
    assert_eq!(
        cleanup
            .drop_flags
            .iter()
            .map(|flag| flag.binding)
            .collect::<Vec<_>>(),
        expected,
        "every exited source owner needs exactly one stable cleanup drop flag"
    );
    let terminal = cleanup
        .actions
        .iter()
        .filter_map(|action| match action {
            MirCleanupAction::Drop { binding, .. } | MirCleanupAction::Protect { binding, .. } => {
                Some(*binding)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        terminal, expected,
        "cleanup must process source owners in reverse lexical initialization order"
    );
    for (binding, flag) in expected.iter().zip(&cleanup.drop_flags) {
        let terminal_index = cleanup
            .actions
            .iter()
            .position(|action| {
                matches!(
                    action,
                    MirCleanupAction::Drop { binding: candidate, flag: action_flag }
                        if candidate == binding && *action_flag == flag.id
                )
            })
            .expect("unprotected assigned owner must have conditional drop");
        let clear_index = cleanup
            .actions
            .iter()
            .position(|action| {
                matches!(
                    action,
                    MirCleanupAction::ClearDropFlag { flag: candidate } if *candidate == flag.id
                )
            })
            .expect("cleanup must clear its assignment drop flag");
        let dead_index = cleanup
            .actions
            .iter()
            .position(|action| {
                matches!(
                    action,
                    MirCleanupAction::StorageDead { binding: candidate } if candidate == binding
                )
            })
            .expect("cleanup must emit StorageDead for every exited owner");
        assert!(
            terminal_index < clear_index && clear_index < dead_index,
            "each source owner must be terminally cleaned, then disarmed, then StorageDead: {cleanup:#?}"
        );
    }
    let published = compile_main(source)
        .artifact
        .expect("assigned lexical leave must publish an artifact");
    assert_eq!(
        published
            .run_i64()
            .expect("assigned lexical leave must execute"),
        42
    );
    let artifact = emit_vm(&function)
        .expect("the validated source-storage Leave must lower to a VM artifact");
    let witness = artifact
        .function
        .instructions
        .iter()
        .find_map(|instruction| match instruction {
            VmInstruction::Leave { cleanup, .. } => Some(&cleanup.storage_erasure),
            _ => None,
        })
        .expect("source Leave must retain a VM storage-erasure witness");
    let VmStorageErasureWitness::Verified {
        storages, actions, ..
    } = witness
    else {
        panic!("source-lowered Leave must carry a checked storage witness");
    };
    let mut expected_storage_ids = expected.iter().map(|binding| binding.0).collect::<Vec<_>>();
    expected_storage_ids.sort_unstable();
    assert_eq!(
        storages.iter().map(|storage| storage.binding).collect::<Vec<_>>(),
        expected_storage_ids,
        "VM storage descriptors must canonically preserve every exited source owner"
    );
    assert_eq!(
        storages
            .iter()
            .map(|storage| storage.value_register)
            .collect::<BTreeSet<_>>()
            .len(),
        storages.len(),
        "source owners must retain distinct VM value registers"
    );
    let vm_terminal = actions
        .iter()
        .filter_map(|action| match action {
            VmStorageErasureAction::Destroy { storage }
            | VmStorageErasureAction::Protect { storage, .. } => Some(*storage),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        vm_terminal,
        expected.iter().map(|binding| binding.0).collect::<Vec<_>>(),
        "VM witness must preserve reverse terminal cleanup order from source MIR"
    );
}

/// If a source owner itself is the non-local payload, cleanup has to protect
/// that exact mapped slot.  It may clear the drop flag and end the lexical
/// storage after transfer, but must never emit a Drop action for the payload
/// owner before the label target receives it.
#[test]
fn source_leave_protects_reinitialized_owner_payload_before_storage_dead() {
    let source = "pub struct Token { number: i64 } pub fn main() -> Token { label done { let value = Token { number: 1 }; move value; value = Token { number: 42 }; transfer done value } }";
    let (_core, _flow, lowered) = lower_main(source);
    let function = lowered.function.unwrap_or_else(|| {
        panic!(
            "protected source payload leave must lower: {:#?}",
            lowered.diagnostics
        )
    });
    function.validate().unwrap_or_else(|error| {
        panic!("protected source payload MIR must validate: {error}\n{function:#?}")
    });
    let slot = let_slot(&function);
    let (arguments, cleanup) = function
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            MirTerminator::Leave {
                arguments, cleanup, ..
            } => Some((arguments, cleanup)),
            _ => None,
        })
        .expect("source transfer must remain a MIR Leave");
    assert_eq!(
        arguments,
        &[slot],
        "the transferred source owner must remain the exact protected payload slot: {function:#?}"
    );
    assert_eq!(cleanup.protected_values, vec![slot]);
    let binding = function
        .control
        .source_storage
        .binding_locals
        .iter()
        .position(|local| *local == Some(slot))
        .map(|index| grandiose_stage0::MirPlaceBindingId(index as u32))
        .expect("protected source slot must retain frozen binding provenance");
    assert!(
        cleanup.actions.iter().any(|action| matches!(
            action,
            MirCleanupAction::Protect { binding: candidate, local } if *candidate == binding && *local == slot
        )),
        "cleanup must Protect the payload source owner rather than infer a temporary: {cleanup:#?}"
    );
    assert!(
        !cleanup.actions.iter().any(|action| matches!(
            action,
            MirCleanupAction::Drop { binding: candidate, .. } if *candidate == binding
        )),
        "cleanup must never drop a protected transferred source owner: {cleanup:#?}"
    );
    assert!(
        cleanup.actions.iter().any(|action| matches!(
            action,
            MirCleanupAction::StorageDead { binding: candidate } if *candidate == binding
        )),
        "the transferred source owner still needs an explicit lexical StorageDead: {cleanup:#?}"
    );
}

/// A `Leave` emitted from a handler clause is a separate MIR block from the
/// lexical label body.  It must still consume the label's branded
/// source-storage boundary and preserve a direct source owner as the payload,
/// rather than reconstructing cleanup from the handler block or moving the
/// owner through an untracked temporary.
#[test]
fn handler_leave_protects_a_direct_reinitialized_source_owner_payload() {
    let source = r#"
        pub struct Token { number: i64 }
        effect Ask { [1,1] ask() -> Token; }

        pub fn escape() -> Token {
            label done {
                let owner = Token { number: 1 };
                move owner;
                owner = Token { number: 42 };
                handle Ask::ask() {
                    Ask::ask() => transfer done owner
                }
            }
        }

        pub fn main() -> i64 {
            let token = escape();
            token.number
        }
    "#;
    let (_core, _flow, lowered) = lower_function(source, "escape");
    let function = lowered.function.unwrap_or_else(|| {
        panic!(
            "handler payload leave must lower: {:#?}",
            lowered.diagnostics
        )
    });
    function.validate().unwrap_or_else(|error| {
        panic!("handler payload leave MIR must validate: {error}\n{function:#?}")
    });
    let (arguments, cleanup) = function
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            MirTerminator::Leave {
                arguments, cleanup, ..
            } if !cleanup.actions.is_empty() => Some((arguments, cleanup)),
            _ => None,
        })
        .expect("handler clause transfer must retain executable source cleanup");
    assert_eq!(
        cleanup.protected_values, *arguments,
        "the protected storage payload must exactly match the handler Leave arguments: {cleanup:#?}"
    );
    let protected = cleanup
        .actions
        .iter()
        .filter_map(|action| match action {
            MirCleanupAction::Protect { binding, local } => Some((*binding, *local)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        protected.len(),
        1,
        "only the directly transferred owner may be protected: {cleanup:#?}"
    );
    assert_eq!(protected[0].1, arguments[0]);
    assert!(
        cleanup.actions.iter().any(|action| matches!(
            action,
            MirCleanupAction::StorageDead { binding } if *binding == protected[0].0
        )),
        "the protected owner must still leave lexical source storage"
    );
    assert_eq!(
        compile_main(source)
            .artifact
            .expect("handler payload leave must publish an artifact")
            .run_i64()
            .expect("handler payload leave must execute"),
        42
    );
}
