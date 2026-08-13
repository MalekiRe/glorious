use grandiose_stage0::{
    BodySyntax, CaptureMode, CoreHandlerResumption, CoreKind, DeclarationScan, DefinitionIndex,
    ElaboratedInterface, FileKey, InterfaceSet, LexedFile, LogicalPath, MirInstruction,
    MirLowering, PackageKey, PlaceFlow, TypedBody,
};

#[test]
fn typed_core_elaborates_scoped_locals_and_flat_numeric_operator_chains() {
    let package = PackageKey("core@0.1.0".into());
    let source = "pub fn main() -> i64 { let value = 1; value + 2 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let root = core.expression(core.root);
    assert!(matches!(root.kind, CoreKind::Block(_)));
    assert!(
        core.expressions
            .iter()
            .any(|expression| matches!(expression.kind, CoreKind::Binary { .. }))
    );
}

#[test]
fn typed_core_checks_a_function_body_against_its_declared_result() {
    let package = PackageKey("core@0.1.0".into());
    let source = "pub fn main() -> Text { 1 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4110")
    );
}

#[test]
fn placeflow_rejects_use_after_move_from_typed_core() {
    let package = PackageKey("core@0.1.0".into());
    let source = "pub fn main() -> i64 { let value = 1; move value; value }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001")
    );
}

#[test]
fn typed_core_and_placeflow_lower_to_validated_mir() {
    let package = PackageKey("core@0.1.0".into());
    let source = "pub fn main() -> i64 { let value = 1; value + 2 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    let flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(definition.key, &core, &flow);
    assert!(lowered.diagnostics.is_empty(), "{:#?}", lowered.diagnostics);
    let mir = lowered.function.unwrap();
    assert!(
        mir.entry_block()
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::AddI64 { .. }))
    );
    assert!(mir.validate().is_ok());
}

#[test]
fn typed_closures_become_callable_core_values_with_explicit_capture_modes() {
    let package = PackageKey("core-closure@0.1.0".into());
    let source =
        "pub fn main(value: i64) -> i64 { let add = (extra: i64) -> i64 { value + extra }; 1 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let Some(CoreKind::Closure {
        parameters,
        captures,
        ..
    }) = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            closure @ CoreKind::Closure { .. } => Some(closure),
            _ => None,
        })
    else {
        panic!("typed closure was not elaborated")
    };
    assert_eq!(parameters[0].0, "extra");
    assert_eq!(captures.len(), 1);
    assert_eq!(captures[0].name, "value");
    assert_eq!(captures[0].mode, CaptureMode::SharedBorrow);
}

#[test]
fn placeflow_applies_a_closure_move_capture_when_the_closure_is_created() {
    let package = PackageKey("core-closure-move@0.1.0".into());
    let source = "pub fn main(value: i64) -> i64 { let consume = (extra: i64) -> i64 { move value + extra }; value }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "{:#?}",
        flow.diagnostics
    );
}

#[test]
fn contextual_blocks_become_closures_only_under_callable_parameter_expectations() {
    let package = PackageKey("core-contextual@0.1.0".into());
    let source = "pub fn accept(block: () -> i64) -> () { } pub fn main() -> () { accept { 42 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(
        core.expressions
            .iter()
            .any(|value| matches!(value.kind, CoreKind::Closure { ref parameters, .. } if parameters.is_empty()))
    );
}

#[test]
fn typed_core_resolves_deep_handler_operations_payloads_and_resumptions() {
    let package = PackageKey("core-handler@0.1.0".into());
    let source = "effect Console { read(value: i64) -> i64; } pub fn main() -> i64 { handle Console::read(41) { Console::read(value) with resume => resume(value) } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let Some(CoreKind::Handle {
        computation,
        clauses,
    }) = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            handler @ CoreKind::Handle { .. } => Some(handler),
            _ => None,
        })
    else {
        panic!("handler syntax did not elaborate into Typed Core")
    };
    assert!(matches!(
        core.expression(*computation).kind,
        CoreKind::Perform {
            terminal: false,
            ..
        }
    ));
    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0].bindings[0].0, "value");
    assert!(matches!(
        clauses[0].resumption,
        CoreHandlerResumption::Explicit { ref name, .. } if name == "resume"
    ));
}

#[test]
fn handler_coverage_is_protocol_total_and_terminal_arms_have_no_resumption() {
    let package = PackageKey("core-handler-coverage@0.1.0".into());
    let source = "effect Console { read() -> i64; write(value: i64) -> i64; } effect Stop { abort() -> !; } pub fn partial() -> i64 { handle Console::read() { Console::read() => 1 } } pub fn terminal() -> i64 { handle Stop::abort() { Stop::abort() with resume => 42 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let index = DefinitionIndex::from_interface(&interface);

    let partial = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("partial"))
        .unwrap();
    let partial_body = BodySyntax::parse(&lexed, source, partial.body.unwrap());
    let partial_core = TypedBody::elaborate(partial, &partial_body, &index, &signatures);
    assert!(
        partial_core
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "partial handler unexpectedly discharged Console: {:#?}",
        partial_core.diagnostics
    );

    let terminal = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("terminal"))
        .unwrap();
    let terminal_body = BodySyntax::parse(&lexed, source, terminal.body.unwrap());
    let terminal_core = TypedBody::elaborate(terminal, &terminal_body, &index, &signatures);
    assert!(
        terminal_core
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4160"),
        "terminal handler accepted a resumption: {:#?}",
        terminal_core.diagnostics
    );
}

#[test]
fn handler_payload_binders_capture_only_when_a_nested_closure_needs_them() {
    let package = PackageKey("core-handler-capture@0.1.0".into());
    let source = "effect Console { read(value: i64) -> i64; } pub fn main() -> i64 { handle Console::read(1) { Console::read(value) => { let delayed = (ignored: i64) -> i64 { value }; 1 } } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let closure = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Closure { captures, .. } => Some(captures),
            _ => None,
        })
        .expect("handler clause closure was not elaborated");
    assert_eq!(closure.len(), 1);
    assert_eq!(closure[0].name, "value");
}

#[test]
fn handler_payload_binders_do_not_escape_into_the_enclosing_closure() {
    let package = PackageKey("core-handler-scope@0.1.0".into());
    let source = "effect Console { read(value: i64) -> i64; } pub fn main() -> i64 { let delayed = (ignored: i64) -> i64 { handle Console::read(1) { Console::read(value) => value } }; 0 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let captures = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Closure { captures, .. } => Some(captures),
            _ => None,
        })
        .expect("enclosing closure was not elaborated");
    assert!(
        captures.is_empty(),
        "handler binder escaped its arm: {captures:#?}"
    );
}

#[test]
fn generic_effect_instances_are_resolved_as_distinct_handler_identities() {
    let package = PackageKey("core-handler-generic@0.1.0".into());
    let source = "effect Fail<E> { fail(error: E) -> !; } pub fn main() -> i64 { handle Fail<i64>::fail(42) { Fail<i64>::fail(error) => error } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let clause = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Handle { clauses, .. } => clauses.first(),
            _ => None,
        })
        .expect("generic handler did not reach Core");
    assert_eq!(clause.effect.arguments.len(), 1);
    assert!(matches!(
        clause.effect.arguments[0],
        grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::I64)
    ));
    assert!(clause.terminal);

    let mismatched = "effect Fail<E> { fail(error: E) -> !; } pub fn main() -> i64 { handle Fail<i64>::fail(42) { Fail<Text>::fail(error) => 0 } }";
    let lexed = LexedFile::lex(file, mismatched);
    let scan = DeclarationScan::scan(&lexed, mismatched);
    let interface = InterfaceSet::collect(
        PackageKey("core-handler-generic-mismatch@0.1.0".into()),
        "crate",
        &lexed,
        mismatched,
        &scan,
    )
    .interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, mismatched, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "handler for a distinct generic protocol instance intercepted the operation: {:#?}",
        core.diagnostics
    );
}

#[test]
fn placeflow_joins_handler_arms_conservatively_after_dynamic_selection() {
    let package = PackageKey("core-handler-flow@0.1.0".into());
    let source = "effect Console { read() -> i64; } pub fn main() -> i64 { let value = 7; handle Console::read() { Console::read() => move value, Console::read() => 0 }; value }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "a move in one dynamic handler arm was not propagated: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn exact_one_shot_tail_resumption_lowers_to_a_runtime_handler_frame() {
    let package = PackageKey("core-handler-runtime@0.1.0".into());
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(41); value + 1 } { Ask::ask(seed) => seed } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .expect("one-shot tail handler lowers to MIR");
    let instructions = mir
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::InstallHandler { .. }))
    );
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::Resume { .. }))
    );
}

#[test]
fn generic_effect_handler_frame_retains_its_nominal_instance_arguments() {
    let package = PackageKey("core-handler-runtime-generic@0.1.0".into());
    let source = "effect State<T> { [1,1] get() -> T; } pub fn main() -> i64 { handle State<i64>::get() { State<i64>::get() => 42 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .expect("generic one-shot handler lowers to MIR");
    assert!(mir.blocks.iter().flat_map(|block| &block.instructions).any(
        |instruction| matches!(
            instruction,
            MirInstruction::InstallHandler {
                effect_arguments,
                ..
            } if effect_arguments == &[grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::I64)]
        )
    ));
}
