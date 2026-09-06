use grandiose_stage0::evaluation_mir::{
    EvaluationExit, EvaluationMir, EvaluationOperand, EvaluationOperation as Op, EvaluationPlace,
};
use grandiose_stage0::{
    BodySyntax, DeclarationScan, DefinitionIndex, ElaboratedInterface, FileKey, InterfaceSet,
    LexedFile, PackageKey, Type, TypedBody,
};

fn normalize(source: &str) -> EvaluationMir {
    let package = PackageKey("evaluation-mir@0.1.0".into());
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
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
    let result = EvaluationMir::lower(definition.key, &core).unwrap();
    result.validate().unwrap();
    result
}

#[test]
fn strict_calls_are_ordered_before_their_aggregate() {
    let mir = normalize(
        "fn first() -> i64 { 1 } fn second() -> i64 { 2 } pub fn main() -> (i64, i64) { (first(), second()) }",
    );
    let root = &mir.regions()[mir.entry().0 as usize];
    let calls: Vec<_> = root
        .instructions
        .iter()
        .filter(|instruction| matches!(instruction.operation, Op::Call(_)))
        .collect();
    assert_eq!(calls.len(), 2);
    let tuple = root.instructions.last().unwrap();
    assert_eq!(tuple.operation, Op::Tuple);
    assert_eq!(
        tuple.operands,
        calls
            .iter()
            .map(|call| EvaluationOperand::Value(call.value))
            .collect::<Vec<_>>()
    );
    assert!(calls[0].span.start < calls[1].span.start);
}

#[test]
fn lazy_rhs_is_a_deferred_region() {
    let mir = normalize("fn probe() -> Bool { true } pub fn main() -> Bool { false and probe() }");
    let root = &mir.regions()[mir.entry().0 as usize];
    assert!(
        !root
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.operation, Op::Call(_)))
    );
    let lazy = root.instructions.last().unwrap();
    let Op::LazyBoolean {
        conjunction: true,
        right,
    } = lazy.operation
    else {
        panic!("{lazy:?}");
    };
    assert_eq!(lazy.operands.len(), 1);
    assert!(
        mir.regions()[right.0 as usize]
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.operation, Op::Call(_)))
    );
}

#[test]
fn borrow_projects_a_place_without_reading_the_owner() {
    let mir = normalize(
        "struct Pair { first: i64, second: i64 } pub fn main(value: Pair) -> i64 { let loan = &value.second; *loan }",
    );
    let root = &mir.regions()[mir.entry().0 as usize];
    let borrow = root
        .instructions
        .iter()
        .find(|instruction| matches!(instruction.operation, Op::Borrow { .. }))
        .unwrap();
    assert!(
        matches!(&borrow.operands[..], [EvaluationOperand::Place(EvaluationPlace::Field { base, index: 1, .. })]
        if matches!(base.as_ref(), EvaluationPlace::Local { name, .. } if name == "value"))
    );
    assert!(!root.instructions.iter().any(
        |instruction| matches!(&instruction.operation, Op::ReadLocal(name) if name == "value")
    ));
}

#[test]
fn assignment_orders_rhs_before_target_reference() {
    let mir =
        normalize("pub fn main(target: &mut i64, rhs: () -> i64) -> i64 { *target = rhs(); 0 }");
    let root = &mir.regions()[mir.entry().0 as usize];
    let call = root
        .instructions
        .iter()
        .position(|instruction| matches!(instruction.operation, Op::Call(_)))
        .unwrap();
    let target = root
        .instructions
        .iter()
        .position(
            |instruction| matches!(&instruction.operation, Op::ReadLocal(name) if name == "target"),
        )
        .unwrap();
    let store = root
        .instructions
        .iter()
        .position(|instruction| instruction.operation == Op::Assign)
        .unwrap();
    assert!(call < target && target < store);
    assert!(matches!(
        &root.instructions[store].operands[..],
        [
            EvaluationOperand::Value(_),
            EvaluationOperand::Place(EvaluationPlace::Deref { .. })
        ]
    ));
}

#[test]
fn terminal_call_argument_has_no_aggregate_or_suffix() {
    let mir = normalize("pub fn main(halt: () -> !) -> (i64, i64) { (halt(), 7) }");
    let root = &mir.regions()[mir.entry().0 as usize];
    assert!(matches!(root.exit, EvaluationExit::Diverge(_)));
    assert_eq!(root.instructions.last().unwrap().ty, Type::Never);
    assert!(
        !root
            .instructions
            .iter()
            .any(|instruction| instruction.operation == Op::Tuple
                || instruction.operation == Op::Literal("7".into()))
    );
}

#[test]
fn terminal_nested_block_has_no_enclosing_strict_suffix() {
    let mir = normalize("pub fn main(halt: () -> !) -> (i64, i64) { ({ halt() }, 7) }");
    let root = &mir.regions()[mir.entry().0 as usize];
    assert!(matches!(root.exit, EvaluationExit::Diverge(_)));
    assert!(
        !root
            .instructions
            .iter()
            .any(|instruction| instruction.operation == Op::Tuple
                || instruction.operation == Op::Literal("7".into()))
    );
}

#[test]
fn closure_body_is_not_evaluated_at_construction() {
    let mir = normalize(
        "pub fn main() -> i64 { let callable = (value: i64) -> i64 { value + 1 }; callable(41) }",
    );
    let root = &mir.regions()[mir.entry().0 as usize];
    let body = root
        .instructions
        .iter()
        .find_map(|instruction| match instruction.operation {
            Op::Closure { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    assert!(
        !root
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.operation, Op::Intrinsic(_)))
    );
    assert!(
        mir.regions()[body.0 as usize]
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.operation, Op::Intrinsic(_)))
    );
}

#[test]
fn handler_computation_and_clause_have_separate_regions_and_contracts() {
    let mir = normalize(
        "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => k(42) } }",
    );
    let root = &mir.regions()[mir.entry().0 as usize];
    let Op::Handle { computation, arms } = &root.instructions.last().unwrap().operation else {
        panic!("{root:?}");
    };
    assert_eq!(arms.len(), 1);
    assert_ne!(*computation, arms[0].region);
    assert!(arms[0].continuation.is_some());
    assert!(
        mir.regions()[computation.0 as usize]
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.operation, Op::Perform { .. }))
    );
    assert!(
        mir.regions()[arms[0].region.0 as usize]
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.operation, Op::Call(_)))
    );
    assert!(
        !root
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.operation, Op::Perform { .. } | Op::Call(_)))
    );
}

#[test]
fn normalizing_the_same_core_is_deterministic() {
    let source = "pub fn main() -> i64 { let value = 41; value + 1 }";
    assert_eq!(normalize(source), normalize(source));
}

#[test]
fn completion_refinement_keeps_once_evaluated_subject_provenance() {
    let mir = normalize(
        "pub enum Result { Ok(i64), Err } pub fn main(value: Result) -> i64 { handle value is Result::Ok(found) { true => found; false => 0 } }",
    );
    let root = &mir.regions()[mir.entry().0 as usize];
    let Op::Completion { computation, arms } = &root.instructions.last().unwrap().operation else {
        panic!("{root:?}");
    };
    assert_eq!(arms.len(), 2);
    let refinement = arms.iter().find_map(|arm| arm.refinement.as_ref()).unwrap();
    let subject = &mir.regions()[computation.0 as usize];
    assert!(
        subject
            .instructions
            .iter()
            .any(|instruction| instruction.source == refinement.subject)
    );
    for arm in arms {
        assert!(
            !mir.regions()[arm.region.0 as usize]
                .instructions
                .iter()
                .any(|instruction| instruction.source == refinement.subject)
        );
    }
}

#[test]
fn label_transfer_is_terminal_only_inside_its_delimited_region() {
    let mir = normalize("pub fn main() -> Bool { label done { false or transfer done true } }");
    let root = &mir.regions()[mir.entry().0 as usize];
    let Op::Label { brand, body } = root.instructions.last().unwrap().operation else {
        panic!("{root:?}");
    };
    assert!(matches!(root.exit, EvaluationExit::Yield(_)));
    let region = &mir.regions()[body.0 as usize];
    let Op::LazyBoolean {
        conjunction: false,
        right,
    } = region.instructions.last().unwrap().operation
    else {
        panic!("{region:?}");
    };
    let transfer = &mir.regions()[right.0 as usize];
    assert_eq!(
        transfer.instructions.last().unwrap().operation,
        Op::Transfer(brand)
    );
    assert!(matches!(transfer.exit, EvaluationExit::Diverge(_)));
}

#[test]
fn temporary_borrow_keeps_its_owner_as_an_explicit_dependency() {
    let mir = normalize("pub fn main() -> i64 { let loan = &42; *loan }");
    let root = &mir.regions()[mir.entry().0 as usize];
    let borrow = root
        .instructions
        .iter()
        .find(|instruction| matches!(instruction.operation, Op::Borrow { .. }))
        .unwrap();
    assert!(
        matches!(&borrow.operands[..], [EvaluationOperand::Place(EvaluationPlace::Temporary { value, .. })]
        if root.instructions.iter().any(|instruction| instruction.value == *value && instruction.operation == Op::Literal("42".into())))
    );
}

#[test]
fn statement_disposition_precedes_the_next_statement() {
    let mir = normalize(
        "fn first() -> i64 { 1 } fn second() -> i64 { 2 } pub fn main() -> i64 { first(); second() }",
    );
    let root = &mir.regions()[mir.entry().0 as usize];
    let first = root
        .instructions
        .iter()
        .position(|instruction| matches!(instruction.operation, Op::Call(_)))
        .unwrap();
    let discard = &root.instructions[first + 1];
    assert_eq!(discard.operation, Op::Discard);
    assert_eq!(
        discard.operands,
        vec![EvaluationOperand::Value(root.instructions[first].value)]
    );
    assert!(
        root.instructions[first + 2..]
            .iter()
            .any(|instruction| matches!(instruction.operation, Op::Call(_)))
    );
}
