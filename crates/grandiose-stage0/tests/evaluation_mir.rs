mod support;

use grandiose_stage0::evaluation_mir::{
    EvaluationExit, EvaluationMir, EvaluationOperand, EvaluationOperation as Op, EvaluationPlace,
};
use grandiose_stage0::Type;

fn normalize(source: &str) -> EvaluationMir {
    let (definition, core, _) = support::frontend("evaluation-mir@0.1.0", source, "main");
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let result = EvaluationMir::lower(definition, &core).unwrap();
    result.validate().unwrap();
    result
}

#[test]
fn callable_initializers_and_reads_share_their_resolved_value_join() {
    let mir = normalize("pub fn main() -> i64 {
        let first = 42; let second = 0;
        let mut callback:(i64)->i64 = (argument:i64)->i64 {first};
        let replacement:(i64)->i64 = (argument:i64)->i64 {second};
        callback({callback = replacement; 0})
    }");
    let instructions = mir.regions().iter().flat_map(|region| &region.instructions).collect::<Vec<_>>();
    let binding = instructions.iter().find(|instruction|
        matches!(&instruction.operation, Op::Bind(name) if name == "callback")).unwrap();
    let [EvaluationOperand::Value(value)] = binding.operands.as_slice() else { panic!("binding input") };
    let initializer = instructions.iter().find(|instruction| instruction.value == *value).unwrap();
    assert!(matches!(&initializer.ty, Type::Callable { contract, .. } if contract.environment.is_none()));
    let call = instructions.iter().find(|instruction| matches!(&instruction.operation,
        Op::Call(contract) if !contract.prepared_receiver)).unwrap();
    let EvaluationOperand::Value(value) = call.operands[0] else { panic!("receiver input") };
    let receiver = instructions.iter().find(|instruction| instruction.value == value).unwrap();
    assert!(matches!(receiver.operation, Op::AcquireValue));
    assert_eq!(initializer.ty, receiver.ty);
    grandiose_stage0::control_mir::ControlMir::lower(&mir).unwrap();
}

#[test]
fn receiver_storage_retention_uses_checked_projection_overlap() {
    for (field, prepared) in [(0, false), (1, true)] {
        let mir = normalize(&format!("fn first(value:i64) -> i64 {{42}}
            fn second(value:i64) -> i64 {{0}}
            pub fn main() -> i64 {{
                let callback:(i64)->i64=first;
                let mut saved=(callback,callback);
                saved.0({{saved.{field}=callback; 0}})
            }}"));
        let instructions = mir.regions().iter().flat_map(|region| &region.instructions).collect::<Vec<_>>();
        let call = instructions.iter().find(|instruction| matches!(instruction.operation, Op::Call(_))).unwrap();
        assert!(matches!(&call.operation, Op::Call(contract) if contract.prepared_receiver == prepared), "{field}: {call:?}");
        let EvaluationOperand::Value(value) = call.operands[0] else { panic!("receiver input") };
        let receiver = instructions.iter().find(|instruction| instruction.value == value).unwrap();
        assert_eq!(matches!(receiver.operation, Op::PrepareInvocation), prepared);
        assert!(prepared || matches!(receiver.operation, Op::AcquireValue));
        grandiose_stage0::control_mir::ControlMir::lower(&mir).unwrap();
    }
}

#[test]
fn generic_callable_arguments_share_the_resolved_value_join() {
    let mir = normalize("fn keep<T>(value:T) -> T {value}
        pub fn main() -> i64 {
            let first = 42; let second = 0;
            let mut callback:(i64)->i64 = (argument:i64)->i64 {first};
            let replacement:(i64)->i64 = (argument:i64)->i64 {second};
            let saved = keep(callback);
            callback = replacement;
            saved(0)
        }");
    let instructions = mir.regions().iter().flat_map(|region| &region.instructions).collect::<Vec<_>>();
    let binding = instructions.iter().find(|instruction|
        matches!(&instruction.operation, Op::Bind(name) if name == "callback")).unwrap();
    let [EvaluationOperand::Value(value)] = binding.operands.as_slice() else { panic!("binding input") };
    let initializer = instructions.iter().find(|instruction| instruction.value == *value).unwrap();
    let argument = instructions.iter().find_map(|instruction| match &instruction.operation {
        Op::Function { arguments, .. } if arguments.len() == 1 => Some(&arguments[0]),
        _ => None,
    }).unwrap();
    assert_eq!(argument, &grandiose_stage0::GenericArgument::Type(initializer.ty.clone()));
    assert!(matches!(&initializer.ty, Type::Callable { contract, .. } if contract.environment.is_none()));
    grandiose_stage0::control_mir::ControlMir::lower(&mir).unwrap();
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
fn a_callable_field_prepares_its_receiver_before_strict_arguments() {
    let mir = normalize("fn answer(value:i64) -> i64 { value }
        fn argument() -> i64 { 42 }
        pub fn main() -> i64 { let saved = (answer,); saved.0(argument()) }");
    let instructions = mir.regions().iter().flat_map(|region| &region.instructions).collect::<Vec<_>>();
    let (position, receiver) = instructions.iter().enumerate().find(|(_, instruction)|
        matches!(instruction.operation, Op::PrepareInvocation)).unwrap();
    assert!(matches!(receiver.operands.as_slice(), [EvaluationOperand::Place(EvaluationPlace::Field { index: 0, .. })]));
    let calls = instructions[position + 1..].iter().filter(|instruction| matches!(instruction.operation, Op::Call(_))).collect::<Vec<_>>();
    assert_eq!(calls.len(), 2);
    assert!(matches!(&calls[1].operation, Op::Call(contract) if contract.prepared_receiver));
    assert_eq!(calls[1].operands[0], EvaluationOperand::Value(receiver.value));
}

#[test]
fn a_strict_argument_acquires_its_value_before_the_next_operand_scope() {
    let mir = normalize("fn first(value:i64) -> i64 {42} fn second(value:i64) -> i64 {0}
        fn invoke(task:(i64)->i64, value:i64) -> i64 {task(value)}
        pub fn main() -> i64 {
            let mut callback:(i64)->i64=first;
            let replacement:(i64)->i64=second;
            invoke(callback, {callback=replacement; 0})
        }");
    let instructions = &mir.regions()[mir.entry().0 as usize].instructions;
    let call = instructions.iter().rposition(|instruction| matches!(instruction.operation, Op::Call(_))).unwrap();
    let EvaluationOperand::Value(first) = instructions[call].operands[1] else { panic!("argument value") };
    let acquired = instructions.iter().position(|instruction| instruction.value == first).unwrap();
    assert!(matches!(instructions[acquired].operation, Op::AcquireValue));
    let later = instructions.iter().position(|instruction| matches!(instruction.operation, Op::Scope(_))).unwrap();
    assert!(acquired < later && later < call);
}

#[test]
fn lazy_rhs_is_a_deferred_region() {
    let mir = normalize("fn probe() -> Bool { true } pub fn main() -> Bool { false and { probe() } }");
    let root = &mir.regions()[mir.entry().0 as usize];
    // `and` is an ordinary library call; only the thunk construction is
    // strict. Its probe call must remain in the separate closure region.
    assert_eq!(root.instructions.iter().filter(|instruction|
        matches!(instruction.operation, Op::Call(_))).count(), 1);
    let right = root.instructions.iter().find_map(|instruction|
        match instruction.operation { Op::Closure { body, .. } => Some(body), _ => None }).unwrap();
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
            .any(|instruction| matches!(instruction.operation, Op::TraitMethod { .. }))
    );
    assert!(
        mir.regions()[body.0 as usize]
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.operation, Op::TraitMethod { .. }))
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
        "pub enum Result { Ok(i64), Err } fn probe() -> Result { Result::Ok(42) } pub fn main() -> i64 { handle probe() is Result::Ok(found) { Test::Yes(_) => 1; Test::No(_) => 0 } }",
    );
    let root = &mir.regions()[mir.entry().0 as usize];
    let Op::Completion { computation, arms, .. } = &root.instructions.last().unwrap().operation else {
        panic!("{root:?}");
    };
    assert_eq!(arms.len(), 2);
    let subject = &mir.regions()[computation.0 as usize];
    // `is` constructs an ordinary Test by an inner pattern completion. The
    // outer completion observes that carrier without calling `probe` again.
    let tested_region = subject.instructions.iter().find_map(|instruction|
        match instruction.operation { Op::Completion { computation, .. } => Some(computation), _ => None }).unwrap();
    assert_eq!(mir.regions()[tested_region.0 as usize].instructions.iter().filter(|instruction|
        matches!(&instruction.operation, Op::Call(_))).count(), 1);
    assert_eq!(mir.regions().iter().flat_map(|region| &region.instructions).filter(|instruction|
        matches!(&instruction.operation, Op::Call(_))).count(), 1);
    for arm in arms {
        assert!(
            !mir.regions()[arm.region.0 as usize]
                .instructions
                .iter()
                .any(|instruction| matches!(&instruction.operation, Op::Call(_)))
        );
    }
}

#[test]
fn label_transfer_is_terminal_only_inside_its_delimited_region() {
    let mir = normalize("pub fn main() -> Bool { label done { transfer done true } }");
    let root = &mir.regions()[mir.entry().0 as usize];
    let Op::Label { brand, body } = root.instructions.last().unwrap().operation else {
        panic!("{root:?}");
    };
    assert!(matches!(root.exit, EvaluationExit::Yield(_)));
    let transfer = &mir.regions()[body.0 as usize];
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
