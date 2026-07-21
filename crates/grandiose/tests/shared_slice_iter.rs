use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{
    Type, Value, Vm,
    value::{ArenaObject, ArrayValue, ReferenceTarget},
    verify,
};

#[derive(Default)]
struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<RecoveryValue>,
        span: Span,
    ) -> Result<RecoveryValue, grandiose::diagnostic::Diagnostic> {
        Err(grandiose::diagnostic::Diagnostic::error(
            "unexpected effect",
            "shared SliceIter recovery test performed a host effect",
            span,
        ))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| {
            function.name == name
                || function
                    .name
                    .strip_prefix("$specialization$")
                    .and_then(|wire| wire.split_once('#'))
                    .is_some_and(|(template, _)| template == name)
        })
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const SHARED_SLICE_ITER_SURFACE: &str = r#"
    values() -> Vec<i64> { Vec::new() }

    answer() -> usize {
        let values = values();
        Vec::push(&mut values, 10);
        Vec::push(&mut values, 20);
        Vec::push(&mut values, 30);
        let view = Vec::as_slice(&values);
        let iterator = Slice::iter(view);
        let remaining = SliceIter::len(&iterator);
        let _empty = SliceIter::is_empty(&iterator);
        let _step = SliceIter::next(iterator);
        remaining
    }

    empty_answer() -> usize {
        let values = values();
        let view = Vec::as_slice(&values);
        let iterator = Slice::iter(view);
        let _step = SliceIter::next(iterator);
        Slice::len(view)
    }

    main() -> () { () }
"#;

fn iter_value(
    artifact: &grandiose_vm::Artifact,
    iter_ty: u32,
    start: u64,
    length: u64,
    index: u64,
) -> Value {
    let Type::Struct { name, fields, .. } = artifact.types[iter_ty as usize].representation()
    else {
        panic!("SliceIter parameter is not a struct")
    };
    assert_eq!(name, "SliceIter");
    let base_ref_ty = fields[0].ty;
    let Type::RefShared { referent } = artifact.types[base_ref_ty as usize].representation() else {
        panic!("SliceIter base is not a shared Array reference")
    };
    let array = ArenaObject::new(ArrayValue {
        element_type: grandiose_vm::I64,
        slots: [10, 20, 30, 40]
            .into_iter()
            .map(|value| Some(Value::I64(value)))
            .collect(),
        logical_capacity: 4,
    });
    Value::aggregate(
        iter_ty,
        [
            Value::Reference {
                referent_type: *referent,
                unique: false,
                target: ReferenceTarget::Array(array),
            },
            Value::U64(start),
            Value::U64(length),
            Value::U64(index),
        ],
    )
}

#[test]
fn shared_slice_iterator_orders_and_exhausts_at_every_optimization_level() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "shared-slice-iter.glorious",
            SHARED_SLICE_ITER_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = function_id(&phases.artifact, "answer");
        let empty_answer = function_id(&phases.artifact, "empty_answer");
        let next = function_id(&phases.artifact, "__g1_slice_iter_next");
        let iter_ty = phases.artifact.functions[next as usize].params[0];
        let vm = Vm::new(verify(phases.artifact.clone()).unwrap());

        assert_eq!(vm.run(answer, vec![]).unwrap(), Value::U64(3));
        assert_eq!(vm.run(empty_answer, vec![]).unwrap(), Value::U64(0));

        for (index, expected_next) in [(0, 1), (1, 2)] {
            let iterator = iter_value(&phases.artifact, iter_ty, 1, 2, index);
            let Value::Aggregate(some) = vm.run(next, vec![iterator]).unwrap() else {
                panic!("{optimization_level:?}: next did not return Option::Some")
            };
            let some = some.borrow();
            assert_eq!(some.variant, Some(0), "{optimization_level:?}");
            let Some(Value::Aggregate(pair)) = some.fields[0].as_ref() else {
                panic!("{optimization_level:?}: Some payload is not the index/state pair")
            };
            let pair = pair.borrow();
            assert_eq!(pair.fields[0], Some(Value::U64(index)));
            let Some(Value::Aggregate(next_state)) = pair.fields[1].as_ref() else {
                panic!("{optimization_level:?}: pair did not retain SliceIter state")
            };
            assert_eq!(
                next_state.borrow().fields[3],
                Some(Value::U64(expected_next)),
                "{optimization_level:?}"
            );
        }

        for index in [2, 3] {
            let iterator = iter_value(&phases.artifact, iter_ty, 1, 2, index);
            let Value::Aggregate(none) = vm.run(next, vec![iterator]).unwrap() else {
                panic!("{optimization_level:?}: exhausted next did not return Option::None")
            };
            assert_eq!(none.borrow().variant, Some(1), "{optimization_level:?}");
        }

        let empty = iter_value(&phases.artifact, iter_ty, 0, 0, 0);
        let Value::Aggregate(none) = vm.run(next, vec![empty]).unwrap() else {
            panic!("{optimization_level:?}: empty next did not return Option::None")
        };
        assert_eq!(none.borrow().variant, Some(1), "{optimization_level:?}");
    }
}

#[test]
fn shared_slice_iterator_private_representation_cannot_be_forged_or_projected() {
    for (name, source, expected) in [
        (
            "slice-iter-forge.glorious",
            "bad<'a>(base:&'a Array<i64>)->SliceIter<'a,i64>{SliceIter{base:base,start:0,length:0,index:0}} main()->(){()}",
            "private field",
        ),
        (
            "slice-iter-project.glorious",
            "bad<'a>(value:SliceIter<'a,i64>)->usize{value.index} main()->(){()}",
            "private field `index`",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("user code accessed SliceIter's private representation");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn shared_slice_iterator_preserves_the_vec_loan_and_cannot_escape_it() {
    for (name, source, expected) in [
        (
            "slice-iter-local-escape.glorious",
            "empty_i64()->Vec<i64>{Vec::new()} bad()->SliceIter<'static,i64>{let values=empty_i64();Vec::push(&mut values,1);let view=Vec::as_slice(&values);Slice::iter(view)} main()->(){()}",
            "cannot escape",
        ),
        (
            "slice-iter-unique-conflict.glorious",
            "empty_i64()->Vec<i64>{Vec::new()} bad()->(){let values=empty_i64();Vec::push(&mut values,1);let view=Vec::as_slice(&values);let iterator=Slice::iter(view);Vec::push(&mut values,2);let _length=SliceIter::len(&iterator);()} main()->(){()}",
            "loan",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("a shared SliceIter lost its backing Vec loan");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn shared_slice_iterator_construction_and_length_have_recovery_parity() {
    let result = run_source(
        "shared-slice-iter-recovery.glorious",
        r#"
            main() -> usize {
                let values = Vec::new();
                Vec::push(&mut values, 10);
                Vec::push(&mut values, 20);
                let view = Vec::as_slice(&values);
                let iterator = Slice::iter(view);
                SliceIter::len(&iterator)
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(2));
}
