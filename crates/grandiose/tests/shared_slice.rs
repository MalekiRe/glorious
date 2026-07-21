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
            "shared Slice recovery test performed a host effect",
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

const SHARED_SLICE_SURFACE: &str = r#"
    values() -> Vec<i64> { Vec::new() }

    answer() -> usize {
        let values = values();
        Vec::push(&mut values, 10);
        Vec::push(&mut values, 20);
        Vec::push(&mut values, 30);
        Vec::push(&mut values, 40);
        let view = Vec::as_slice(&values);
        let _first = Slice::first(view);
        let _inside = Slice::get(view, 2);
        let _outside = Slice::get(view, 9);
        let _piece = Slice::subslice(view, 1, 2);
        let _empty_tail = Slice::subslice(view, 4, 0);
        let _bad_start = Slice::subslice(view, 5, 0);
        let _bad_length = Slice::subslice(view, 3, 2);
        let _empty = Slice::is_empty(view);
        Slice::len(view)
    }

    main() -> () { () }
"#;

fn slice_value(
    artifact: &grandiose_vm::Artifact,
    slice_ty: u32,
    start: u64,
    length: u64,
) -> (Value, ArenaObject<ArrayValue>) {
    let Type::Struct { name, fields, .. } = artifact.types[slice_ty as usize].representation()
    else {
        panic!("Slice parameter is not a struct")
    };
    assert_eq!(name, "Slice");
    let base_ref_ty = fields[0].ty;
    let Type::RefShared { referent } = artifact.types[base_ref_ty as usize].representation() else {
        panic!("Slice base is not a shared Array reference")
    };
    let array = ArenaObject::new(ArrayValue {
        element_type: grandiose_vm::I64,
        slots: [10, 20, 30, 40]
            .into_iter()
            .map(|value| Some(Value::I64(value)))
            .collect(),
        logical_capacity: 4,
    });
    (
        Value::aggregate(
            slice_ty,
            [
                Value::Reference {
                    referent_type: *referent,
                    unique: false,
                    target: ReferenceTarget::Array(array.clone()),
                },
                Value::U64(start),
                Value::U64(length),
            ],
        ),
        array,
    )
}

#[test]
fn shared_slice_checked_surface_executes_at_every_optimization_level() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "shared-slice.glorious",
            SHARED_SLICE_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = function_id(&phases.artifact, "answer");
        let get = function_id(&phases.artifact, "__g1_slice_get");
        let subslice = function_id(&phases.artifact, "__g1_slice_subslice");
        let slice_ty = phases.artifact.functions[get as usize].params[0];
        let (view, array) = slice_value(&phases.artifact, slice_ty, 1, 2);
        let vm = Vm::new(verify(phases.artifact.clone()).unwrap());
        assert_eq!(
            vm.run(answer, vec![]).unwrap(),
            Value::U64(4),
            "{optimization_level:?}"
        );

        let Value::Aggregate(some) = vm.run(get, vec![view, Value::U64(1)]).unwrap() else {
            panic!("{optimization_level:?}: in-range get did not return Option::Some")
        };
        let some = some.borrow();
        assert_eq!(some.variant, Some(0), "{optimization_level:?}");
        let Some(Value::Reference {
            target:
                ReferenceTarget::ArrayElement {
                    array: found,
                    index,
                },
            ..
        }) = some.fields[0].as_ref()
        else {
            panic!("{optimization_level:?}: get did not return an element reference")
        };
        assert!(ArenaObject::ptr_eq(found, &array), "{optimization_level:?}");
        assert_eq!(*index, 2, "{optimization_level:?}");
        drop(some);

        let (view, _) = slice_value(&phases.artifact, slice_ty, 1, 2);
        let Value::Aggregate(none) = vm.run(get, vec![view, Value::U64(2)]).unwrap() else {
            panic!("{optimization_level:?}: out-of-range get did not return Option::None")
        };
        assert_eq!(none.borrow().variant, Some(1), "{optimization_level:?}");

        let (view, _) = slice_value(&phases.artifact, slice_ty, 1, 2);
        let Value::Aggregate(piece) = vm
            .run(subslice, vec![view, Value::U64(1), Value::U64(1)])
            .unwrap()
        else {
            panic!("{optimization_level:?}: valid subslice did not return Option::Some")
        };
        let piece = piece.borrow();
        assert_eq!(piece.variant, Some(0), "{optimization_level:?}");
        let Some(Value::Aggregate(piece)) = piece.fields[0].as_ref() else {
            panic!("{optimization_level:?}: subslice payload is not Slice")
        };
        let piece = piece.borrow();
        assert_eq!(
            piece.fields[1],
            Some(Value::U64(2)),
            "{optimization_level:?}"
        );
        assert_eq!(
            piece.fields[2],
            Some(Value::U64(1)),
            "{optimization_level:?}"
        );

        let (view, _) = slice_value(&phases.artifact, slice_ty, 1, 2);
        let Value::Aggregate(none) = vm
            .run(subslice, vec![view, Value::U64(2), Value::U64(1)])
            .unwrap()
        else {
            panic!("{optimization_level:?}: invalid subslice did not return Option::None")
        };
        assert_eq!(none.borrow().variant, Some(1), "{optimization_level:?}");
    }
}

#[test]
fn shared_slice_private_representation_cannot_be_forged_or_projected() {
    for (name, source, expected) in [
        (
            "slice-forge.glorious",
            "bad<'a>(base:&'a Array<i64>)->Slice<'a,i64>{Slice{base:base,start:0,length:0}} main()->(){()}",
            "private field",
        ),
        (
            "slice-project.glorious",
            "bad<'a>(value:Slice<'a,i64>)->usize{value.start} main()->(){()}",
            "private field `start`",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("user code accessed Slice's private representation");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn shared_slice_preserves_the_vec_loan_and_cannot_escape_it() {
    for (name, source, expected) in [
        (
            "slice-local-escape.glorious",
            "empty_i64()->Vec<i64>{Vec::new()} bad()->Slice<'static,i64>{let values=empty_i64();Vec::push(&mut values,1);Vec::as_slice(&values)} main()->(){()}",
            "cannot escape",
        ),
        (
            "slice-unique-conflict.glorious",
            "empty_i64()->Vec<i64>{Vec::new()} bad()->(){let values=empty_i64();Vec::push(&mut values,1);let view=Vec::as_slice(&values);Vec::push(&mut values,2);let _length=Slice::len(view);()} main()->(){()}",
            "loan",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("a shared Slice lost its backing Vec loan");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn shared_slice_construction_and_length_have_recovery_parity() {
    let result = run_source(
        "shared-slice-recovery.glorious",
        r#"
            main() -> usize {
                let values = Vec::new();
                Vec::push(&mut values, 10);
                Vec::push(&mut values, 20);
                let view = Vec::as_slice(&values);
                Slice::len(view)
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(2));
}
