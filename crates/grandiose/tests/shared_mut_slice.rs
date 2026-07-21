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
            "SliceMut recovery test performed a host effect",
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

const MUT_SLICE_SURFACE: &str = r#"
    values() -> Vec<i64> { Vec::new() }

    exercise_get_mut() -> usize {
        let values = values();
        Vec::push(&mut values, 10);
        Vec::push(&mut values, 20);
        let view = Vec::as_mut_slice(&mut values);
        let length = SliceMut::len(&view);
        let _empty = SliceMut::is_empty(&view);
        let _item = SliceMut::get_mut(move view, 1);
        length
    }

    exercise_first_mut() -> () {
        let values = values();
        Vec::push(&mut values, 10);
        let view = Vec::as_mut_slice(&mut values);
        let _item = SliceMut::first_mut(move view);
        ()
    }

    exercise_get() -> () {
        let values = values();
        Vec::push(&mut values, 10);
        let view = Vec::as_mut_slice(&mut values);
        let _item = SliceMut::get(move view, 0);
        ()
    }

    exercise_first() -> () {
        let values = values();
        Vec::push(&mut values, 10);
        let view = Vec::as_mut_slice(&mut values);
        let _item = SliceMut::first(move view);
        ()
    }

    exercise_subslice_mut() -> () {
        let values = values();
        Vec::push(&mut values, 10);
        Vec::push(&mut values, 20);
        Vec::push(&mut values, 30);
        let view = Vec::as_mut_slice(&mut values);
        let _piece = SliceMut::subslice_mut(move view, 1, 2);
        ()
    }

    exercise_subslice() -> () {
        let values = values();
        Vec::push(&mut values, 10);
        Vec::push(&mut values, 20);
        let view = Vec::as_mut_slice(&mut values);
        let _piece = SliceMut::subslice(move view, 0, 1);
        ()
    }

    main() -> () { () }
"#;

fn slice_mut_value(
    artifact: &grandiose_vm::Artifact,
    slice_ty: u32,
    start: u64,
    length: u64,
) -> Value {
    let Type::Struct { name, fields, .. } = artifact.types[slice_ty as usize].representation()
    else {
        panic!("SliceMut parameter is not a struct")
    };
    assert_eq!(name, "SliceMut");
    let Type::RefUnique { referent } = artifact.types[fields[0].ty as usize].representation()
    else {
        panic!("SliceMut base is not a unique Array reference")
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
        slice_ty,
        [
            Value::Reference {
                referent_type: *referent,
                unique: true,
                target: ReferenceTarget::Array(array),
            },
            Value::U64(start),
            Value::U64(length),
        ],
    )
}

#[test]
fn mutable_slice_checked_surface_executes_at_every_optimization_level() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "shared-mut-slice.glorious",
            MUT_SLICE_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let exercise = function_id(&phases.artifact, "exercise_get_mut");
        let get_mut = function_id(&phases.artifact, "__g1_slice_mut_get_mut");
        let get = function_id(&phases.artifact, "__g1_slice_mut_get");
        let subslice_mut = function_id(&phases.artifact, "__g1_slice_mut_subslice_mut");
        let subslice = function_id(&phases.artifact, "__g1_slice_mut_subslice");
        let slice_ty = phases.artifact.functions[get_mut as usize].params[0];
        let vm = Vm::new(verify(phases.artifact.clone()).unwrap());
        assert_eq!(
            vm.run(exercise, vec![]).unwrap(),
            Value::U64(2),
            "{optimization_level:?}"
        );

        let Value::Aggregate(some) = vm
            .run(
                get_mut,
                vec![
                    slice_mut_value(&phases.artifact, slice_ty, 1, 2),
                    Value::U64(1),
                ],
            )
            .unwrap()
        else {
            panic!("{optimization_level:?}: in-range get_mut did not return Some")
        };
        let some = some.borrow();
        assert_eq!(some.variant, Some(0), "{optimization_level:?}");
        let Some(Value::Reference {
            unique: true,
            target: ReferenceTarget::ArrayElement { index, .. },
            ..
        }) = some.fields[0].as_ref()
        else {
            panic!("{optimization_level:?}: get_mut did not return a unique element reference")
        };
        assert_eq!(*index, 2, "{optimization_level:?}");

        let Value::Aggregate(none) = vm
            .run(
                get_mut,
                vec![
                    slice_mut_value(&phases.artifact, slice_ty, 1, 2),
                    Value::U64(2),
                ],
            )
            .unwrap()
        else {
            panic!("{optimization_level:?}: out-of-range get_mut did not return None")
        };
        assert_eq!(none.borrow().variant, Some(1), "{optimization_level:?}");

        let Value::Aggregate(some) = vm
            .run(
                get,
                vec![
                    slice_mut_value(&phases.artifact, slice_ty, 1, 2),
                    Value::U64(0),
                ],
            )
            .unwrap()
        else {
            panic!("{optimization_level:?}: in-range shared get did not return Some")
        };
        let some = some.borrow();
        let Some(Value::Reference {
            unique: false,
            target: ReferenceTarget::ArrayElement { index, .. },
            ..
        }) = some.fields[0].as_ref()
        else {
            panic!("{optimization_level:?}: shared get did not downgrade the element reference")
        };
        assert_eq!(*index, 1, "{optimization_level:?}");

        let Value::Aggregate(none) = vm
            .run(
                get,
                vec![
                    slice_mut_value(&phases.artifact, slice_ty, 1, 2),
                    Value::U64(2),
                ],
            )
            .unwrap()
        else {
            panic!("{optimization_level:?}: out-of-range shared get did not return None")
        };
        assert_eq!(none.borrow().variant, Some(1), "{optimization_level:?}");

        let Value::Aggregate(piece) = vm
            .run(
                subslice_mut,
                vec![
                    slice_mut_value(&phases.artifact, slice_ty, 1, 2),
                    Value::U64(1),
                    Value::U64(1),
                ],
            )
            .unwrap()
        else {
            panic!("{optimization_level:?}: valid subslice_mut did not return Some")
        };
        let piece = piece.borrow();
        assert_eq!(piece.variant, Some(0), "{optimization_level:?}");
        let Some(Value::Aggregate(piece)) = piece.fields[0].as_ref() else {
            panic!("{optimization_level:?}: subslice_mut payload is not SliceMut")
        };
        let piece = piece.borrow();
        assert_eq!(
            piece.fields[1],
            Some(Value::U64(2)),
            "{optimization_level:?}"
        );

        let Value::Aggregate(none) = vm
            .run(
                subslice,
                vec![
                    slice_mut_value(&phases.artifact, slice_ty, 1, 2),
                    Value::U64(2),
                    Value::U64(1),
                ],
            )
            .unwrap()
        else {
            panic!("{optimization_level:?}: invalid shared subslice did not return None")
        };
        assert_eq!(none.borrow().variant, Some(1), "{optimization_level:?}");
        assert_eq!(
            piece.fields[2],
            Some(Value::U64(1)),
            "{optimization_level:?}"
        );

        let Value::Aggregate(none) = vm
            .run(
                subslice_mut,
                vec![
                    slice_mut_value(&phases.artifact, slice_ty, 1, 2),
                    Value::U64(2),
                    Value::U64(1),
                ],
            )
            .unwrap()
        else {
            panic!("{optimization_level:?}: invalid subslice_mut did not return None")
        };
        assert_eq!(none.borrow().variant, Some(1), "{optimization_level:?}");

        let Value::Aggregate(piece) = vm
            .run(
                subslice,
                vec![
                    slice_mut_value(&phases.artifact, slice_ty, 1, 2),
                    Value::U64(1),
                    Value::U64(1),
                ],
            )
            .unwrap()
        else {
            panic!("{optimization_level:?}: valid shared subslice did not return Some")
        };
        let piece = piece.borrow();
        let Some(Value::Aggregate(piece)) = piece.fields[0].as_ref() else {
            panic!("{optimization_level:?}: shared subslice payload is not Slice")
        };
        let piece = piece.borrow();
        let Type::Struct { name, .. } = phases.artifact.types[piece.ty as usize].representation()
        else {
            panic!("{optimization_level:?}: shared subslice payload type is not a struct")
        };
        assert_eq!(name, "Slice", "{optimization_level:?}");
        assert_eq!(
            piece.fields[1],
            Some(Value::U64(2)),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn mutable_slice_is_private_linear_and_keeps_the_vec_uniquely_loaned() {
    for (name, source, expected) in [
        (
            "slice-mut-forge.glorious",
            "bad<'a>(base:&'a mut Array<i64>)->SliceMut<'a,i64>{SliceMut{base:base,start:0,length:0}} main()->(){()}",
            "private field",
        ),
        (
            "slice-mut-copy.glorious",
            "empty_i64()->Vec<i64>{Vec::new()} bad()->usize{let values=empty_i64();let view=Vec::as_mut_slice(&mut values);let second=move view;SliceMut::len(&view)} main()->(){()}",
            "moved",
        ),
        (
            "slice-mut-alias.glorious",
            "empty_i64()->Vec<i64>{Vec::new()} bad()->(){let values=empty_i64();let first=Vec::as_mut_slice(&mut values);let second=Vec::as_mut_slice(&mut values);let _a=SliceMut::len(&first);let _b=SliceMut::len(&second);()} main()->(){()}",
            "loan",
        ),
        (
            "slice-mut-escape.glorious",
            "empty_i64()->Vec<i64>{Vec::new()} bad()->SliceMut<'static,i64>{let values=empty_i64();Vec::push(&mut values,1);Vec::as_mut_slice(&mut values)} main()->(){()}",
            "cannot escape",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("an invalid SliceMut ownership path compiled");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn mutable_slice_construction_and_length_have_recovery_parity() {
    let result = run_source(
        "slice-mut-recovery.glorious",
        r#"
            main() -> usize {
                let values = Vec::new();
                Vec::push(&mut values, 10);
                Vec::push(&mut values, 20);
                let view = Vec::as_mut_slice(&mut values);
                SliceMut::len(&view)
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(2));
}
