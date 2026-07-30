use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options};
use grandiose_vm::{Value, Vm, verify};

const SOURCE: &str = r#"
    struct ItemTag {}

    values() -> IndexVec<ItemTag, usize> {
        let output = IndexVec::new();
        IndexVec::push(&mut output, 2);
        IndexVec::push(&mut output, 3);
        IndexVec::push(&mut output, 5);
        IndexVec::push(&mut output, 7);
        output
    }

    effect Observe {
        [1,1] item(id: usize, value: usize) -> ()
    }

    observe(id: Id<ItemTag>, value: &usize) -> () / {Observe} {
        perform Observe::item(Id::to_usize(id), *value)
    }

    for_each_ids_and_values() -> usize {
        let source = values();
        handle {
            IndexVec::for_each(&source, observe);
            0
        } {
            Observe::item(id, value) with continuation => {
                id * 10 + value + resume(continuation, ())
            }
        }
    }

    reject_five(id: Id<ItemTag>, value: &usize) -> Result<(), usize> {
        if(*value == 5) {
            Result::Err(Id::to_usize(id))
        } else if(*value == 7) {
            Result::Err(90 + Id::to_usize(id))
        } else {
            Result::Ok(())
        }
    }

    try_for_each_stops_at_error() -> usize {
        let source = values();
        handle IndexVec::try_for_each(&source, reject_five) {
            Result::Err(id) => id,
            Result::Ok(_) => 99
        }
    }

    observe_then_reject(
        id: Id<ItemTag>,
        value: &usize
    ) -> Result<(), usize> / {Observe} {
        perform Observe::item(Id::to_usize(id), *value);
        reject_five(id, value)
    }

    try_for_each_preserves_effects() -> usize {
        let source = values();
        handle {
            handle IndexVec::try_for_each(&source, observe_then_reject) {
                Result::Err(id) => id,
                Result::Ok(_) => 99
            }
        } {
            Observe::item(id, value) with continuation => {
                id + value + resume(continuation, ())
            }
        }
    }

    fold_item(total: usize, id: Id<ItemTag>, value: &usize) -> usize {
        total * 100 + Id::to_usize(id) * 10 + *value
    }

    fold_preserves_order_ids_and_values() -> usize {
        let source = values();
        IndexVec::fold(&source, 0, fold_item)
    }

    observe_and_fold(
        total: usize,
        id: Id<ItemTag>,
        value: &usize
    ) -> usize / {Observe} {
        perform Observe::item(Id::to_usize(id), *value);
        fold_item(total, id, value)
    }

    fold_preserves_effects() -> usize {
        let source = values();
        handle IndexVec::fold(&source, 0, observe_and_fold) {
            Observe::item(id, value) with continuation => {
                id + value + resume(continuation, ())
            }
        }
    }

    checked_fold_item(
        total: usize,
        id: Id<ItemTag>,
        value: &usize
    ) -> Result<usize, usize> {
        if(*value == 5) {
            Result::Err(total)
        } else if(*value == 7) {
            Result::Err(9000 + total)
        } else {
            Result::Ok(fold_item(total, id, value))
        }
    }

    try_fold_stops_at_error() -> usize {
        let source = values();
        handle IndexVec::try_fold(&source, 0, checked_fold_item) {
            Result::Err(total) => total,
            Result::Ok(total) => total
        }
    }

    observe_then_checked_fold(
        total: usize,
        id: Id<ItemTag>,
        value: &usize
    ) -> Result<usize, usize> / {Observe} {
        perform Observe::item(Id::to_usize(id), *value);
        checked_fold_item(total, id, value)
    }

    try_fold_preserves_effects_and_stops() -> usize {
        let source = values();
        handle {
            handle IndexVec::try_fold(&source, 0, observe_then_checked_fold) {
                Result::Err(total) => total,
                Result::Ok(total) => total
            }
        } {
            Observe::item(id, value) with continuation => {
                id + value + resume(continuation, ())
            }
        }
    }

    main() -> () { () }
"#;

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

#[test]
fn borrowed_index_vec_traversal_preserves_ids_values_errors_and_effects() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "index-vec-traversal.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(artifact.clone()).unwrap();

        for (name, expected) in [
            ("for_each_ids_and_values", 77),
            ("try_for_each_stops_at_error", 2),
            ("try_for_each_preserves_effects", 15),
            ("fold_preserves_order_ids_and_values", 2_132_537),
            ("fold_preserves_effects", 2_132_560),
            ("try_fold_stops_at_error", 213),
            ("try_fold_preserves_effects_and_stops", 226),
        ] {
            assert_eq!(
                Vm::new(verified.clone())
                    .run(function_id(&artifact, name), vec![])
                    .unwrap(),
                Value::U64(expected),
                "{optimization_level:?} {name}"
            );
        }
    }
}
