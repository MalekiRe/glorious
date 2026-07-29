use grandiose::{
    CompileOptions, OptimizationLevel, compile_bundle_to_bytecode, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
    eval::{Host, Value as RecoveryValue},
    run_bundle,
    source_bundle::{Segment, SourceBundle},
    span::Span,
};
use grandiose_vm::{Value, Vm, verify};

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
            "stored-lifetime recovery test performed a host effect",
            span,
        ))
    }
}

const SHARED: &str = r#"
    struct Cell { value: i64 }
    struct View<'a, T> { private base: &'a T, start: usize }

    make<'a, T>(base: &'a T) -> View<'a, T> {
        View { base: base, start: 0 }
    }

    forward<'a, T>(value: View<'a, T>) -> View<'a, T> {
        move value
    }

    into_base<'a, T>(value: View<'a, T>) -> &'a T {
        value.base
    }

    answer() -> i64 {
        let cell = Cell { value: 42 };
        let view = make(&cell);
        let carried = forward(move view);
        let base = into_base(move carried);
        base.value
    }

    main() -> () { () }
"#;

#[test]
fn stored_shared_origin_survives_construction_forwarding_and_projection() {
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "stored-shared.glorious",
            SHARED,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"));
        let answer = artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(answer, vec![])
                .unwrap(),
            Value::I64(42),
            "{level:?}"
        );
    }
}

#[test]
fn lifetime_parameterized_enum_carries_and_iterates_a_borrowed_slice() {
    let source = r#"
        enum BorrowedItems<'a, T> {
            Items(Slice<'a, T>)
        }

        borrow_items<'a, T>(
            values: &'a Vec<T>
        ) -> BorrowedItems<'a, T> {
            handle Slice::subslice(
                Vec::as_slice(values),
                0,
                Vec::len(values)
            ) {
                Result::Err(_) => unreachable(),
                Result::Ok(items) => BorrowedItems::Items(items)
            }
        }

        add_item(total: usize, item: &usize) -> usize {
            total + *item
        }

        sum_items<'a>(
            view: BorrowedItems<'a, usize>
        ) -> usize {
            handle view {
                BorrowedItems::Items(items) =>
                    Slice::fold(items, 0, add_item)
            }
        }

        answer() -> usize {
            let values = Vec::new();
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 3);
            Vec::push(&mut values, 5);
            sum_items(borrow_items(&values))
        }

        main() -> () { () }
    "#;

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "stored-slice-enum.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(answer, vec![])
                .unwrap(),
            Value::U64(10),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn enum_alternatives_can_borrow_distinct_fields_of_one_parameter() {
    let source = r#"
        struct Sources {
            left: Vec<u32>,
            right: Vec<u8>
        }

        enum BorrowedChoice<'a> {
            Left(Slice<'a, u32>),
            Right(Slice<'a, u8>)
        }

        borrow_choice<'a>(
            sources: &'a Sources,
            choose_left: Bool
        ) -> BorrowedChoice<'a> {
            if(choose_left) {
                BorrowedChoice::Left(Vec::as_slice(&sources.left))
            } else {
                BorrowedChoice::Right(Vec::as_slice(&sources.right))
            }
        }

        main() -> () { () }
    "#;

    let artifact = compile_source_to_bytecode("borrowed-choice.glorious", source)
        .unwrap_or_else(|errors| panic!("{errors:#?}"));
    let function = artifact
        .functions
        .iter()
        .position(|function| function.name == "borrow_choice")
        .unwrap() as u32;
    let contract = artifact
        .reference_return_contracts
        .iter()
        .find(|contract| contract.function == function)
        .expect("the compiler emitted an aggregate lifetime contract");
    assert_eq!(contract.routes.len(), 2);
    assert_ne!(
        contract.routes[0].result_path,
        contract.routes[1].result_path
    );
    assert!(contract.routes.iter().all(|route| matches!(
        &route.origin,
        grandiose_vm::bytecode::ReferenceReturnOrigin::Parameter { parameter: 0, .. }
    )));
    verify(artifact).expect("each borrowed alternative has an exact source-field route");
}

#[test]
fn generic_borrowed_payload_accepts_a_monomorphic_alias_argument() {
    let source = r#"
        struct ItemTag {}
        type ItemId = Id<ItemTag>;

        enum BorrowedIds<'a> {
            Items(Slice<'a, ItemId>)
        }

        borrow_ids<'a>(values: &'a Vec<ItemId>) -> BorrowedIds<'a> {
            BorrowedIds::Items(Vec::as_slice(values))
        }

        main() -> () { () }
    "#;

    compile_source_to_bytecode("borrowed-alias-payload.glorious", source)
        .unwrap_or_else(|errors| panic!("{errors:#?}"));
}

#[test]
fn private_stored_reference_cannot_be_projected_outside_its_authority_domain() {
    let bundle = SourceBundle::new(
        Segment::new("views.glorious", "struct View<'a,T>{private base:&'a T}\n"),
        Segment::new(
            "user.glorious",
            "steal<'a>(value:View<'a,i64>)->&'a i64{value.base}\nmain()->(){()}\n",
        ),
        [],
    );
    let errors = compile_bundle_to_bytecode(&bundle)
        .expect_err("a private stored reference escaped its defining source segment");
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("private field `base`")),
        "{errors:#?}"
    );
}

#[test]
fn stored_regions_enforce_escape_covariance_and_unique_invariance() {
    let accepted = r#"
        struct View<'a, T> { base: &'a T }
        shorten<'long, 'short>(value: View<'long, i64>) -> View<'short, i64>
            where 'long: 'short { move value }
        main() -> () { () }
    "#;
    compile_source_to_bytecode("stored-covariance.glorious", accepted).unwrap();
    compile_source_to_bytecode(
        "stored-nested-covariance.glorious",
        "struct Cov<T>{value:T} shorten<'long,'short>(value:Cov<&'long i64>)->Cov<&'short i64> where 'long:'short {move value} main()->(){()}",
    )
    .unwrap();
    for (name, source, expected) in [
        (
            "stored-escape.glorious",
            "struct View<'a,T>{base:&'a T} bad<'a>(base:&'a i64)->View<'static,i64>{View{base:base}} main()->(){()}",
            "outlive",
        ),
        (
            "stored-no-outlives.glorious",
            "struct View<'a,T>{base:&'a T} bad<'long,'short>(value:View<'long,i64>)->View<'short,i64>{move value} main()->(){()}",
            "outlive",
        ),
        (
            "stored-unrelated-supplier.glorious",
            "struct View<'a,T>{base:&'a T} bad<'long,'short>(wrong:View<'long,i64>, unrelated:View<'short,i64>)->View<'short,i64>{move wrong} main()->(){()}",
            "outlive",
        ),
        (
            "stored-unique-region-invariant.glorious",
            "struct ViewMut<'a,T>{base:&'a mut T} bad<'long,'short>(value:ViewMut<'long,i64>)->ViewMut<'short,i64> where 'long:'short {move value} main()->(){()}",
            "outlive",
        ),
        (
            "stored-nested-unique-invariant.glorious",
            "struct Cell<T>{value:&mut T} bad<'long,'short>(value:Cell<&'long i64>)->Cell<&'short i64> where 'long:'short {move value} main()->(){()}",
            "outlive",
        ),
        (
            "stored-unique-referent-invariant.glorious",
            "struct Left{n:i64} struct Right{n:i64} struct ViewMut<'a,T>{base:&'a mut T} bad<'a>(value:ViewMut<'a,Left>)->ViewMut<'a,Right>{move value} main()->(){()}",
            "expected ViewMut",
        ),
    ] {
        let errors = match compile_source_to_bytecode(name, source) {
            Ok(_) => panic!("{name}: an invalid stored-reference region conversion compiled"),
            Err(errors) => errors,
        };
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn stored_lifetime_must_be_bound_by_its_nominal() {
    let errors = compile_source_to_bytecode(
        "unbound-stored.glorious",
        "struct Bad<T>{base:&'missing T} main()->(){()}",
    )
    .expect_err("an unbound stored lifetime compiled");
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("containing nominal")),
        "{errors:#?}"
    );
}

#[test]
fn unique_origin_remains_live_while_stored_in_an_aggregate() {
    let source = r#"
        struct Cell { value: i64 }
        struct ViewMut<'a, T> { base: &'a mut T }
        make<'a, T>(base: &'a mut T) -> ViewMut<'a, T> {
            ViewMut { base: base }
        }
        into_base<'a, T>(value: ViewMut<'a, T>) -> &'a mut T {
            let ViewMut { base } = move value;
            base
        }
        bad() -> i64 {
            let cell = Cell { value: 7 };
            let view = make(&mut cell);
            let observed = cell.value;
            let base = into_base(move view);
            observed + base.value
        }
        main() -> () { () }
    "#;
    let errors = compile_source_to_bytecode("stored-unique-loan.glorious", source)
        .expect_err("the owner was accessed while its unique loan lived in ViewMut");
    assert!(
        errors
            .iter()
            .any(|error| { error.message.contains("borrow") || error.message.contains("loan") }),
        "{errors:#?}"
    );
}

#[test]
fn stored_reference_construction_and_projection_have_recovery_parity() {
    let bundle = SourceBundle::raw_for_conformance(
        Segment::new("empty.glorious", ""),
        Segment::new(
            "stored-recovery.glorious",
            r#"
                struct Cell { value: i64 }
                struct Slice<'a> { base: &'a Cell }
                make<'a>(base: &'a Cell) -> Slice<'a> { Slice { base: base } }
                into_base<'a>(value: Slice<'a>) -> &'a Cell { value.base }
                main() -> i64 {
                    let cell = Cell { value: 42 };
                    let view = make(&cell);
                    let base = into_base(move view);
                    base.value
                }
            "#,
        ),
        [],
    );
    assert_eq!(
        run_bundle(&bundle, vec![], &mut NoHost).unwrap(),
        RecoveryValue::Int(42)
    );
}
