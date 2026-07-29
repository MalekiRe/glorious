use grandiose::{compile_source_to_bytecode, compile_source_to_phases};
use grandiose_vm::{Artifact, Value, Vm, verify};

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

fn run(source: &str, name: &str) -> Value {
    let artifact = compile_source_to_bytecode("effect-aware-fn.glorious", source).unwrap();
    let function = function_id(&artifact, name);
    Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
}

fn assert_rejected(source: &str, required_words: &[&str]) {
    let diagnostics =
        compile_source_to_bytecode("bad-effect-aware-fn.glorious", source).unwrap_err();
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.span.is_some()),
        "every rejection must retain source provenance: {diagnostics:#?}"
    );
    assert!(
        diagnostics.iter().any(|diagnostic| {
            required_words.iter().all(|word| {
                diagnostic
                    .message
                    .to_lowercase()
                    .contains(&word.to_lowercase())
            })
        }),
        "missing diagnostic containing {required_words:?}: {diagnostics:#?}"
    );
}

#[test]
fn lazy_boolean_blocks_preserve_nominal_capture_types() {
    let source = r#"
        struct ExprId { index: u32 }
        impl Use<[0,infinity]> for ExprId {}

        index(value: ExprId) -> u32 { value.index }
        captured(left: ExprId) -> Bool {
            false or { index(left) == 7 }
        }
        main() -> { captured(ExprId { index: 7 }); () }
    "#;
    compile_source_to_bytecode("lazy-nominal-capture.glorious", source).unwrap();
}

#[test]
fn unrestricted_nominal_observe_captures_keep_value_transport() {
    let source = r#"
        struct ExprId { index: u32 }
        impl Use<[0,infinity]> for ExprId {}

        index(value: ExprId) -> u32 { value.index }
        apply<F>(body: F) -> u32 where F: Fn<(), Output = u32> { body() }
        captured(left: ExprId) -> u32 { apply({ => index(left) }) }
        main() -> { captured(ExprId { index: 7 }); () }
    "#;
    compile_source_to_bytecode("nominal-observe-capture.glorious", source).unwrap();
}

#[test]
fn structural_if_branches_keep_the_enclosing_result_context() {
    let source = r#"
        classify(value: u8) -> Option<u8> {
            if(value == 0) { Result::Ok(7) } else { Result::Err(()) }
        }
        main() -> { classify(0); () }
    "#;
    compile_source_to_bytecode("structural-if-context.glorious", source).unwrap();
}

#[test]
fn standard_if_over_option_resolves_its_instantiated_result_constructors() {
    let source = r#"
        struct Payload { value: u32 }
        impl Use<[0,infinity]> for Payload {}

        present(value: Option<Payload>) -> Option<u32> {
            if(value) { 1 }
        }
        main() -> {
            present(Result::Ok(Payload { value: 7 }));
            ()
        }
    "#;
    compile_source_to_bytecode("if-option-result-construction.glorious", source).unwrap();
}

#[test]
fn nested_source_boolean_if_uses_structural_lowering_before_generic_inlining() {
    let source = r#"
        choose(outer: Bool, inner: Bool) -> Option<u32> {
            if(outer) {
                Result::Ok(1)
            } else {
                if(inner) { Result::Ok(2) } else { Result::Err(()) }
            }
        }
        main() -> {
            choose(false, true);
            ()
        }
    "#;
    compile_source_to_bytecode("nested-structural-if.glorious", source).unwrap();
}

#[test]
fn lazy_structural_if_numeric_literals_use_the_later_binding_context() {
    let source = r#"
        consume(value: u32) -> u32 { value }
        choose(condition: Bool) -> u32 {
            let copy = if(condition) { 0 } else { 1 };
            consume(copy)
        }
        main() -> { choose(true); () }
    "#;
    compile_source_to_bytecode("structural-if-numeric-context.glorious", source).unwrap();
}

#[test]
fn lazy_numeric_local_uses_a_later_usize_call_without_identity_wrapper() {
    let source = r#"
        consume_usize(value: usize) -> usize { value }
        choose(condition: Bool) -> usize {
            let sign = if(condition) { 1 } else { 0 };
            let candidate = 1 + sign;
            consume_usize(sign);
            candidate
        }
        main() -> { choose(true); () }
    "#;
    compile_source_to_phases("later-usize-call-without-wrapper.glorious", source).unwrap();
}

#[test]
fn lazy_numeric_local_uses_a_later_u8_field_without_identity_wrapper() {
    let source = r#"
        struct GenericParam { kind_code: u8 }
        choose(condition: Bool) -> GenericParam {
            let kind = if(condition) {
                if(false) { 3 } else { 0 }
            } else {
                1
            };
            kind == 0;
            GenericParam { kind_code: kind }
        }
        main() -> { choose(true); () }
    "#;
    compile_source_to_phases("later-u8-field-without-wrapper.glorious", source).unwrap();
}

#[test]
fn numeric_later_use_hint_stops_at_a_sequential_shadow() {
    let source = r#"
        make_u64() -> u64 { 2 }
        consume_u64(value: u64) -> u64 { value }
        choose(condition: Bool) -> i64 {
            let copy = if(condition) { 0 } else { 1 };
            let result = 1 + copy;
            let copy = make_u64();
            consume_u64(copy);
            result
        }
        main() -> { choose(true); () }
    "#;
    compile_source_to_phases("numeric-later-use-shadow.glorious", source).unwrap();
}

#[test]
fn later_binding_context_stops_at_a_sequential_shadow() {
    let source = r#"
        consume_u32(value: u32) -> u32 { value }
        consume_u64(value: u64) -> u64 { value }
        make_u64() -> u64 { 2 }
        choose(condition: Bool) {
            let copy = if(condition) { 0 } else { 1 };
            consume_u32(copy);
            let copy = make_u64();
            consume_u64(copy);
            ()
        }
        choose_nested(condition: Bool) {
            let copy = if(condition) { 0 } else { 1 };
            {
                let copy = make_u64();
                consume_u64(copy);
                ()
            };
            consume_u32(copy);
            ()
        }
        main() -> { choose(true); choose_nested(false); () }
    "#;
    compile_source_to_phases("later-binding-sequential-shadow.glorious", source).unwrap();
}

#[test]
fn lazy_structural_if_numeric_literals_use_the_assignment_place_type() {
    let source = r#"
        assign(values: &mut Vec<u32>, condition: Bool) {
            *Vec::index_mut(values, 0) = if(condition) { 1 } else { 0 };
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("structural-if-assignment-context.glorious", source).unwrap();
}

#[test]
fn associated_fn_effect_rows_accept_empty_protocol_and_alias_forms() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        cases Asking = {Ask};

        pure<F>(body: F) -> i64
            where F: Fn<(), Output=i64, Effects={}> { body() }
        direct<F>(body: F) -> i64 / {Ask}
            where F: Fn<(), Output=i64, Effects={Ask}> { body() }
        aliased<F>(body: F) -> i64 / {Asking}
            where F: Fn<(), Output=i64, Effects=Asking> { body() }

        pure_answer() -> i64 { pure({ => 42 }) }
        direct_answer() -> i64 / {Ask} { direct({ => perform Ask::ask() }) }
        alias_answer() -> i64 / {Ask} { aliased({ => perform Ask::ask() }) }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("associated-effect-rows.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&artifact, "pure_answer"), vec![])
            .unwrap(),
        Value::I64(42)
    );
    for name in ["direct_answer", "alias_answer"] {
        assert_eq!(
            artifact.functions[function_id(&artifact, name) as usize]
                .outward_protocols
                .len(),
            1
        );
    }
}

#[test]
fn open_fn_effect_rows_bind_canonical_residuals_without_dropping_the_prefix() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        effect Trace { [1,1] trace() -> i64 }

        invoke<F, e: EffectRow>(body: F) -> i64
            where F: Fn<(), Output=i64, Effects={Ask | e}> { body() }
        invoke_bare<F, e: EffectRow>(body: F) -> i64
            where F: Fn<(), Output=i64, Effects=e> { body() }

        ask_only() -> i64 / {Ask} {
            invoke({ => perform Ask::ask() })
        }
        ask_and_trace() -> i64 / {Ask, Trace} {
            invoke({ => { perform Ask::ask(); perform Trace::trace() } })
        }
        trace_bare() -> i64 / {Trace} {
            invoke_bare({ => perform Trace::trace() })
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("open-fn-effect-rows.glorious", source).unwrap();
    let mut invoke_rows = artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$specialization$invoke#"))
        .map(|function| function.outward_protocols.len())
        .collect::<Vec<_>>();
    invoke_rows.sort_unstable();
    assert_eq!(invoke_rows, [1, 2]);
    assert_eq!(
        artifact.functions[function_id(&artifact, "trace_bare") as usize]
            .outward_protocols
            .len(),
        1
    );

    let unresolved = r#"
        effect Ask { [1,1] ask() -> i64 }
        bad<e: EffectRow>() -> i64 / {| e} { 0 }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("unresolved-outward-row.glorious", unresolved).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("outward rows must be closed")),
        "{errors:#?}"
    );
}

#[test]
fn repeated_open_row_variables_require_equal_residuals() {
    let shared = r#"
        effect Ask { [1,1] ask() -> i64 }
        effect Trace { [1,1] trace() -> i64 }
        pair<F, G, e: EffectRow>(left: F, right: G) -> i64
            where F: Fn<(), Output=i64, Effects={| e}>,
                  G: Fn<(), Output=i64, Effects={| e}> { left() + right() }
    "#;
    let positive = format!(
        "{shared} good() -> i64 / {{Ask}} {{ pair({{ => perform Ask::ask() }}, {{ => perform Ask::ask() }}) }} main()->{{()}}"
    );
    compile_source_to_bytecode("equal-open-row-residuals.glorious", &positive).unwrap();

    let negative = format!(
        "{shared} bad() -> i64 / {{Ask,Trace}} {{ pair({{ => perform Ask::ask() }}, {{ => perform Trace::trace() }}) }} main()->{{()}}"
    );
    let errors = compile_source_to_bytecode("conflicting-open-row-residuals.glorious", &negative)
        .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("conflicting residual rows")),
        "{errors:#?}"
    );
}

#[test]
fn open_row_known_members_are_canonical_across_source_order() {
    let source = |row: &str| {
        format!(
            r#"
        effect Ask {{ [1,1] ask() -> i64 }}
        effect Trace {{ [1,1] trace() -> i64 }}
        invoke<F, e: EffectRow>(body:F)->i64
            where F:Fn<(),Output=i64,Effects={row}> {{ body() }}
        answer()->i64 / {{Ask,Trace}} {{ invoke({{ => perform Ask::ask() }}) }}
        main()->{{()}}
    "#
        )
    };
    let left =
        compile_source_to_bytecode("open-row-order-left.glorious", &source("{Ask, Trace | e}"))
            .unwrap();
    let right =
        compile_source_to_bytecode("open-row-order-right.glorious", &source("{Trace, Ask | e}"))
            .unwrap();
    assert_eq!(left.encode(), right.encode());
}

#[test]
fn associated_item_kinds_and_exact_effect_rows_are_enforced() {
    assert_rejected(
        r#"
            effect Ask { [1,1] ask() -> i64 }
            bad<F>(body: F) -> i64 where F: Fn<(), Output={Ask}> { 0 }
            main() -> { () }
        "#,
        &["Output", "type"],
    );
    assert_rejected(
        r#"
            bad<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects=i64> { 0 }
            main() -> { () }
        "#,
        &["Effects", "effect row"],
    );
    assert_rejected(
        r#"
            bad<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Missing}> { 0 }
            main() -> { () }
        "#,
        &["unknown", "effect"],
    );
    assert_rejected(
        r#"
            effect Ask { [1,1] ask() -> i64 }
            pure<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={}> { body() }
            bad() -> i64 / {Ask} { pure({ => perform Ask::ask() }) }
            main() -> { () }
        "#,
        &["effect", "row"],
    );
}

#[test]
fn omitted_effects_infer_and_keep_pure_and_effectful_specializations_distinct() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        invoke<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }

        pure_answer() -> i64 { invoke({ => 42 }) }
        effectful_answer() -> i64 / {Ask} { invoke({ => perform Ask::ask() }) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("inferred-effects.glorious", source).unwrap();
    let invoke = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$specialization$invoke#"))
        .collect::<Vec<_>>();
    assert_eq!(
        invoke.len(),
        2,
        "effect rows participate in specialization identity"
    );
    assert!(
        invoke
            .iter()
            .any(|function| function.outward_protocols.is_empty())
    );
    assert!(
        invoke
            .iter()
            .any(|function| function.outward_protocols.len() == 1)
    );

    let closures = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$closure$"))
        .collect::<Vec<_>>();
    assert_eq!(closures.len(), 2);
    assert!(
        closures
            .iter()
            .any(|function| function.outward_protocols.is_empty())
    );
    assert!(
        closures
            .iter()
            .any(|function| function.outward_protocols.len() == 1)
    );

    let verified = verify(phases.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified.clone())
            .run(function_id(&phases.artifact, "pure_answer"), vec![])
            .unwrap(),
        Value::I64(42)
    );
    assert_eq!(
        phases.artifact.functions[function_id(&phases.artifact, "effectful_answer") as usize]
            .outward_protocols
            .len(),
        1
    );
}

#[test]
fn generic_forwarders_propagate_rows_and_an_internal_handler_closes_them() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        forward_one<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }
        forward_two<F>(body: F) -> i64 where F: Fn<(), Output=i64> {
            forward_one(body)
        }
        close<F>(body: F) -> i64
            where F: Fn<(), Output=i64, Effects={Ask}> {
            handle { body() } {
                Ask::ask() with k => resume(k, 42)
            }
        }
        forward_close<F>(body: F) -> i64
            where F: Fn<(), Output=i64, Effects={Ask}> {
            close(body)
        }
        outward() -> i64 / {Ask} { forward_two({ => perform Ask::ask() }) }
        outward_answer() -> i64 {
            handle { outward() } {
                Ask::ask() with k => resume(k, 42)
            }
        }
        closed_answer() -> i64 { close({ => perform Ask::ask() }) }
        forwarded_closed_answer() -> i64 {
            forward_close({ => perform Ask::ask() })
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("forwarded-effects.glorious", source).unwrap();
    for prefix in [
        "$specialization$forward_one#",
        "$specialization$forward_two#",
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name.starts_with(prefix))
            .unwrap_or_else(|| panic!("missing `{prefix}`"));
        assert_eq!(function.outward_protocols.len(), 1, "{prefix}");
    }
    let close = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$specialization$close#"))
        .unwrap();
    assert!(close.outward_protocols.is_empty());
    let forward_close = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$specialization$forward_close#"))
        .unwrap();
    assert!(
        forward_close.outward_protocols.is_empty(),
        "a transitive forward into an internally handling callable must remain closed"
    );

    let verified = verify(phases.artifact.clone()).unwrap();
    for name in ["outward_answer", "closed_answer", "forwarded_closed_answer"] {
        assert_eq!(
            Vm::new(verified.clone())
                .run(function_id(&phases.artifact, name), vec![])
                .unwrap(),
            Value::I64(42),
            "{name}"
        );
    }
}

#[test]
fn exhaustive_enum_handler_matrix_closes_forwarded_effect_but_partial_coverage_does_not() {
    let source = r#"
        enum Branch { Left, Right }
        effect Ask { [1,1] ask(branch: Branch) -> i64 }
        effect Multi {
            [1,1] first(branch: Branch) -> i64
            [1,1] second() -> i64
        }

        close<F>(body: F) -> i64
            where F: Fn<(), Output=i64, Effects={Ask}> {
            handle { body() } {
                Ask::ask(Branch::Left) with k => resume(k, 41),
                Ask::ask(Branch::Right) with k => resume(k, 42)
            }
        }
        forward_close<F>(body: F) -> i64
            where F: Fn<(), Output=i64, Effects={Ask}> { close(body) }

        partial_matrix<F>(body: F) -> i64 / {Ask}
            where F: Fn<(), Output=i64, Effects={Ask}> {
            handle { body() } {
                Ask::ask(Branch::Left) with k => resume(k, 41)
            }
        }
        missing_operation<F>(body: F) -> i64 / {Multi}
            where F: Fn<(), Output=i64, Effects={Multi}> {
            handle { body() } {
                Multi::first(Branch::Left) with k => resume(k, 41),
                Multi::first(Branch::Right) with k => resume(k, 42)
            }
        }

        answer() -> i64 {
            forward_close({ => perform Ask::ask(Branch::Right) })
        }
        partial_answer() -> i64 / {Ask} {
            partial_matrix({ => perform Ask::ask(Branch::Left) })
        }
        missing_answer() -> i64 / {Multi} {
            missing_operation({ => perform Multi::first(Branch::Left) })
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("enum-handler-effects.glorious", source).unwrap();
    for prefix in ["$specialization$close#", "$specialization$forward_close#"] {
        let function = phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name.starts_with(prefix))
            .unwrap_or_else(|| panic!("missing `{prefix}`"));
        assert!(
            function.outward_protocols.is_empty(),
            "the exhaustive enum matrix must close the forwarded effect: {prefix}"
        );
    }
    for prefix in [
        "$specialization$partial_matrix#",
        "$specialization$missing_operation#",
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name.starts_with(prefix))
            .unwrap_or_else(|| panic!("missing `{prefix}`"));
        assert_eq!(
            function.outward_protocols.len(),
            1,
            "partial pattern/operation coverage must keep the protocol outward: {prefix}"
        );
    }

    let verified = verify(phases.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&phases.artifact, "answer"), vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn contextual_blocks_are_eager_for_scalars_and_delayed_only_for_fn_evidence() {
    let source = r#"
        scalar(value: i64) -> i64 { value }
        delayed<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }
        eager_answer() -> i64 { scalar({ 40 + 2 }) }
        delayed_answer() -> i64 { delayed({ 40 + 2 }) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("contextual-eager-delayed.glorious", source).unwrap();
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$closure$"))
            .count(),
        1,
        "the scalar block must not become a closure"
    );
    let verified = verify(phases.artifact.clone()).unwrap();
    for name in ["eager_answer", "delayed_answer"] {
        assert_eq!(
            Vm::new(verified.clone())
                .run(function_id(&phases.artifact, name), vec![])
                .unwrap(),
            Value::I64(42)
        );
    }
}

#[test]
fn operator_spelling_has_no_lazy_semantics_and_old_lazy_fixity_is_rejected() {
    let source = r#"
        infixl 5 lazy;
        lazy(left: i64, right: i64) -> i64 { left + right }
        answer() -> i64 { 40 lazy { 2 } }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));

    assert_rejected(
        r#"
            infixr 1 otherwise lazy;
            otherwise(left: i64, right: i64) -> i64 { left }
            main() -> { () }
        "#,
        &["expected", ";"],
    );
}

#[test]
fn arbitrary_operator_rhs_is_delayed_only_by_its_fn_constraint() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        infixr 1 keep;
        keep<F>(left: i64, right: F) -> i64
            where F: Fn<(), Output=i64, Effects={Ask}> { left }
        answer() -> i64 { 42 keep { perform Ask::ask() } }
        main() -> { () }
    "#;
    assert_eq!(
        run(source, "answer"),
        Value::I64(42),
        "constructing an uninvoked effectful RHS must remain pure"
    );
}

#[test]
fn invoked_effectful_rhs_performs_only_at_invocation() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        invoke<F>(body: F) -> i64 / {Ask}
            where F: Fn<(), Output=i64, Effects={Ask}> { body() }
        answer() -> i64 {
            handle { invoke({ => perform Ask::ask() }) } {
                Ask::ask() with k => resume(k, 42)
            }
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn handle_call_with_nested_explicit_closure_keeps_the_handler_delimiter() {
    let source = r#"
        effect Stop { stop() -> ! }
        invoke<F>(body: F) -> i64 / {Stop}
            where F: Fn<(), Output=i64, Effects={Stop}> { body() }
        answer() -> i64 {
            handle invoke({ => perform Stop::stop() }) {
                Stop::stop() => 42
            }
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn effect_aware_specialization_is_deterministic_across_declaration_order() {
    let first = r#"
        effect Ask { [1,1] ask() -> i64 }
        invoke<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }
        pure() -> i64 { invoke({ => 42 }) }
        effectful() -> i64 / {Ask} { invoke({ => perform Ask::ask() }) }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        effectful() -> i64 / {Ask} { invoke({ => perform Ask::ask() }) }
        pure() -> i64 { invoke({ => 42 }) }
        invoke<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }
        effect Ask { [1,1] ask() -> i64 }
    "#;
    assert_eq!(
        compile_source_to_bytecode("ordered.glorious", first)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("reordered.glorious", reordered)
            .unwrap()
            .encode()
    );
}

#[test]
fn exact_linear_capture_moved_by_one_invocation_is_accepted() {
    let source = r#"
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        once<F>(body: F) -> i64 where F: Fn<(), Output=i64, Effects={}> {
            body()
        }
        answer() -> i64 {
            let ticket = Ticket { marker: 42 };
            once({ => {
                let Ticket { marker } = move ticket;
                marker
            } })
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn mutually_exclusive_invocations_join_exact_linear_capture_by_hull() {
    let source = r#"
        enum Side { Left, Right }
        effect Dispatch { select(side: Side) -> ! }
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}

        choose<F>(side: Side, body: F) -> i64
            where F: Fn<(), Output=i64, Effects={}> {
            handle perform Dispatch::select(side) {
                Dispatch::select(Side::Left) => body(),
                Dispatch::select(Side::Right) => body()
            }
        }
        answer() -> i64 {
            let ticket = Ticket { marker: 42 };
            choose(Side::Left, { => {
                let Ticket { marker } = move ticket;
                marker
            } })
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn distinct_handler_operations_share_one_exact_linear_incoming_environment() {
    let source = r#"
        effect Pick { left() -> ! right() -> ! }
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}

        left_answer(ticket: Ticket) -> i64 {
            handle perform Pick::left() {
                Pick::left() => { let Ticket { marker } = move ticket; marker },
                Pick::right() => { let Ticket { marker } = move ticket; marker }
            }
        }
        right_answer(ticket: Ticket) -> i64 {
            handle perform Pick::right() {
                Pick::left() => { let Ticket { marker } = move ticket; marker },
                Pick::right() => { let Ticket { marker } = move ticket; marker }
            }
        }
        make_left() -> i64 { left_answer(Ticket { marker: 41 }) }
        make_right() -> i64 { right_answer(Ticket { marker: 42 }) }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("cross-operation-environment.glorious", source).unwrap();
    let bytes = artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);

    let mut hostile = artifact.clone();
    let ordinary_function = function_id(&hostile, "make_left");
    let shared = hostile
        .code
        .iter_mut()
        .find_map(|instruction| match instruction {
            grandiose_vm::Instruction::MakeHandlerShared { functions, .. } => Some(functions),
            _ => None,
        })
        .expect("cross-operation handler must use one shared environment");
    shared[0] = ordinary_function;
    assert!(
        verify(hostile).is_err(),
        "verifier accepted a non-clause function"
    );

    let verified = verify(artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified.clone())
            .run(function_id(&artifact, "make_left"), vec![])
            .unwrap(),
        Value::I64(41)
    );
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&artifact, "make_right"), vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn unused_effectful_callback_stays_pure_through_transitive_forwarding() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        ignore<F>(body: F) -> i64
            where F: Fn<(), Output=i64, Effects={Ask}> { 42 }
        forward<F>(body: F) -> i64
            where F: Fn<(), Output=i64, Effects={Ask}> { ignore(body) }
        answer() -> i64 { forward({ => perform Ask::ask() }) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("unused-effectful-forward.glorious", source).unwrap();
    for prefix in ["$specialization$ignore#", "$specialization$forward#"] {
        let specialization = phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name.starts_with(prefix))
            .unwrap_or_else(|| panic!("missing `{prefix}`"));
        assert!(
            specialization.outward_protocols.is_empty(),
            "forwarding an uninvoked callback leaked its latent row through `{prefix}`"
        );
    }
    assert!(
        phases.artifact.functions[function_id(&phases.artifact, "answer") as usize]
            .outward_protocols
            .is_empty()
    );
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(function_id(&phases.artifact, "answer"), vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn exact_linear_capture_cannot_be_abandoned_or_invoked_twice() {
    assert_rejected(
        r#"
            struct Ticket { marker: i64 }
            impl Use<[1,1]> for Ticket {}
            ignore<F, R>(body: F) -> i64 where F: Fn<(), Output=R> { 42 }
            bad(ticket: Ticket) -> i64 {
                ignore({ => { let Ticket { marker } = move ticket; marker } })
            }
            main() -> { () }
        "#,
        &["actual use", "[1,1]"],
    );
    assert_rejected(
        r#"
            struct Ticket { marker: i64 }
            impl Use<[1,1]> for Ticket {}
            twice<F>(body: F) -> i64 where F: Fn<(), Output=i64> {
                body() + body()
            }
            bad(ticket: Ticket) -> i64 {
                twice({ => { let Ticket { marker } = move ticket; marker } })
            }
            main() -> { () }
        "#,
        &["actual use", "[1,1]", "more than once"],
    );
}

#[test]
fn borrowed_capture_cannot_escape_but_custom_drop_is_not_blanket_rejected() {
    assert_rejected(
        r#"
            retain<F>(body: F) -> F where F: Fn<(), Output=i64> { body }
            bad() -> i64 {
                let escaped = {
                    let value = 42;
                    let reference = &value;
                    retain({ => *reference })
                };
                escaped()
            }
            main() -> { () }
        "#,
        &["closure", "reference"],
    );

    let accepted = r#"
        struct Guard { marker: i64 }
        impl Drop for Guard { drop(&mut self) -> { self.marker; () } }
        invoke<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }
        answer() -> i64 {
            let guard = Guard { marker: 42 };
            invoke({ => guard.marker })
        }
        main() -> { () }
    "#;
    assert_eq!(run(accepted, "answer"), Value::I64(42));
}
