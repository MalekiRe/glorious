use super::*;

#[test]
fn semantic_callable_brands_and_runs_in_evidence_are_fresh_and_sealed() {
    let core = core_for(
        "semantic-callable-brands@0.1.0",
        r#"
            left(value: i64) -> i64 { value }
            right(value: i64) -> i64 { value }
            pub fn main() -> i64 {
                let shared = 1;
                let unique = 2;
                let moved = 3;
                let empty = () -> i64 { 0 };
                let by_shared = () -> i64 { shared };
                let by_unique = () -> i64 { unique = unique + 1; unique };
                let by_move = () -> i64 { move moved };
                left(0) + right(0) + empty() + by_shared() + by_unique() + by_move()
            }
        "#,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let environments = core
        .expressions
        .iter()
        .filter_map(|expression| match &expression.kind {
            CoreKind::Closure { environment, .. } => Some(environment),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(environments.len(), 4, "{core:#?}");
    let named_callables = core
        .expressions
        .iter()
        .filter_map(|expression| match &expression.kind {
            CoreKind::Function { definition, .. } => Some(*definition),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        named_callables.len(),
        2,
        "distinct named callables must retain distinct nominal identities: {core:#?}"
    );
    assert_eq!(
        environments
            .iter()
            .map(|environment| environment.brand)
            .collect::<BTreeSet<_>>()
            .len(),
        environments.len(),
        "each closure must mint a fresh environment brand"
    );
    for environment in &environments {
        assert!(environment.sealed, "{environment:#?}");
        assert!(environment.runs_in.sealed, "{environment:#?}");
        assert_eq!(environment.brand, environment.runs_in.environment);
        assert_eq!(environment.brand.callable, environment.runs_in.callable);
        assert_eq!(environment.post_states, environment.runs_in.post_states);
    }
    assert!(
        environments
            .iter()
            .any(|environment| environment.captures.is_empty()),
        "the empty closure must use the canonical empty environment"
    );
    let capture_modes = environments
        .iter()
        .flat_map(|environment| environment.captures.iter().map(|capture| capture.mode))
        .collect::<BTreeSet<_>>();
    assert!(capture_modes.contains(&CaptureMode::Copy));

    let core_source = fs::read_to_string(crate_path("src/core.rs")).unwrap();
    let types_source = fs::read_to_string(crate_path("src/types.rs")).unwrap();
    for forbidden in ["ReceiverMode", "CallableReceiverMode"] {
        assert!(
            !core_source.contains(forbidden),
            "found {forbidden} in Core"
        );
        assert!(
            !types_source.contains(forbidden),
            "found {forbidden} in types"
        );
    }
}

#[test]
fn semantic_optional_move_capture_forces_an_owned_closure_environment() {
    let source = r#"
            pub fn main() -> i64 {
                let configuration = 41;
                let deferred = move (configuration) { configuration + 1 };
                deferred()
            }
        "#;
    let core = core_for("semantic-optional-move-capture@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let environment = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Closure { environment, .. } => Some(environment),
            _ => None,
        })
        .expect("move capture must elaborate to a closure");
    assert_eq!(
        environment.captures,
        vec![grandiose_stage0::ClosureCapture {
            name: "configuration".into(),
            mode: CaptureMode::Copy,
            ty: grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::I64),
        }],
        "an explicit owned capture copies an unrestricted value into the closure environment",
    );
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_optional_move_capture_copies_a_duplicable_source() {
    let source = r#"
        pub fn main() -> i64 {
            let configuration = 41;
            let deferred = move (configuration) { configuration + 1 };
            configuration + deferred()
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn semantic_inferred_closure_capture_moves_an_owned_nonduplicable_value() {
    assert_semantic_rejection(
        r#"
            struct Ticket {}
            impl Use<[1, 1]> for Ticket {}

            pub fn main() -> i64 {
                let ticket = Ticket {};
                let deferred = () -> Ticket { ticket };
                let again = ticket;
                move deferred;
                move again;
                42
            }
        "#,
        "an inferred owned closure capture moves a non-duplicable source",
        &[&["move", "moved", "use"]],
    );
}

#[test]
fn semantic_optional_move_capture_rejects_nonlocal_names() {
    assert_semantic_rejection(
        r#"
            pub fn main() -> i64 {
                let deferred = move (missing) { 42 };
                deferred()
            }
        "#,
        "closure move captures must name an outer local",
        &[&["closure", "capture"], &["missing", "outer", "local"]],
    );
}

#[test]
fn semantic_plain_owned_arguments_do_not_require_move_spelling() {
    let source = r#"
        struct Ticket {}
        impl Use<[1, 1]> for Ticket {}

        relay(ticket: Ticket) -> Ticket { ticket }

        pub fn main() -> i64 {
            let ticket = Ticket {};
            let ticket = relay(ticket);
            move ticket;
            42
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_plain_owned_argument_cannot_be_used_after_implicit_move() {
    assert_semantic_rejection(
        r#"
            struct Ticket {}
            impl Use<[1, 1]> for Ticket {}

            relay(ticket: Ticket) -> Ticket { ticket }

            pub fn main() -> i64 {
                let ticket = Ticket {};
                let forwarded = relay(ticket);
                let again = relay(ticket);
                move forwarded;
                move again;
                42
            }
        "#,
        "implicit owned argument moves its source",
        &[&["move", "moved", "use"]],
    );
}

#[test]
fn semantic_available_is_affine_intrinsic_evidence_with_affine_erasure_release() {
    let source = r#"
        release<'e, E>(available: Available<'e, E>) ->
        where E: Environment<'e>, E: Use<[0, 1]>
        {
            available_to_unit(available)
        }
        pub main() -> i64 { 42 }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let missing_affine_erasure = r#"
        release<'e, E>(available: Available<'e, E>) ->
        where E: Environment<'e>
        {
            available_to_unit(available)
        }
        pub main() -> i64 { 42 }
    "#;
    assert_semantic_rejection(
        missing_affine_erasure,
        "Available<E> release requires affine erasure evidence",
        &[&["available"], &["use", "affine", "[0,1]", "[0, 1]"]],
    );
}

#[test]
fn semantic_available_and_compiler_evidence_cannot_be_forged() {
    let forged_available = r#"
        struct Empty {}
        pub main() -> i64 {
            let witness = Available<'static, Empty> {};
            42
        }
    "#;
    assert_semantic_rejection(
        forged_available,
        "Available<E> is compiler-generated",
        &[
            &["available"],
            &["forge", "construct", "intrinsic", "compiler"],
        ],
    );

    let forged_refinement = r#"
        struct Empty {}
        pub main() -> i64 {
            let bindings = Bindings<'static, Empty> {};
            42
        }
    "#;
    assert_semantic_rejection(
        forged_refinement,
        "refinement bindings are compiler-generated",
        &[
            &["bindings", "refinement"],
            &["forge", "construct", "intrinsic", "compiler"],
        ],
    );

    for (relation, source) in [
        (
            "Label",
            "struct Ticket {} impl Label<i64> for Ticket {} pub main() -> i64 { 42 }",
        ),
        (
            "Environment",
            "struct Ticket {} impl<'a> Environment<'a> for Ticket {} pub main() -> i64 { 42 }",
        ),
        (
            "Fn",
            "struct Ticket {} impl Fn<()> for Ticket {} pub main() -> i64 { 42 }",
        ),
        (
            "RunsIn",
            concat!(
                "struct Ticket {} struct Env {} ",
                "impl RunsIn<Env, ()> for Ticket {} ",
                "pub main() -> i64 { 42 }",
            ),
        ),
    ] {
        assert_semantic_rejection(
            source,
            "compiler-generated relation cannot be manually implemented",
            &[&[relation], &["compiler", "intrinsic", "sealed", "manual"]],
        );
    }
}

#[test]
fn semantic_manual_use_may_restrict_but_never_widen_structure() {
    let accepted = r#"
        struct Ticket {}
        impl Use<[1, 1]> for Ticket {}
        pub main() -> i64 { 42 }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);

    let widening = r#"
        struct Holder<'a> { value: &'a mut i64 }
        impl<'a> Use<[0, *]> for Holder<'a> {}
        pub main() -> i64 { 42 }
    "#;
    assert_semantic_rejection(
        widening,
        "manual Use implementation cannot widen the structural interval",
        &[
            &["use", "principal"],
            &["widen", "subset", "structural", "interval"],
        ],
    );
}

#[test]
fn semantic_zero_only_principal_use_is_rejected() {
    let source = r#"
        struct Erased {}
        impl Use<[0, 0]> for Erased {}
        pub main() -> i64 { 42 }
    "#;
    assert_semantic_rejection(
        source,
        "zero-only Use is not a public principal contract",
        &[
            &["use", "principal"],
            &["[0, 0]", "[0,0]", "affine", "public"],
        ],
    );
}

#[test]
fn semantic_drop_runs_once_on_normal_and_nonlocal_cleanup() {
    let source = r#"
        struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0, 1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> {
            drop(&mut self) -> {
                *self.target = *self.target + 1;
            }
        }
        pub main() -> i64 {
            let first = 19;
            { let normal = Probe { target: &mut first }; () };
            let second = 20;
            let escaped = @done: i64 {
                let nonlocal = Probe { target: &mut second };
                @done(1);
                0
            };
            first + second + escaped
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(
        outcome.artifact.unwrap().run_i64().unwrap(),
        42,
        "each custom Drop hook must run exactly once on its legal cleanup edge"
    );
}

#[test]
fn semantic_drop_is_zero_use_only_and_cannot_expose_control() {
    let positive_lower = r#"
        struct Ticket {}
        impl Use<[1, 1]> for Ticket {}
        impl Drop for Ticket { drop(&mut self) -> {} }
        pub main() -> i64 { 42 }
    "#;
    assert_semantic_rejection(
        positive_lower,
        "Drop is unavailable to positive-lower types",
        &[&["drop"], &["zero", "[0,0]", "[0, 0]", "lower", "use"]],
    );

    let effectful = r#"
        effect Log { write(); }
        struct Writer {}
        impl Drop for Writer {
            drop(&mut self) -> / {Log} { Log::write() }
        }
        pub main() -> i64 { 42 }
    "#;
    assert_semantic_rejection(
        effectful,
        "Drop cannot expose effects or suspension",
        &[&["drop", "destructor"], &["effect", "suspend", "pure"]],
    );

    let transferring = r#"
        struct Probe {}
        impl Drop for Probe {
            drop(&mut self) -> { @drop(()); }
        }
        pub main() -> i64 { 42 }
    "#;
    assert_semantic_rejection(
        transferring,
        "Drop cannot transfer to an implicit label",
        &[&["drop", "destructor"], &["label", "transfer", "control"]],
    );
}

#[test]
fn semantic_custom_drop_types_cannot_be_partially_moved_or_deconstructed() {
    for source in [
        r#"
            struct Pair { left: i64, right: i64 }
            impl Drop for Pair { drop(&mut self) -> {} }
            pub main() -> i64 {
                let pair = Pair { left: 40, right: 2 };
                move pair.left
            }
        "#,
        r#"
            struct Pair { left: i64, right: i64 }
            impl Drop for Pair { drop(&mut self) -> {} }
            pub main() -> i64 {
                let pair = Pair { left: 40, right: 2 };
                handle pair { Pair { left, right } => left + right }
            }
        "#,
    ] {
        assert_semantic_rejection(
            source,
            "custom-Drop aggregate must remain opaque to consuming projection",
            &[
                &["drop", "destructor"],
                &["partial", "move", "deconstruct", "pattern"],
            ],
        );
    }
}

#[test]
fn semantic_restricted_use_globals_are_rejected() {
    let source = r#"
        struct Ticket {}
        impl Use<[1, 1]> for Ticket {}
        let ticket = Ticket {};
        pub main() -> i64 { 42 }
    "#;
    assert_semantic_rejection(
        source,
        "restricted-use memoized global is outside the G1 language",
        &[
            &["global", "top-level", "memoized"],
            &["use", "quantity", "restricted"],
        ],
    );
}
