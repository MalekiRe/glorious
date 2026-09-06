use grandiose_stage0::{
    BodySyntax, CallableBrand, CallableId, CaptureEnvironment, CaptureMode, CapturePostState,
    ClosureCapture, ConstInferVar, ConstKind, CoreExpr, CoreHandlerResumption, CoreId, CoreKind,
    CorePattern, CorePlace, DeclarationScan, DefKey, DefinitionIndex, Digest, EffectInstance,
    EffectRow, EffectRowProjection, EffectTail, EffectVar, ElaboratedInterface, EnvironmentBrand,
    EscapeFlow, FileKey, FlowEventKind, GenericArgument, InferVar, InterfaceSet, LexedFile,
    Lifetime, LogicalPath, MirInstruction, MirLowering, MirPattern, PackageKey, PlaceFlow,
    Quantity, RunsInEvidence, ScalarType, Span, StructuralU32Expr, Type, TypedBody, UseFlow,
    implementation_method_key,
};
use std::collections::{BTreeMap, BTreeSet};

fn flow_for(package_name: &str, source: &str) -> PlaceFlow {
    let package = PackageKey(package_name.into());
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
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    PlaceFlow::analyze(&core)
}

fn core_and_signatures_for(package_name: &str, source: &str) -> (TypedBody, ElaboratedInterface) {
    let package = PackageKey(package_name.into());
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
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    (
        TypedBody::elaborate(
            definition,
            &body,
            &DefinitionIndex::from_interface(&interface),
            &signatures,
        ),
        signatures,
    )
}

fn core_for(package_name: &str, source: &str) -> TypedBody {
    core_and_signatures_for(package_name, source).0
}

/// Source MIR retains destruction intent until concrete instance discovery.
/// Keep template proof checks above this boundary, then exercise the real
/// specialization/glue pipeline and independent artifact verifier below it.
fn compile_with_destruction(source: &str, template: &grandiose_stage0::MirFunction) -> grandiose_stage0::VerifiedVmProgram {
    assert!(matches!(grandiose_stage0::emit_vm(template),
        Err(grandiose_stage0::VmArtifactError::MalformedEncoding {
            message: "unelaborated destruction reached VM lowering",
        })));
    let package = PackageKey("core-concrete-destruction@0.1.0".into());
    let request = grandiose_stage0::CompilationRequest {
        build: grandiose_stage0::CompilerBuildIdentity::stage0(Digest::of_bytes(b"core-concrete-destruction")),
        mode: grandiose_stage0::CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![grandiose_stage0::SourceInput::new(package,
            LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(), codegen_options: BTreeMap::new(),
        capability_manifest: vec![], runtime_manifest: None,
    };
    let outcome = grandiose_stage0::StageZeroCompiler::new().compile(request).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    grandiose_stage0::decode_and_verify_program(&outcome.artifact.unwrap().canonical_bytes()).unwrap()
}

#[test]
fn contextual_call_to_a_shadowing_non_callable_reports_an_error_instead_of_panicking() {
    let core = core_for(
        "shadowed-call@0.1.0",
        "pub fn target() -> i64 { 42 } pub fn main() -> i64 { let target = 7; target() }",
    );
    assert!(core.diagnostics.iter().any(|diagnostic| diagnostic.code == "G4105"));
}

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
            .any(|expression| matches!(expression.kind, CoreKind::IntrinsicCall { .. }))
    );
}

#[test]
fn generic_record_view_over_a_direct_array_borrow_is_elaborated() {
    let source = "struct View<'a, T> { storage: &'a Array<T> } pub fn main<T>(storage: &Array<T>) -> View<'_, T> { View<'_, T> { storage: storage } }";
    let core = core_for("generic-array-view@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_core_contextualizes_late_generic_integer_literals_from_prior_arguments() {
    for (name, float, bits, mask, scalar) in [
        (
            "f32",
            "f32",
            "__g1_f32_to_bits",
            "2139095040",
            ScalarType::U32,
        ),
        (
            "f64",
            "f64",
            "__g1_f64_to_bits",
            "9218868437227405312",
            ScalarType::U64,
        ),
    ] {
        let source = format!(
            "fn {bits}(value: {float}) -> {scalar_name} {{ () }}\
             fn __g1_int_bit_and<T>(left: T, right: T) -> T {{ () }}\
             bit_and<T>(left: T, right: T) -> T {{ __g1_int_bit_and(move left, move right) }}\
             pub fn main(value: {float}) -> Bool {{\
                 bit_and({bits}(move value), {mask}) != {mask}\
             }}",
            scalar_name = match scalar {
                ScalarType::U32 => "u32",
                ScalarType::U64 => "u64",
                _ => unreachable!(),
            },
        );
        let core = core_for(&format!("core-canonical-{name}-finite"), &source);
        assert!(
            core.diagnostics.is_empty(),
            "{name}: {:#?}",
            core.diagnostics
        );
        assert_eq!(
            core.expression(core.root).ty,
            Type::Scalar(ScalarType::Bool)
        );
        assert!(core.expressions.iter().any(|expression| {
            matches!(&expression.kind, CoreKind::Literal(value) if value == mask)
                && expression.ty == Type::Scalar(scalar)
        }));
    }
}

#[test]
fn typed_core_opens_intrinsic_fn_where_contract_for_generic_local_calls() {
    let core = core_for(
        "core-intrinsic-fn-contract",
        "pub fn main<F>(body: F) -> i64 where F: Fn<(), Output = i64, Effects = {}> { body() }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(
        core.expressions
            .iter()
            .any(|expression| matches!(expression.kind, CoreKind::Call { .. }))
    );
    assert_eq!(core.expression(core.root).ty, Type::Scalar(ScalarType::I64));
}

#[test]
fn typed_core_rejects_a_forged_unfrozen_top_level_value_initializer() {
    let package = PackageKey("core-forged-let-initializer@0.1.0".into());
    let source = "let answer = 40 + 2; pub fn main() -> i64 { answer }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    // `elaborate` alone is the pre-initialization frozen interface. The
    // service normally fills this value's inferred type before bodies are
    // read; retaining the incomplete map simulates forged metadata.
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4102"),
        "unfrozen top-level value metadata reached executable Core: {:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_core_opens_intrinsic_label_where_contract_for_generic_escape_calls() {
    let core = core_for(
        "core-intrinsic-label-contract",
        "pub fn main<L>(exit: L) -> ! where L: Label<i64> { exit(7) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(expression.kind, CoreKind::Call { .. }) && expression.ty == Type::Never
    }));
}

#[test]
fn declared_result_expectations_flow_through_blocks_and_structured_values() {
    let core = core_for(
        "core-structured-expected-types@0.1.0",
        "pub fn main() -> ((i64) -> i64, Array<i64>) { ({ value => value }, []) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.ty,
            Type::Callable {
                parameters,
                result,
                ..
            } if parameters == &vec![Type::Scalar(ScalarType::I64)]
                && **result == Type::Scalar(ScalarType::I64)
        )
    }));
    assert!(core.expressions.iter().any(|expression| {
        expression.ty == Type::Array(Box::new(Type::Scalar(ScalarType::I64)))
            && matches!(expression.kind, CoreKind::Array(ref values) if values.is_empty())
    }));
}

#[test]
fn typed_core_retains_explicit_nominal_arguments_on_record_and_enum_construction() {
    let core = core_for(
        "core-explicit-nominal-construction@0.1.0",
        "pub struct Packet<T> { value: T } pub enum Result<T> { Ok(T) } pub fn main() -> i64 { let packet = Packet<i64> { value: 7 }; let result = Result<i64>::Ok(9); let matches = result is Result<i64>::Ok(_); packet.value }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let expected = vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))];
    assert!(core.expressions.iter().any(|expression| {
        matches!(&expression.ty, Type::Nominal { arguments, .. } if arguments == &expected)
            && matches!(expression.kind, CoreKind::Record { .. })
    }));
    assert!(core.expressions.iter().any(|expression| {
        matches!(&expression.ty, Type::Nominal { arguments, .. } if arguments == &expected)
            && matches!(expression.kind, CoreKind::Enum { .. })
    }));
}

#[test]
fn typed_core_accepts_multiple_explicit_type_arguments_on_constructors_and_calls() {
    let core = core_for(
        "core-multiple-explicit-generic-arguments@0.1.0",
        "pub enum Result<T, E> { Ok(T), Err(E) } pub fn make<T, E>(value: T) -> Result<T, E> { Result::Ok(value) } pub fn main() -> Result<i64, ()> { let direct = Result<i64, ()>::Ok(7); make<i64, ()>(7) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let expected = vec![
        GenericArgument::Type(Type::Scalar(ScalarType::I64)),
        GenericArgument::Type(Type::Unit),
    ];
    assert!(core.expressions.iter().any(|expression| {
        matches!(&expression.ty, Type::Nominal { arguments, .. } if arguments == &expected)
            && matches!(expression.kind, CoreKind::Enum { .. })
    }));
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::Function { arguments, .. } if arguments == &expected
        )
    }));
}

#[test]
fn mixed_nominal_constructor_arguments_reach_the_runtime_layout_boundary() {
    let core = core_for(
        "core-mixed-nominal-construction@0.1.0",
        "effect Trace { note(); } pub struct Mixed<'a, e: EffectRow, n: u32, q: Quantity, T> {} pub fn main() -> i64 { Mixed<'static, {Trace}, 7, [1, 2], i64> {}; 0 }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4123"),
        "mixed identity did not reach the type-only layout boundary: {:#?}",
        core.diagnostics
    );
    assert!(
        !core
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4185"),
        "mixed nominal arguments were rejected before nominal kind validation: {:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_core_retains_quantity_arguments_on_enum_construction() {
    let core = core_for(
        "core-quantity-enum-construction@0.1.0",
        "pub enum Packet<q: Quantity, T> { Value(T) } pub fn main() -> i64 { let packet = Packet<[1, 1], i64>::Value(41); 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let expected = vec![
        GenericArgument::ConstQuantity(Quantity::new(1, Some(1)).unwrap()),
        GenericArgument::Type(Type::Scalar(ScalarType::I64)),
    ];
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::Enum { .. }
                if matches!(&expression.ty, Type::Nominal { arguments, .. } if arguments == &expected)
        )
    }));
}

#[test]
fn mixed_nominal_pattern_arguments_are_checked_against_subject_identity() {
    let core = core_for(
        "core-mixed-nominal-pattern@0.1.0",
        "effect Trace { note(); } pub struct Mixed<'a, e: EffectRow, n: u32, q: Quantity, T> {} pub fn main(value: Mixed<'static, {Trace}, 7, [1, 2], i64>) -> bool { value is Mixed<'static, {Trace}, 8, [1, 2], i64> {} }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4216"),
        "mixed nominal pattern identity mismatch was not diagnosed: {:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_core_retains_zonked_direct_call_specialization_arguments() {
    let core = core_for(
        "core-direct-instance@0.1.0",
        "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(42) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::Function { arguments, .. }
                if arguments.as_slice()
                    == [GenericArgument::Type(Type::Scalar(ScalarType::I64))]
        )
    }));
}

#[test]
fn typed_core_zonks_implicit_const_callable_specialization_arguments() {
    let source = "pub struct Tag<n: u32> {} pub struct Budget<q: Quantity> {} pub fn retain<n: u32, q: Quantity>(value: Tag<n>, budget: Budget<q>) -> Tag<n> { value } pub fn main(value: Tag<7>, budget: Budget<[2, 4]>) -> i64 { retain(value, budget); 0 }";
    let core = core_for("core-implicit-const-call@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(
        core.expressions.iter().any(|expression| {
            matches!(
                &expression.kind,
                CoreKind::Function { arguments, .. }
                    if arguments == &vec![
                        GenericArgument::ConstU32(7),
                        GenericArgument::ConstQuantity(Quantity::new(2, Some(4)).unwrap()),
                    ]
            )
        }),
        "implicit const callable substitution did not freeze to the source-proven values: {core:#?}"
    );
}

#[test]
fn typed_core_rejects_an_unconstrained_implicit_const_callable_argument() {
    let core = core_for(
        "core-unconstrained-implicit-const-call@0.1.0",
        "pub fn unconstrained<n: u32>() -> i64 { 42 } pub fn main() -> i64 { unconstrained() }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4116"),
        "unresolved const hole escaped Typed Core sealing: {core:#?}"
    );
}

#[test]
fn typed_core_retains_explicit_direct_callable_generic_arguments() {
    let core = core_for(
        "core-explicit-direct-generic@0.1.0",
        "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity<i64>(42) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::Function { arguments, .. }
                if arguments.as_slice()
                    == [GenericArgument::Type(Type::Scalar(ScalarType::I64))]
        )
    }));
}

#[test]
fn typed_core_substitutes_explicit_quantity_callable_arguments() {
    let core = core_for(
        "core-explicit-quantity-generic@0.1.0",
        "pub struct Budget<q: Quantity> {} pub fn identity<q: Quantity>(value: Budget<q>) -> Budget<q> { value } pub fn main(value: Budget<[1, 2]>) -> Budget<[1, 2]> { identity<[1, 2]>(value) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::Function { arguments, .. }
                if arguments.as_slice()
                    == [GenericArgument::ConstQuantity(Quantity::new(1, Some(2)).unwrap())]
        )
    }));
}

#[test]
fn typed_core_retains_explicit_trait_method_generic_arguments() {
    let core = core_for(
        "core-explicit-trait-generic@0.1.0",
        "trait Identity<T> { fn identity(value: T) -> T; } impl<T> Identity<T> for T { fn identity(value: T) -> T { value } } pub fn main() -> i64 { Identity<i64>::identity(42) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::TraitMethod {
                trait_arguments,
                method_arguments,
                ..
            } if trait_arguments.as_slice()
                == [GenericArgument::Type(Type::Scalar(ScalarType::I64))]
                && method_arguments.is_empty()
        )
    }));
}

#[test]
fn direct_callable_type_prefix_infers_trailing_types_from_arguments_and_context() {
    for source in [
        "fn pair<T, S>(a: S, b: T) -> (S, T) { (a, b) } pub fn main() -> (i64, u32) { pair<u32>(7, 9) }",
        "fn choose<T, S>(value: T, other: S) -> S { other } pub fn main() -> u32 { choose<i64>(7, 9) }",
        "pub fn choose<T, S>(value: T, other: S) -> S { other } pub fn main() -> u32 { crate::choose<i64>(7, 9) }",
    ] {
        let core = core_for("partial-generics@0.1.0", source);
        assert!(core.diagnostics.is_empty(), "{source}: {:#?}", core.diagnostics);
        assert!(core.expressions.iter().any(|expression| matches!(&expression.kind,
            CoreKind::Function { arguments, .. } if arguments.len() == 2
                && arguments.iter().all(|a| matches!(a, GenericArgument::Type(Type::Scalar(_)))))));
    }
}

#[test]
fn direct_callable_type_prefix_preserves_kind_arity_and_fixed_argument_checks() {
    for source in [
        "fn identity<T>(x: T) -> T { x } pub fn main() -> i64 { identity<i64, i64>(1) }",
        "fn identity<T, q: Quantity>(x: T) -> T { x } pub fn main() -> i64 { identity<i64>(1) }",
        "fn identity<T, S>(x: T, y: S) -> T { x } pub fn main() -> i64 { identity<u32>(1, 2) }",
    ] {
        let core = core_for("partial-generics-reject@0.1.0", source);
        assert!(!core.diagnostics.is_empty(), "must reject {source}");
    }
}

#[test]
fn typed_core_selects_methods_inherited_through_a_supertrait() {
    let core = core_for(
        "core-supertrait-method@0.1.0",
        "trait Parent<T> { fn identity(value: T) -> T; } trait Child<U>: Parent<U> {} impl Parent<i64> for i64 { fn identity(value: i64) -> i64 { value } } impl Child<i64> for i64 {} pub fn main() -> i64 { Child<i64>::identity(42) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(
        core.expressions
            .iter()
            .any(|expression| { matches!(expression.kind, CoreKind::TraitMethod { .. }) })
    );
}

#[test]
fn typed_core_requires_child_evidence_for_inherited_qualified_methods() {
    for (package, child_impl, expected) in [
        (
            "core-parent-only-inherited-method@0.1.0",
            "",
            "no implementation provides the qualified trait method",
        ),
        (
            "core-negative-child-inherited-method@0.1.0",
            "impl !Child<i64> for i64 {}",
            "qualified trait method is refuted by a negative implementation",
        ),
    ] {
        let source = format!(
            "trait Parent<T> {{ fn relay(value: i64) -> i64; }} trait Child<U>: Parent<U> {{}} impl Parent<i64> for i64 {{ fn relay(value: i64) -> i64 {{ value }} }} {child_impl} pub fn main() -> i64 {{ Child<i64>::relay(42) }}"
        );
        let core = core_for(package, &source);
        assert!(
            core.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains(expected)),
            "missing {expected}: {:#?}",
            core.diagnostics
        );
    }
}

#[test]
fn typed_core_selects_aliased_hrtb_inherited_method_values_from_child_assumptions() {
    // The only evidence for generic `T` is the lexical Child bound. The
    // inherited method belongs to a Parent blanket that additionally needs
    // Gate, so this checks transitive Child assumptions discharge both the
    // owner relation and selected-rule obligation without making parent-only
    // assumptions sufficient in the reverse case.
    let core = core_for(
        "core-aliased-hrtb-inherited-method-assumption@0.1.0",
        "trait Gate {} trait Parent<U> { fn relay<'a>(receiver: Self, value: &'a i64) -> i64; } trait Child<U>: Parent<U> + Gate {} impl<T> Parent<i64> for T where T: Gate { fn relay<'a>(receiver: T, value: &'a i64) -> i64 { *value } } pub fn main<T>() -> for<'a> (T, &'a i64) -> i64 where T: Child<i64> { Child<i64>::relay }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::TraitMethod { .. }
                if matches!(expression.ty, Type::Callable { safety: grandiose_stage0::Safety::Safe, lifetime_binders: 1, .. })
        )
    }), "Child-bound inherited HRTB method value was not retained in Core: {:#?}", core.expressions);
}

#[test]
fn typed_core_normalizes_concrete_associated_effect_rows_on_method_values() {
    let core = core_for(
        "core-trait-method-associated-effect-row@0.1.0",
        "effect Trace { note() -> i64; } trait Capability { type Effects: EffectRow; } impl Capability for i64 { type Effects = {Trace}; } trait Relay { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects }; } impl Relay for i64 { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects } { Trace::note() } } pub fn apply(callable: (i64) -> i64 / Trace) -> i64 / Trace { callable(0) } pub fn main() -> i64 { handle apply(Relay::relay) { Trace::note() with k => k(42) } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::TraitMethod { .. }
                if matches!(
                    &expression.ty,
                    Type::Callable { effects, .. }
                        if effects.projections.is_empty() && effects.effects.len() == 1
                )
        )
    }));
}

#[test]
fn projected_trait_effect_handler_statements_rejoin_their_lexical_suffix_in_mir() {
    let source = "effect Trace { [1,1] note() -> i64; } trait Capability { type Effects: EffectRow; } impl Capability for i64 { type Effects = {Trace}; } trait Relay { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects }; } impl Relay for i64 { fn relay(receiver: i64) -> i64 / { <i64 as Capability>::Effects } { Trace::note() } } pub fn apply(callable: (i64) -> i64 / Trace) -> i64 / Trace { callable(0) } pub fn main() -> i64 { let invoke = apply; handle invoke(Relay::relay) { Trace::note() with k => k(41) }; let suffix = (value: i64) -> i64 { value + 1 }; suffix(41) }";
    let package = PackageKey("core-projected-statement-handler@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let index = DefinitionIndex::from_interface(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(definition, &body, &index, &signatures);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        &expression.kind,
        CoreKind::Call { callee, .. }
            if matches!(
                &core.expression(*callee).ty,
                Type::Callable { effects, .. }
                    if effects.projections.is_empty() && effects.effects.len() == 1
            )
    )), "the selected associated row must be concrete before statement MIR lowering: {:#?}", core.expressions);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        definition.key,
        &core,
        &flow,
        &BTreeMap::new(),
        Some(&signatures),
    );
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "projected statement handler must lower: {:#?}",
            lowered.diagnostics
        )
    });
    mir.validate().unwrap_or_else(|error| {
        panic!("projected statement handler MIR validates: {error}\n{mir:#?}")
    });
    let entry = &mir.blocks[mir.entry.0 as usize].instructions;
    let install = entry
        .iter()
        .position(|instruction| matches!(instruction, MirInstruction::InstallHandler { .. }))
        .expect("statement handler frame");
    let call = entry
        .iter()
        .position(|instruction| matches!(instruction, MirInstruction::CallIndirect { .. }))
        .expect("opaque projected callable call");
    let uninstall = entry
        .iter()
        .position(|instruction| matches!(instruction, MirInstruction::UninstallHandler))
        .expect("statement handler normal cleanup");
    assert!(install < call && call < uninstall, "the handler must remain active through the opaque call: {mir:#?}");
    assert!(entry[uninstall + 1..]
        .iter()
        .any(|instruction| matches!(instruction, MirInstruction::CallIndirect { .. })),
        "the lexical suffix call must begin only after handler cleanup: {mir:#?}");
}

#[test]
fn typed_core_freezes_open_hrtb_effect_rows_selected_by_a_positive_trait_impl() {
    let core = core_for(
        "core-positive-hrtb-effect-row-selection@0.1.0",
        "effect Trace<T> { [1,1] note(value: T) -> i64; } trait Gate { type Effects<'a, e: EffectRow>: EffectRow; fn relay<'a, e: EffectRow>(value: &'a i64) -> i64 / { <Self as Gate>::Effects<'a, e> } where Self: Gate<Effects<'a, e> = {Trace<i64>, | e}>; } trait Top: Gate {} type Callback<E: EffectRow> = for<'a> (&'a i64) -> i64 / { <i64 as Gate>::Effects<'a, E> }; impl Gate for i64 { type Effects<'a, e: EffectRow> = {Trace<i64>, | e}; fn relay<'a, e: EffectRow>(value: &'a i64) -> i64 / { <i64 as Gate>::Effects<'a, e> } where i64: Gate<Effects<'a, e> = {Trace<i64>, | e}> { *value } } impl Top for i64 where i64: Gate {} pub fn main<e: EffectRow>() -> Callback<e> { Top::relay }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(matches!(core.expression(core.root).ty, Type::Callable { safety: grandiose_stage0::Safety::Safe, lifetime_binders: 1, .. }));
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::TraitMethod { .. }
                if matches!(
                    &expression.ty,
                    Type::Callable { safety: grandiose_stage0::Safety::Safe, lifetime_binders: 1, effects, .. }
                        if effects.effects.is_empty()
                            && effects.projections.len() == 1
                            && matches!(effects.projections[0].item_arguments.as_slice(), [GenericArgument::Lifetime(Lifetime::Bound { .. }), GenericArgument::EffectRow(EffectRow { tail: Some(EffectTail::Generic(0)), .. })])
                )
        )
    }), "Core must retain the selected HRTB row and its caller-owned generic tail: {:#?}", core.expressions);
}

#[test]
fn typed_core_accepts_generic_subtrait_impls_proven_by_their_where_contract() {
    let core = core_for(
        "core-generic-supertrait-where@0.1.0",
        "trait Gate {} trait Parent<T> { fn identity(value: T) -> T; } trait Child<T>: Parent<T> {} impl Gate for i64 {} impl<T> Parent<T> for T where T: Gate { fn identity(value: T) -> T { value } } impl<T> Child<T> for T where T: Gate {} pub fn main() -> i64 { Child<i64>::identity(42) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(
        core.expressions
            .iter()
            .any(|expression| matches!(expression.kind, CoreKind::TraitMethod { .. }))
    );
}

#[test]
fn typed_core_normalizes_all_selected_items_through_recursive_generic_supertraits() {
    let core = core_for(
        "core-recursive-generic-supertrait-projections@0.1.0",
        "effect Trace<n: u32, T> { [1,1] note(value: T) -> i64; } trait Root<T> { const Width: u32; type Item<U, n: u32>; type Effects<U, n: u32>: EffectRow; } trait Left<T>: Root<T> + Right<T> { fn relay<U>(receiver: T, value: U) -> <Self as Root<T>>::Item<U, <Self as Root<T>>::Width> / { <Self as Root<T>>::Effects<U, <Self as Root<T>>::Width> }; } trait Right<T>: Root<T> {} impl<T> Root<T> for i64 { const Width = 7; type Item<U, n: u32> = i64; type Effects<U, n: u32> = {Trace<n, U>}; } impl<T> Right<T> for i64 {} impl<T> Left<T> for i64 where i64: Right<T> { fn relay<U>(receiver: T, value: U) -> i64 / Trace<7, U> { receiver; 42 } } pub fn main() -> i64 / Trace<7, i64> { Left<i64>::relay(0, 42) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert_eq!(core.expression(core.root).ty, Type::Scalar(ScalarType::I64));
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::TraitMethod { .. }
                if matches!(
                    &expression.ty,
                    Type::Callable { result, effects, .. }
                        if **result == Type::Scalar(ScalarType::I64)
                            && effects.projections.is_empty()
                            && effects.effects.len() == 1
                )
        )
    }), "selected type, effect, and const projections must be frozen in Core: {:#?}", core.expressions);
}

#[test]
fn typed_core_selects_inherited_associated_consts_for_nominal_arithmetic() {
    let core = core_for(
        "core-inherited-associated-const-nominal@0.1.0",
        "effect Trace<n: u32, T> { [1,1] note(value: T) -> i64; } trait Parent<T> { const Width: u32; type Effects<'a>: EffectRow; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { const Width = 7; type Effects<'a> = {Trace<<i64 as Parent<i64>>::Width, i64>}; } impl Child<i64> for i64 where i64: Parent<i64> {} struct Witness<n: u32> { value: i64 } type Callback = for<'a> (&'a i64) -> i64 / { <i64 as Child<i64>>::Effects<'a> }; pub fn main() -> i64 { let witness = Witness<<i64 as Child<i64>>::Width> { value: 42 }; witness.value }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert_eq!(core.expression(core.root).ty, Type::Scalar(ScalarType::I64));
    assert!(core.expressions.iter().any(|expression| {
        matches!(expression.kind, CoreKind::Record { .. })
            && matches!(expression.ty, Type::Nominal { .. })
    }), "the inherited constant must materialize a nominal constructor: {:#?}", core.expressions);
}

#[test]
fn typed_core_refutes_negative_child_inherited_type_effect_and_const_projections() {
    // `Child` inherits all three items from Parent.  Its negative impl must
    // remain authoritative at each Core boundary rather than allowing the
    // selected Parent implementation to provide a back door.
    let core = core_for(
        "core-negative-inherited-projections@0.1.0",
        "effect Trace { note() -> i64; } trait Parent<T> { const Width: u32; type Item; type Effects: EffectRow; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { const Width = 7; type Item = i64; type Effects = {Trace}; } impl !Child<i64> for i64 {} struct Witness<n: u32> { value: i64 } pub fn main() -> <i64 as Child<i64>>::Item / { <i64 as Child<i64>>::Effects } { let witness = Witness<<i64 as Child<i64>>::Width> { value: 42 }; witness.value }",
    );
    let messages = core
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "associated type projection is refuted by a negative implementation",
        "associated effect-row projection is refuted by a negative implementation",
        "associated constant projection is refuted by a negative implementation",
    ] {
        assert!(
            messages.iter().any(|message| message.contains(expected)),
            "missing {expected}: {:#?}",
            core.diagnostics
        );
    }
}

#[test]
fn typed_core_rejects_parent_only_inherited_type_effect_and_const_projections() {
    // Parent's implementation does not establish the distinct Child
    // capability through which each projection is written.
    let core = core_for(
        "core-unimplemented-child-projections@0.1.0",
        "effect Trace { note() -> i64; } trait Parent<T> { const Width: u32; type Item; type Effects: EffectRow; } trait Child<T>: Parent<T> {} impl Parent<i64> for i64 { const Width = 7; type Item = i64; type Effects = {Trace}; } struct Witness<n: u32> { value: i64 } pub fn main() -> <i64 as Child<i64>>::Item / { <i64 as Child<i64>>::Effects } { let witness = Witness<<i64 as Child<i64>>::Width> { value: 42 }; witness.value }",
    );
    let messages = core
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "no implementation can normalize this associated type projection",
        "no implementation can normalize this associated effect-row projection",
        "no implementation can normalize this associated constant",
    ] {
        assert!(
            messages.iter().any(|message| message.contains(expected)),
            "missing {expected}: {:#?}",
            core.diagnostics
        );
    }
}

#[test]
fn typed_core_materializes_defaulted_nominal_items_before_partial_move_analysis() {
    let source = "struct Token {} struct Packet<T> { head: T, tail: i64 } trait Mark: Use<[0, 1]> {} impl<T> Use<[0, 1]> for Packet<T> where T: Mark {} impl<T> Drop for Packet<T> where T: Mark { drop(&mut self) -> {} } trait Family { type Item<T> = Packet<T>; } impl Family for i64 {} fn make<T>(value: T) -> <i64 as Family>::Item<T> { Packet<T> { head: value, tail: 2 } } pub fn main() -> i64 { let packet = make<Token>(Token {}); move packet.head; packet.tail + 40 }";
    let core = core_for("core-defaulted-nominal-partial-move@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert_eq!(core.expression(core.root).ty, Type::Scalar(ScalarType::I64));
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            expression.kind,
            CoreKind::Move(value)
                if matches!(core.expression(value).kind, CoreKind::Field { .. })
        )
    }), "the defaulted nominal projection must materialize to a movable field place: {:#?}", core.expressions);
    let flow = flow_for("core-defaulted-nominal-partial-move@0.1.0", source);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
}

#[test]
fn recovered_source_elaborates_to_core_error_and_is_rejected_before_mir() {
    let source = "pub fn main() -> i64 { let = ; }";
    let core = core_for("core-recovered-source@0.1.0", source);
    assert!(core.recovered);
    assert!(
        core.expressions
            .iter()
            .any(|expression| matches!(expression.kind, CoreKind::Error))
    );
    assert!(
        !core
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4101"),
        "parser recovery must not become an unsupported-Core diagnostic: {:#?}",
        core.diagnostics
    );

    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"core-recovered-source")),
        &core,
        &flow,
    );
    assert!(lowered.function.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6000")
    );
}

#[test]
fn typed_core_validation_rejects_dangling_expression_edges() {
    let package = PackageKey("core-validation@0.1.0".into());
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Block(vec![CoreId(1)]),
            ty: Type::Unit,
            span: Span {
                file: FileKey::new(&package, "src/main.glorious"),
                start: 0,
                end: 1,
            },
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };

    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4180"),
        "dangling Typed Core edge must be rejected at the Core boundary"
    );
}

#[test]
fn typed_core_projection_validation_rechecks_frozen_trait_evidence() {
    let package = PackageKey("core-projection-obligation-validation@0.1.0".into());
    let source = "trait Marker { type Item; } pub fn main() -> i64 { 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface =
        InterfaceSet::collect(package.clone(), "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let marker = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Marker"))
        .expect("Marker definition")
        .key;
    let span = Span {
        file,
        start: 0,
        end: 1,
    };
    let projection = Type::Projection {
        subject: Box::new(Type::Generic(0)),
        trait_definition: marker,
        trait_arguments: vec![],
        name: "Item".into(),
        item_generic_kinds: vec![],
        item_arguments: vec![],
    };
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![("value".into(), Type::Generic(0))],
        expressions: vec![CoreExpr {
            kind: CoreKind::Local("value".into()),
            ty: projection,
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(body.validate().is_empty());
    assert!(
        body.validate_projection_obligations(&signatures, &[])
            .iter()
            .any(|diagnostic| diagnostic.code == "G4190"),
        "forged symbolic Core must not bypass the frozen trait obligation"
    );
    assert!(
        body.validate_projection_obligations(
            &signatures,
            &[(
                Type::Generic(0),
                grandiose_stage0::ElaboratedTraitReference {
                    definition: marker,
                    arguments: vec![],
                },
            )],
        )
        .is_empty(),
        "the lexical where evidence must remain available after Core freezes"
    );
}

#[test]
fn typed_core_rejects_alias_spelled_delayed_effect_projection_metadata() {
    let package = PackageKey("core-alias-delayed-effect-projection@0.1.0".into());
    let source = "type Count = i64; trait Capability<T> { type Effects: EffectRow; } struct Value {} impl Capability<i64> for Value { type Effects = {}; } struct Carrier<e: EffectRow> {} pub fn main() -> i64 { 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let key = |name: &str| {
        interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .expect("fixture declaration")
            .key
    };
    let span = Span {
        file,
        start: 0,
        end: 1,
    };
    let effect_row = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![EffectRowProjection {
            subject: Box::new(Type::Nominal {
                definition: key("Value"),
                arguments: vec![],
            }),
            trait_definition: key("Capability"),
            trait_arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
            name: "Effects".into(),
            item_generic_kinds: vec![],
            item_arguments: vec![],
        }],
        tail: None,
    }
    .canonicalized();
    let mut body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Literal("0".into()),
            ty: Type::Nominal {
                definition: key("Carrier"),
                arguments: vec![GenericArgument::EffectRow(effect_row)],
            },
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(
        body.validate_projection_obligations(&signatures, &[])
            .is_empty(),
        "canonical delayed effect projection lost its selected evidence"
    );
    let Type::Nominal { arguments, .. } = &mut body.expressions[0].ty else {
        unreachable!("fixture carrier")
    };
    let GenericArgument::EffectRow(row) = &mut arguments[0] else {
        unreachable!("fixture row")
    };
    row.projections[0].trait_arguments[0] = GenericArgument::Type(Type::Nominal {
        definition: key("Count"),
        arguments: vec![],
    });
    assert!(
        body.validate_projection_obligations(&signatures, &[])
            .iter()
            .any(|diagnostic| diagnostic.code == "G4190"),
        "forged alias-spelled delayed projection bypassed frozen Core evidence"
    );
}

#[test]
fn typed_core_rechecks_hrtb_effect_projection_evidence_in_function_metadata() {
    let package = PackageKey("core-hrtb-frozen-effect-evidence@0.1.0".into());
    let source = "type Count = i64; trait Capability<T> { type Effects: EffectRow; } struct Value {} impl Capability<i64> for Value { type Effects = {}; } pub fn main() -> i64 { 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let key = |name: &str| {
        interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .expect("fixture declaration")
            .key
    };
    let row = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![EffectRowProjection {
            subject: Box::new(Type::Nominal {
                definition: key("Value"),
                arguments: vec![],
            }),
            trait_definition: key("Capability"),
            trait_arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
            name: "Effects".into(),
            item_generic_kinds: vec![],
            item_arguments: vec![],
        }],
        tail: None,
    }
    .canonicalized();
    let span = Span {
        file,
        start: 0,
        end: 1,
    };
    let mut body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Function {
                definition: key("main"),
                arguments: vec![GenericArgument::Type(Type::Callable {
                    safety: grandiose_stage0::Safety::Safe,
                    lifetime_binders: 1,
                    parameters: vec![Type::Reference {
                        mutability: grandiose_stage0::Mutability::Shared,
                        lifetime: Lifetime::Bound { depth: 0, index: 0 },
                        referent: Box::new(Type::Unit),
                    }],
                    result: Box::new(Type::Unit),
                    effects: row,
                    invocation: Quantity::ONCE,
                })],
                host_import: None,
            },
            ty: Type::Unit,
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(body.validate().is_empty(), "{:#?}", body.validate());
    assert!(
        body.validate_projection_obligations(&signatures, &[])
            .is_empty(),
        "a scoped HRTB callback must preserve valid delayed effect-row evidence"
    );
    let CoreKind::Function { arguments, .. } = &mut body.expressions[0].kind else {
        unreachable!("fixture function metadata")
    };
    let GenericArgument::Type(Type::Callable { effects, .. }) = &mut arguments[0] else {
        unreachable!("fixture HRTB callable")
    };
    effects.projections[0].trait_arguments[0] = GenericArgument::Type(Type::Nominal {
        definition: key("Count"),
        arguments: vec![],
    });
    assert!(
        body.validate_projection_obligations(&signatures, &[])
            .iter()
            .any(|diagnostic| diagnostic.code == "G4190"),
        "a forged nested HRTB effect-row projection must not bypass frozen evidence"
    );
}

#[test]
fn typed_core_validation_rejects_impossible_structural_projection() {
    let package = PackageKey("core-structural-validation@0.1.0".into());
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Field {
                base: CoreId(0),
                index: 1,
                field_count: 1,
            },
            ty: Type::Unit,
            span: Span {
                file: FileKey::new(&package, "src/main.glorious"),
                start: 0,
                end: 1,
            },
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };

    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4183"),
        "invalid structural arity must be rejected before MIR lowering"
    );
}

#[test]
fn typed_core_validation_rejects_out_of_range_nominal_pattern_fields() {
    let mut body = core_for(
        "core-pattern-arity-validation@0.1.0",
        "pub struct Pair { left: i64 } pub fn main(value: Pair) -> bool { value is Pair { left: _ } }",
    );
    let pattern = body
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::PatternTest { pattern, .. } => Some(pattern),
            _ => None,
        })
        .expect("source is-pattern must elaborate to Core");
    let CorePattern::Record {
        field_count,
        fields,
        ..
    } = pattern
    else {
        panic!("source record pattern must preserve its nominal shape")
    };
    assert_eq!(*field_count, 1);
    fields[0].index = 1;

    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4183"),
        "forged Core nominal pattern field must be rejected before MIR lowering"
    );
}

#[test]
fn typed_core_validation_rejects_nominal_pattern_field_type_forgery() {
    let mut body = core_for(
        "core-pattern-layout-validation@0.1.0",
        "pub struct Pair { left: i64, right: bool } pub fn main(value: Pair) -> bool { value is Pair { left: _, right: _ } }",
    );
    let pattern = body
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::PatternTest { pattern, .. } => Some(pattern),
            _ => None,
        })
        .expect("source is-pattern must elaborate to Core");
    let CorePattern::Record {
        field_types,
        fields,
        ..
    } = pattern
    else {
        panic!("source record pattern must preserve its nominal layout")
    };
    assert_eq!(field_types[0], Type::Scalar(ScalarType::I64));
    fields[0].ty = Type::Scalar(ScalarType::Bool);

    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4183"),
        "an in-range Core field cannot be relabelled with another layout slot type"
    );
}

#[test]
fn typed_core_validation_rejects_inference_hidden_in_closure_metadata() {
    let package = PackageKey("core-metadata-inference@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![
            CoreExpr {
                kind: CoreKind::Closure {
                    callable: CallableId(0),
                    parameters: vec![],
                    environment: CaptureEnvironment {
                        brand: EnvironmentBrand {
                            owner: grandiose_stage0::DefKey(grandiose_stage0::Digest::of_bytes(
                                b"core-test",
                            )),
                            callable: CallableId(0),
                        },
                        captures: vec![ClosureCapture {
                            name: "captured".into(),
                            mode: CaptureMode::SharedBorrow,
                            ty: Type::Infer(InferVar(7)),
                        }],
                        post_states: vec![CapturePostState {
                            name: "captured".into(),
                            mode: CaptureMode::SharedBorrow,
                        }],
                        runs_in: RunsInEvidence {
                            environment: EnvironmentBrand {
                                owner: grandiose_stage0::DefKey(
                                    grandiose_stage0::Digest::of_bytes(b"core-test"),
                                ),
                                callable: CallableId(0),
                            },
                            callable: CallableId(0),
                            effects: EffectRow::empty(),
                            post_states: vec![CapturePostState {
                                name: "captured".into(),
                                mode: CaptureMode::SharedBorrow,
                            }],
                            sealed: true,
                        },
                        sealed: true,
                    },
                    body: CoreId(1),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Literal("0".into()),
                ty: Type::Scalar(grandiose_stage0::ScalarType::I64),
                span,
            },
        ],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };

    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4181"),
        "inference hidden in Core metadata must not reach lowering"
    );
}

#[test]
fn placeflow_does_not_freeze_a_capture_loan_without_source_storage() {
    let package = PackageKey("core-unbound-capture-loan@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let owner = DefKey(Digest::of_bytes(b"core-unbound-capture-loan"));
    let brand = EnvironmentBrand {
        owner,
        callable: CallableId(0),
    };
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![
            CoreExpr {
                kind: CoreKind::Closure {
                    callable: CallableId(0),
                    parameters: vec![],
                    environment: CaptureEnvironment {
                        brand,
                        captures: vec![ClosureCapture {
                            name: "wire_key".into(),
                            mode: CaptureMode::SharedBorrow,
                            ty: Type::Scalar(ScalarType::I64),
                        }],
                        post_states: vec![CapturePostState {
                            name: "wire_key".into(),
                            mode: CaptureMode::SharedBorrow,
                        }],
                        runs_in: RunsInEvidence {
                            environment: brand,
                            callable: CallableId(0),
                            effects: EffectRow::empty(),
                            post_states: vec![CapturePostState {
                                name: "wire_key".into(),
                                mode: CaptureMode::SharedBorrow,
                            }],
                            sealed: true,
                        },
                        sealed: true,
                    },
                    body: CoreId(1),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Literal("0".into()),
                ty: Type::Scalar(ScalarType::I64),
                span,
            },
        ],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };

    let flow = PlaceFlow::analyze(&body);
    assert!(
        flow.diagnostics.iter().any(|diagnostic| diagnostic.code == "G5002"),
        "the forged capture must remain an ownership error: {flow:#?}"
    );
    assert!(
        flow.active_loans.is_empty(),
        "a capture without lexical storage must not become a frozen cleanup loan: {flow:#?}"
    );
}

#[test]
fn typed_core_validation_rejects_inference_in_callable_effect_arguments() {
    let package = PackageKey("core-callable-effect-inference@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Literal("0".into()),
            ty: Type::Callable {
                safety: grandiose_stage0::Safety::Safe,
                lifetime_binders: 0,
                parameters: vec![],
                result: Box::new(Type::Unit),
                effects: EffectRow::closed_instances([EffectInstance {
                    definition: DefKey(Digest::of_bytes(b"hidden-inference-effect")),
                    arguments: vec![GenericArgument::Type(Type::Infer(InferVar(17)))],
                }]),
                invocation: Quantity::ONCE,
            },
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4181"),
        "callable effect arguments must not conceal body-local inference"
    );
}

#[test]
fn forged_nominal_effect_row_inference_cannot_cross_the_core_or_mir_boundary() {
    let package = PackageKey("core-nominal-effect-row-inference@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Literal("0".into()),
            ty: Type::Nominal {
                definition: DefKey(Digest::of_bytes(b"forged-row-generic-nominal")),
                arguments: vec![GenericArgument::EffectRow(EffectRow {
                    effects: BTreeSet::new(),
                    projections: vec![],
                    tail: Some(EffectTail::Infer(grandiose_stage0::EffectVar(3))),
                })],
            },
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };

    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4181"),
        "an unresolved effect-row generic argument must not enter frozen Core"
    );
    let flow = PlaceFlow::analyze(&body);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-row-generic-nominal")),
        &body,
        &flow,
    );
    assert!(lowered.function.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR must independently reject a forged nominal effect-row inference tail"
    );
}

#[test]
fn typed_core_validation_rejects_inference_hidden_in_trait_method_metadata() {
    let package = PackageKey("core-trait-method-inference@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::TraitMethod {
                evidence: DefKey(Digest::of_bytes(b"evidence")),
                method: DefKey(Digest::of_bytes(b"method")),
                trait_arguments: vec![
                    GenericArgument::Type(Type::Infer(InferVar(3))),
                    GenericArgument::EffectRow(EffectRow {
                        effects: BTreeSet::new(),
                        projections: vec![],
                        tail: Some(EffectTail::Infer(grandiose_stage0::EffectVar(4))),
                    }),
                ],
                method_arguments: vec![GenericArgument::ConstInfer {
                    variable: ConstInferVar(5),
                    kind: ConstKind::U32,
                }],
                deferred: None,
            },
            ty: Type::Callable {
                safety: grandiose_stage0::Safety::Safe,
                lifetime_binders: 0,
                parameters: vec![],
                result: Box::new(Type::Unit),
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
            },
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };

    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4181"),
        "inference hidden in trait-method metadata must not reach lowering"
    );
    let flow = PlaceFlow::analyze(&body);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-trait-method")),
        &body,
        &flow,
    );
    assert!(lowered.function.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR lowering must independently reject invalid frozen Core"
    );
}

#[test]
fn typed_core_semantic_fingerprint_ignores_arena_allocation_order_and_spans() {
    let package = PackageKey("core-fingerprint@0.1.0".into());
    let span = |start| Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start,
        end: start + 1,
    };
    let first = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![
            CoreExpr {
                kind: CoreKind::Block(vec![CoreId(1), CoreId(2)]),
                ty: Type::Scalar(grandiose_stage0::ScalarType::I64),
                span: span(20),
            },
            CoreExpr {
                kind: CoreKind::Literal("40".into()),
                ty: Type::Scalar(grandiose_stage0::ScalarType::I64),
                span: span(21),
            },
            CoreExpr {
                kind: CoreKind::Literal("42".into()),
                ty: Type::Scalar(grandiose_stage0::ScalarType::I64),
                span: span(22),
            },
        ],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };
    let second = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![
            CoreExpr {
                kind: CoreKind::Literal("40".into()),
                ty: Type::Scalar(grandiose_stage0::ScalarType::I64),
                span: span(200),
            },
            CoreExpr {
                kind: CoreKind::Literal("42".into()),
                ty: Type::Scalar(grandiose_stage0::ScalarType::I64),
                span: span(201),
            },
            CoreExpr {
                kind: CoreKind::Block(vec![CoreId(0), CoreId(1)]),
                ty: Type::Scalar(grandiose_stage0::ScalarType::I64),
                span: span(202),
            },
        ],
        root: CoreId(2),
        diagnostics: vec![],
        recovered: false,
    };

    assert_eq!(
        first.semantic_fingerprint(),
        second.semantic_fingerprint(),
        "equivalent Core must not inherit transient arena IDs or spans"
    );
}

#[test]
fn typed_core_canonicalizes_type_fingerprints_and_rejects_forged_row_order() {
    let projection = |name: &str| EffectRowProjection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition: DefKey(Digest::of_bytes(b"core-canonical-row-trait")),
        trait_arguments: vec![],
        name: name.into(),
        item_generic_kinds: vec![],
        item_arguments: vec![],
    };
    let callable = |projections| Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects: EffectRow {
            effects: BTreeSet::new(),
            projections,
            tail: None,
        },
        invocation: Quantity::ONCE,
    };
    let package = PackageKey("core-canonical-identity@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let body = |ty| TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Literal("0".into()),
            ty,
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };
    let forged = body(callable(vec![
        projection("Z"),
        projection("A"),
        projection("A"),
    ]));
    let canonical = body(callable(vec![projection("A"), projection("Z")]));

    assert_eq!(
        forged.semantic_fingerprint(),
        canonical.semantic_fingerprint(),
        "representation-only effect-row order must not split Core cache identities"
    );
    assert!(
        forged
            .validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4186"),
        "forged noncanonical type metadata must not enter MIR"
    );
    assert!(canonical.validate().is_empty());

    let forged_gat_kind = body(Type::Projection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition: DefKey(Digest::of_bytes(b"core-forged-gat-kind")),
        trait_arguments: vec![],
        name: "Output".into(),
        item_generic_kinds: vec![grandiose_stage0::GenericKind::Const(
            grandiose_stage0::ConstKind::U32,
        )],
        item_arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
    });
    assert!(
        forged_gat_kind
            .validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4186"),
        "Core must reject an associated-item argument whose kind does not match the frozen declaration contract"
    );

    let forged_trait_head = body(Type::Projection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition: DefKey(Digest::of_bytes(b"core-forged-mixed-trait-head")),
        trait_arguments: vec![GenericArgument::EffectRow(EffectRow {
            effects: BTreeSet::new(),
            projections: vec![projection("Z"), projection("A")],
            tail: None,
        })],
        name: "Output".into(),
        item_generic_kinds: vec![],
        item_arguments: vec![],
    });
    assert!(
        forged_trait_head
            .validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4186"),
        "Core must validate canonical identity nested in enclosing mixed-kind trait arguments"
    );

    let hrtb_gat_with_row = body(Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 1,
        parameters: vec![],
        result: Box::new(Type::Projection {
            subject: Box::new(Type::Scalar(ScalarType::I64)),
            trait_definition: DefKey(Digest::of_bytes(b"core-hrtb-gat-row")),
            trait_arguments: vec![],
            name: "Output".into(),
            item_generic_kinds: vec![
                grandiose_stage0::GenericKind::Lifetime,
                grandiose_stage0::GenericKind::EffectRow,
            ],
            item_arguments: vec![
                GenericArgument::Lifetime(Lifetime::Bound { depth: 0, index: 0 }),
                GenericArgument::EffectRow(EffectRow {
                    effects: BTreeSet::new(),
                    projections: vec![],
                    tail: Some(grandiose_stage0::EffectTail::Generic(7)),
                }),
            ],
        }),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
    });
    assert!(
        hrtb_gat_with_row.validate().is_empty(),
        "Core must retain a scoped HRTB lifetime and open effect-row GAT arguments"
    );

    let malformed_const = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Function {
                definition: DefKey(Digest::of_bytes(b"core-forged-structural-const")),
                arguments: vec![GenericArgument::ConstU32Expr(StructuralU32Expr::Div(
                    Box::new(StructuralU32Expr::Literal(1)),
                    Box::new(StructuralU32Expr::Literal(0)),
                ))],
                host_import: None,
            },
            ty: Type::Unit,
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(
        malformed_const
            .validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4186"),
        "forged invalid structural arithmetic must not enter a frozen Core product"
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
fn typed_core_uses_the_enclosing_callable_where_clause_as_bound_evidence() {
    let package = PackageKey("core-ambient-where-bound@0.1.0".into());
    let source = "trait Mark {} pub fn requires_mark<T>(value: T) -> T where T: Mark { value } pub fn forwards_mark<T>(value: T) -> T where T: Mark { requires_mark(value) }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("forwards_mark"))
        .expect("forwarding definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("forwarding body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_core_does_not_invent_callable_where_bound_evidence() {
    let package = PackageKey("core-missing-ambient-where-bound@0.1.0".into());
    let source = "trait Mark {} pub fn requires_mark<T>(value: T) -> T where T: Mark { value } pub fn forwards_without_mark<T>(value: T) -> T { requires_mark(value) }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("forwards_without_mark"))
        .expect("forwarding definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("forwarding body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4143"),
        "missing unproven-bound diagnostic: {:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_core_normalizes_nested_concrete_associated_type_projections() {
    let package = PackageKey("core-nested-associated-projection@0.1.0".into());
    let source = "trait Source { type Item; } trait Wrapper { type Item; } struct Value {} impl Source for Value { type Item = i64; } impl Wrapper for Value { type Item = <Value as Source>::Item; } pub fn value() -> <Value as Wrapper>::Item { 1 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("value"))
        .expect("value definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("value body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_core_reports_recursive_associated_type_projections() {
    let package = PackageKey("core-recursive-associated-projection@0.1.0".into());
    let source = "trait Loop { type Item; } struct Value {} impl Loop for Value { type Item = <Value as Loop>::Item; } pub fn value() -> <Value as Loop>::Item { 1 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("value"))
        .expect("value definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("value body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4157"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_core_admits_calls_with_the_same_symbolic_effect_row_tail() {
    let package = PackageKey("core-symbolic-effect-tail@0.1.0".into());
    let source = "pub fn forward<e: EffectRow>() -> i64 / { | e } { 0 } pub fn relay<T, e: EffectRow>(value: T) -> i64 / { | e } { forward() }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let relay = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .expect("relay definition");
    let body = BodySyntax::parse(&lexed, source, relay.body.expect("relay body"));
    let core = TypedBody::elaborate(
        relay,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_core_instantiates_unconstrained_effect_row_tails_to_a_closed_caller() {
    let package = PackageKey("core-closed-effect-tail-instantiation@0.1.0".into());
    let source = "pub fn forward<e: EffectRow>() -> i64 / { | e } { 0 } pub fn closed() -> i64 { forward() }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let closed = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("closed"))
        .expect("closed definition");
    let body = BodySyntax::parse(&lexed, source, closed.body.expect("closed body"));
    let core = TypedBody::elaborate(
        closed,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn implicit_calls_infer_effect_row_arguments_carried_by_nominals() {
    let core = core_for(
        "core-implicit-nominal-effect-row-inference@0.1.0",
        "effect Trace { note(); } struct Token<e: EffectRow> {} pub fn identity<e: EffectRow>(value: Token<e>) -> Token<e> { value } pub fn main(value: Token<{Trace}>) -> Token<{Trace}> { identity(value) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            &expression.kind,
            CoreKind::Function { arguments, .. }
                if matches!(arguments.as_slice(), [GenericArgument::EffectRow(row)]
                    if row.tail.is_none() && row.effects.len() == 1)
        )
    }));
}

#[test]
fn typed_core_retains_selected_trait_method_evidence() {
    let package = PackageKey("core-trait-method-evidence@0.1.0".into());
    let source = "trait Increment { fn increment(value: i64) -> i64; } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 1 } } pub fn main() -> i64 { Increment::increment(41) }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let main = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, main.body.unwrap());
    let core = TypedBody::elaborate(
        main,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let implementation = interface
        .definitions
        .iter()
        .find(|definition| definition.kind == grandiose_stage0::DeclarationKind::Implementation)
        .expect("implementation definition");
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            expression.kind,
            CoreKind::TraitMethod { evidence, method, .. }
                if evidence == implementation.key
                    && method == implementation_method_key(implementation.key, "increment")
        )
    }));
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
fn placeflow_rejects_read_while_a_unique_borrow_is_live() {
    let package = PackageKey("core-unique-borrow-read@0.1.0".into());
    let source = "pub fn main() -> i64 { let value = 1; let loan = &mut value; value; loan; 0 }";
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
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5008"),
        "a unique loan must exclude reads: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn forged_callable_lifetime_relation_cannot_retarget_a_second_argument() {
    let mut core = core_for(
        "core-forged-call-reference-relation@0.1.0",
        "pub fn first<'a, 'b>(left: &'a i64, right: &'b i64) -> &'a i64 { left } pub fn main() -> i64 { let left = 1; let right = 2; let forwarded = first(&left, &right); *forwarded }",
    );
    let paths = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Call {
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(paths),
                ..
            } => Some(paths),
            _ => None,
        })
        .expect("generic call did not retain its frozen relation");
    paths[0].argument = 1;
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4187"),
        "forged call retargeted a distinct generic lifetime: {:#?}",
        core.validate()
    );
    let flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-call-lifetime-relation")),
        &core,
        &flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR accepted a forged callable lifetime relation: {lowered:#?}"
    );
}

#[test]
fn higher_ranked_callable_relation_survives_local_region_opening() {
    let core = core_for(
        "core-hrtb-distinct-reference-relation@0.1.0",
        "pub fn main(callback: for<'a> for<'b> (&'a i64, &'b i64) -> &'a i64) -> i64 { let left = 1; let right = 2; let forwarded = callback(&left, &right); left = 3; *forwarded }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let paths = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Call {
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(paths),
                ..
            } => Some(paths),
            _ => None,
        })
        .expect("higher-ranked call did not retain its frozen relation");
    assert_eq!(paths[0].argument, 0);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        !flow
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "higher-ranked relation became opaque after opening: {flow:#?}"
    );
}

#[test]
fn placeflow_tracks_a_live_field_borrow_back_to_its_root_local() {
    let package = PackageKey("core-projection-borrow@0.1.0".into());
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &pair.left; move pair; loan; 0 }";
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
        .expect("main definition");
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
            .any(|diagnostic| diagnostic.code == "G5004"),
        "a projection loan must keep its root from moving: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn placeflow_allows_disjoint_field_access_while_a_projection_loan_is_live() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &mut pair.left; pair.right = 3; loan; pair.right }";
    let flow = flow_for("core-projection-disjoint@0.1.0", source);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
}

#[test]
fn placeflow_rejects_accesses_that_overlap_a_projection_loan() {
    let unique_read = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &mut pair.left; pair.left; loan; 0 }";
    let flow = flow_for("core-projection-unique-read@0.1.0", unique_read);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5008"),
        "a unique field loan must exclude reads of that field: {:#?}",
        flow.diagnostics
    );

    let shared_write = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &pair.left; pair.left = 3; loan; pair.right }";
    let flow = flow_for("core-projection-shared-write@0.1.0", shared_write);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5007"),
        "a shared field loan must exclude writes to that field: {:#?}",
        flow.diagnostics
    );

    let whole_unique = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &pair.left; let whole = &mut pair; loan; 0 }";
    let flow = flow_for("core-projection-whole-conflict@0.1.0", whole_unique);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5006"),
        "a whole unique loan must conflict with a live field loan: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn placeflow_ends_a_named_loan_after_its_last_use() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &pair.left; move pair; 0 }";
    let flow = flow_for("core-nll-last-use@0.1.0", source);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert!(flow.active_loans.is_empty(), "{:#?}", flow.active_loans);
    assert!(flow.events.iter().any(|event| matches!(
        event.kind,
        grandiose_stage0::FlowEventKind::EndBorrow(ref owner) if owner == "loan"
    )));
}

#[test]
fn placeflow_keeps_a_named_unique_loan_live_through_handler_control_flow() {
    let source = "effect Tick { tick() -> i64; } pub fn main() -> i64 { let value = 1; let loan = &mut value; handle Tick::tick() { Tick::tick() => { value; loan; 0 } }; 0 }";
    let flow = flow_for("core-nll-handler-live@0.1.0", source);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5008"),
        "a handler arm must observe an outer loan that remains live through its final reference: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn placeflow_propagates_live_loans_across_dynamic_handler_exits() {
    let source = "effect Tick { tick() -> i64; } pub fn main() -> i64 { let value = 1; let loan = &mut value; handle Tick::tick() { Tick::tick() => 0 }; value; loan; 0 }";
    let flow = flow_for("core-nll-handler-exit@0.1.0", source);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5008"),
        "a loan live after a dynamically selected handler must still exclude the root: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn handler_payload_shadowing_keeps_the_outer_loan_across_the_dynamic_join() {
    let source = "effect Read { read(value: i64) -> i64; } pub fn main(value: i64) -> i64 { let loan = &mut value; handle Read::read(1) { Read::read(value) => { let branch = &mut value; branch; 0 } }; value; loan; 0 }";
    let flow = flow_for("core-handler-payload-place-shadow@0.1.0", source);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5008"),
        "a payload spelling must not overwrite the outer unique loan at the handler join: {flow:#?}"
    );
    assert!(
        flow.final_states.keys().all(|name| !name.contains('#')),
        "handler payload identities escaped their clause scope: {flow:#?}"
    );
}

#[test]
fn placeflow_freezes_distinct_move_path_roots_for_shadowed_bindings() {
    let source = "effect Take { take(value: i64) -> i64; } pub fn main(value: i64) -> i64 { handle Take::take(1) { Take::take(value) => { move value; 0 } }; move value; 0 }";
    let flow = flow_for("core-place-binding-shadowed-move-path@0.1.0", source);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert_eq!(flow.move_paths.len(), 2, "{flow:#?}");
    assert!(
        flow.move_paths
            .iter()
            .all(|path| path.parent.is_none() && path.field.is_none() && path.root == "value"),
        "shadowed roots must retain their presentation spelling: {flow:#?}"
    );
    assert_ne!(
        flow.move_paths[0].binding, flow.move_paths[1].binding,
        "shadowed storage must retain distinct opaque binding identities: {flow:#?}"
    );
    assert_eq!(flow.bindings.len(), 2, "{flow:#?}");
    assert!(
        flow.move_paths.iter().all(|path| {
            flow.bindings
                .get(path.binding.0 as usize)
                .is_some_and(|binding| binding.id == path.binding && binding.spelling == path.root)
        }),
        "move paths must point into the frozen binding table: {flow:#?}"
    );
    assert!(
        flow.bindings
            .iter()
            .all(|binding| binding.spelling == "value"),
        "binding spellings are presentation metadata, not identity: {flow:#?}"
    );
}

#[test]
fn forged_completion_refinement_shadowing_is_rejected_before_placeflow_or_mir() {
    let mut core = core_for(
        "core-forged-completion-refinement-place-shadow@0.1.0",
        "pub enum Result { Ok(i64), Err } pub fn main(value: i64, result: Result) -> i64 { let loan = &mut value; handle result is Result::Ok(found) { true => { let branch = &mut found; branch; 0 }; false => 0 }; value; loan; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let clause = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Completion { clauses, .. } => Some(&mut clauses[0]),
            _ => None,
        })
        .expect("positive completion arm");
    assert!(
        clause.refinement.is_some(),
        "fixture needs a refinement arm"
    );
    clause.bindings[0].0 = "value".into();
    let refinement = clause.refinement.as_mut().expect("refinement arm");
    refinement.environment.bindings[0] = "value".into();
    refinement.environment.binding_types[0].0 = "value".into();
    for expression in &mut core.expressions {
        if matches!(&expression.kind, CoreKind::Local(name) if name == "found") {
            expression.kind = CoreKind::Local("value".into());
        }
    }
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4183"),
        "forged completion refinement escaped Typed Core provenance validation: {:#?}",
        core.validate()
    );
    let valid_flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-completion-refinement-shadowing")),
        &core,
        &valid_flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR accepted completion refinement with forged provenance: {lowered:#?}"
    );
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5008"),
        "defensive PlaceFlow analysis must still retain the outer loan: {flow:#?}"
    );
    assert!(
        flow.active_loans
            .iter()
            .all(|loan| loan.owner.as_deref() != Some("branch")),
        "a completion-arm reborrow escaped through the join: {flow:#?}"
    );
}

#[test]
fn typed_core_validation_rejects_completion_refinement_on_a_negative_boolean_arm() {
    let mut core = core_for(
        "core-forged-negative-refinement@0.1.0",
        "pub enum Result { Ok(i64), Err } pub fn main(value: Result) -> i64 { handle value is Result::Ok(found) { true => found; false => 0 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let positive = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Completion { clauses, .. } => clauses[0].refinement.clone(),
            _ => None,
        })
        .expect("positive arm must carry refinement evidence");
    let negative = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Completion { clauses, .. } => Some(&mut clauses[1]),
            _ => None,
        })
        .expect("negative completion arm");
    negative.refinement = Some(positive);

    assert!(
        core.validate().iter().any(|diagnostic| {
            diagnostic.code == "G4183"
                && diagnostic
                    .message
                    .contains("does not prove the test result true")
        }),
        "false branch forged a positive refinement pack: {:#?}",
        core.validate()
    );
    let flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-negative-completion-refinement")),
        &core,
        &flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR lowered a false arm with forged refinement evidence: {lowered:#?}"
    );
}

#[test]
fn typed_core_validation_rederives_refinement_binding_types_from_pattern_layout() {
    let mut core = core_for(
        "core-forged-refinement-binding-type@0.1.0",
        "pub struct Pair { value: i64 } pub fn main(value: Pair) -> i64 { handle value is Pair { value: found } { true => found; false => 0 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let pattern_test = core
        .expressions
        .iter()
        .position(|expression| matches!(expression.kind, CoreKind::PatternTest { .. }))
        .expect("pattern test");
    let mut forged_environment = match &core.expressions[pattern_test].kind {
        CoreKind::PatternTest { refinement, .. } => refinement.clone(),
        _ => unreachable!(),
    };
    forged_environment.binding_types[0].1 = Type::Scalar(ScalarType::Bool);
    if let CoreKind::PatternTest { refinement, .. } = &mut core.expressions[pattern_test].kind {
        *refinement = forged_environment.clone();
    }
    let branch = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Completion { clauses, .. } => clauses[0].refinement.as_mut(),
            _ => None,
        })
        .expect("positive completion refinement");
    branch.environment = forged_environment;

    assert!(
        core.validate().iter().any(|diagnostic| {
            diagnostic.code == "G4183"
                && diagnostic
                    .message
                    .contains("binding types do not match the originating structural pattern")
        }),
        "forged refinement binder type escaped the frozen structural layout: {:#?}",
        core.validate()
    );
}

#[test]
fn forged_explicit_resumption_shadowing_cannot_erase_an_outer_loan() {
    let mut core = core_for(
        "core-forged-resumption-place-shadow@0.1.0",
        "effect Ask { [1, 1] ask() -> i64; } pub fn main(value: i64) -> i64 { let loan = &mut value; handle Ask::ask() { Ask::ask() with k => k(0) }; value; loan; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let clause = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Handle { clauses, .. } => Some(&mut clauses[0]),
            _ => None,
        })
        .expect("handler arm");
    let CoreHandlerResumption::Explicit { name, .. } = &mut clause.resumption else {
        panic!("fixture needs an explicit resumption");
    };
    *name = "value".into();
    assert!(core.validate().is_empty(), "{:#?}", core.validate());
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5008"),
        "forged resumption spelling erased an outer unique loan: {flow:#?}"
    );
    assert!(
        flow.final_states.keys().all(|name| !name.contains('#')),
        "resumption identity escaped its handler arm: {flow:#?}"
    );
}

#[test]
fn placeflow_releases_a_named_loan_after_a_nested_block_last_use() {
    let source =
        "pub fn main() -> i64 { let value = 1; let loan = &mut value; { loan; 0 }; value }";
    let flow = flow_for("core-nll-nested-last-use@0.1.0", source);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
}

#[test]
fn placeflow_ignores_a_forged_conflicting_suffix_after_a_direct_transfer() {
    let package = PackageKey("core-forged-transfer-unreachable@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let i64 = Type::Scalar(ScalarType::I64);
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![("value".into(), i64.clone())],
        expressions: vec![
            CoreExpr {
                kind: CoreKind::Local("value".into()),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Borrow {
                    unique: true,
                    value: CoreId(0),
                },
                ty: Type::Reference {
                    mutability: grandiose_stage0::Mutability::Unique,
                    lifetime: Lifetime::Elided,
                    referent: Box::new(i64.clone()),
                },
                span,
            },
            CoreExpr {
                kind: CoreKind::Let {
                    name: "loan".into(),
                    value: CoreId(1),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Literal("0".into()),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Transfer {
                    brand: grandiose_stage0::LabelBrand {
                        owner: DefKey(Digest::of_bytes(b"forged-transfer-owner")),
                        label: 0,
                    },
                    value: CoreId(3),
                },
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Literal("2".into()),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Assign {
                    place: CorePlace::Local {
                        name: "value".into(),
                        ty: i64.clone(),
                    },
                    value: CoreId(5),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Local("loan".into()),
                ty: Type::Reference {
                    mutability: grandiose_stage0::Mutability::Unique,
                    lifetime: Lifetime::Elided,
                    referent: Box::new(i64.clone()),
                },
                span,
            },
            CoreExpr {
                kind: CoreKind::Block(vec![CoreId(2), CoreId(4), CoreId(6), CoreId(7)]),
                ty: i64,
                span,
            },
        ],
        root: CoreId(8),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(body.validate().is_empty(), "{:#?}", body.validate());
    let flow = PlaceFlow::analyze(&body);
    assert!(
        flow.diagnostics.is_empty(),
        "a post-transfer forged suffix must not participate in PlaceFlow: {flow:#?}"
    );
}

#[test]
fn terminal_strict_operand_does_not_publish_unreachable_move_or_cleanup_facts() {
    let core = core_for(
        "core-terminal-strict-ownership-suffix@0.1.0",
        "effect Stop { stop() -> !; } pub fn main() -> i64 { let value = 7; handle (Stop::stop(), { let loan = &mut value; move value }) { Stop::stop() => 42 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert!(
        !flow.events.iter().any(|event| {
            matches!(&event.kind, FlowEventKind::Move(name) if name == "value")
                || matches!(&event.kind, FlowEventKind::BorrowUnique(name) if name == "value")
        }),
        "unreachable strict suffix contributed ownership events: {:#?}",
        flow.events
    );
    assert!(
        flow.moved_places.iter().all(|place| place.root != "value")
            && flow.active_loans.iter().all(|loan| loan.root != "value"),
        "unreachable strict suffix leaked into terminal cleanup evidence: {flow:#?}"
    );

    let mir = MirLowering::lower(
        DefKey(Digest::of_bytes(b"terminal-strict-ownership-suffix")),
        &core,
        &flow,
    )
    .function
    .expect("terminal handler must lower after unreachable ownership suffix is discarded");
    let image = grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
        .expect("MIR cleanup proof must survive independent VM verification");
    assert_eq!(image.run_i64().unwrap(), 42);
}

#[test]
fn label_consumed_transfer_preserves_following_strict_ownership_effects() {
    let core = core_for(
        "core-label-rejoining-strict-ownership@0.1.0",
        "pub fn main() -> i64 { let value = 0; let result = label done { transfer done 40; 0 }; let loan = &mut value; *loan = 2; result + value }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert!(
        flow.events.iter().any(
            |event| matches!(&event.kind, FlowEventKind::BorrowUnique(name) if name == "value")
        ) && flow
            .events
            .iter()
            .any(|event| matches!(&event.kind, FlowEventKind::Read(name) if name == "value")),
        "a label-rejoining transfer incorrectly suppressed following ownership effects: {:#?}",
        flow.events
    );
    let mir = MirLowering::lower(
        DefKey(Digest::of_bytes(b"label-rejoining-strict-ownership")),
        &core,
        &flow,
    )
    .function
    .expect("label rejoining path must lower");
    let image = grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
        .expect("label rejoining cleanup path must verify");
    assert_eq!(image.run_i64().unwrap(), 42);
}

#[test]
fn placeflow_releases_a_dead_let_bound_closure_capture() {
    let source = "pub fn main() -> i64 { let value = 1; let loan = &value; let saved = () -> &i64 { loan }; value = 2; 0 }";
    let flow = flow_for("core-nll-captured-reference@0.1.0", source);
    assert!(
        flow.events
            .iter()
            .any(|event| matches!(&event.kind, FlowEventKind::Reborrow(root) if root == "value")),
        "capturing a named reference must retain a reborrow of its backing place: {:#?}",
        flow.events
    );
    assert!(
        flow.events.iter().any(
            |event| matches!(&event.kind, FlowEventKind::EndBorrow(owner) if owner == "saved")
        ),
        "a dead closure environment must release its owned capture loan: {:#?}",
        flow.events
    );
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
}

#[test]
fn placeflow_releases_a_dead_handler_arm_closure_capture_after_the_join() {
    let source = "effect Tick { tick() -> i64; } pub fn main() -> i64 { let value = 1; let loan = &value; handle Tick::tick() { Tick::tick() => { let saved = () -> &i64 { loan }; 0 } }; value = 2; 0 }";
    let flow = flow_for("core-nll-captured-reference-handler@0.1.0", source);
    assert!(
        flow.events
            .iter()
            .any(|event| matches!(&event.kind, FlowEventKind::Reborrow(root) if root == "value")),
        "handler-arm closure capture did not create a backing reborrow: {:#?}",
        flow.events
    );
    assert!(
        flow.events.iter().any(
            |event| matches!(&event.kind, FlowEventKind::EndBorrow(owner) if owner == "saved")
        ),
        "a handler-local closure must release its capture before the join: {:#?}",
        flow.events
    );
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
}

#[test]
fn placeflow_tracks_partial_moves_without_consuming_disjoint_fields() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; pair.right }";
    let flow = flow_for("core-projection-partial-move@0.1.0", source);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert_eq!(flow.moved_places.len(), 1, "{:#?}", flow.moved_places);
    assert_eq!(flow.moved_places[0].root, "pair");
    assert_eq!(flow.moved_places[0].fields, vec![0]);
    assert_eq!(flow.move_paths.len(), 2, "{:#?}", flow.move_paths);
    assert_eq!(flow.move_paths[0].parent, None);
    assert_eq!(flow.move_paths[0].root, "pair");
    assert_eq!(flow.move_paths[0].field, None);
    assert_eq!(
        flow.move_paths[1].parent,
        Some(grandiose_stage0::MovePathId(0))
    );
    assert_eq!(flow.move_paths[1].root, "pair");
    assert_eq!(flow.move_paths[1].field, Some(0));
    assert!(
        flow.events.iter().any(|event| matches!(
            (&event.kind, &event.place),
            (FlowEventKind::Move(root), Some(place)) if root == "pair" && place.root == "pair" && place.fields == vec![0]
        )),
        "PlaceFlow must publish the canonical moved projection for downstream obligation analysis: {:#?}",
        flow.events
    );
}

#[test]
fn placeflow_rejects_whole_or_overlapping_use_after_partial_move() {
    let whole = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; move pair; 0 }";
    let flow = flow_for("core-partial-move-whole@0.1.0", whole);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5003"),
        "moving an aggregate with an uninitialized field must fail: {:#?}",
        flow.diagnostics
    );

    let overlap = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; pair.left }";
    let flow = flow_for("core-partial-move-overlap@0.1.0", overlap);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "reading the moved field must fail: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn placeflow_reinitializes_partial_moves_at_field_and_aggregate_boundaries() {
    let field = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; pair.left = 3; pair.left }";
    let flow = flow_for("core-partial-move-field-reinit@0.1.0", field);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert!(flow.moved_places.is_empty(), "{:#?}", flow.moved_places);

    let aggregate = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; pair = Pair { left: 3, right: 4 }; pair.left }";
    let flow = flow_for("core-partial-move-aggregate-reinit@0.1.0", aggregate);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert!(flow.moved_places.is_empty(), "{:#?}", flow.moved_places);
}

#[test]
fn placeflow_tracks_nested_partial_moves_and_respects_projection_loans() {
    let nested = "pub struct Pair { left: i64, right: i64 } pub struct Outer { pair: Pair, spare: i64 } pub fn main() -> i64 { let outer = Outer { pair: Pair { left: 1, right: 2 }, spare: 3 }; move outer.pair.left; outer.pair.right + outer.spare }";
    let flow = flow_for("core-nested-partial-move@0.1.0", nested);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert!(
        flow.moved_places
            .iter()
            .any(|place| place.root == "outer" && place.fields == vec![0, 0]),
        "nested move path was not retained for aggregate cleanup: {:#?}",
        flow.moved_places
    );
    assert_eq!(flow.move_paths.len(), 3, "{:#?}", flow.move_paths);
    assert_eq!(flow.move_paths[0].parent, None);
    assert_eq!(flow.move_paths[0].root, "outer");
    assert_eq!(flow.move_paths[0].field, None);
    assert_eq!(
        flow.move_paths[1].parent,
        Some(grandiose_stage0::MovePathId(0))
    );
    assert_eq!(flow.move_paths[1].field, Some(0));
    assert_eq!(
        flow.move_paths[2].parent,
        Some(grandiose_stage0::MovePathId(1))
    );
    assert_eq!(flow.move_paths[2].field, Some(0));
    assert!(
        flow.move_paths
            .iter()
            .all(|path| path.binding == flow.move_paths[0].binding),
        "every prefix of one owned place must retain its opaque binding root: {flow:#?}"
    );
    assert_eq!(flow.bindings.len(), 1, "{flow:#?}");
    assert_eq!(flow.bindings[0].id, flow.move_paths[0].binding);
    assert_eq!(flow.bindings[0].spelling, "outer");

    let disjoint_loan = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &pair.right; move pair.left; loan; 0 }";
    let flow = flow_for("core-partial-move-disjoint-loan@0.1.0", disjoint_loan);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);

    let overlapping_loan = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &pair.left; move pair.left; loan; 0 }";
    let flow = flow_for("core-partial-move-overlap-loan@0.1.0", overlapping_loan);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "moving a live borrowed field must be rejected: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn placeflow_rejects_writes_through_a_moved_parent_projection() {
    let source = "pub struct Pair { left: i64, right: i64 } pub struct Outer { pair: Pair } pub fn main() -> i64 { let outer = Outer { pair: Pair { left: 1, right: 2 } }; move outer.pair; outer.pair.left = 3; 0 }";
    let flow = flow_for("core-partial-move-parent-write@0.1.0", source);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5009"),
        "writing through a moved parent must require aggregate reinitialization: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn placeflow_joins_partial_moves_from_dynamic_handler_exits() {
    let source = "effect Tick { tick(value: Bool) -> i64; } pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; handle Tick::tick(true) { Tick::tick(true) => move pair.left, Tick::tick(false) => 0 }; pair.left }";
    let flow = flow_for("core-partial-move-handler-join@0.1.0", source);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "a dynamically moved field must remain unavailable after the join: {:#?}",
        flow.diagnostics
    );
    assert!(
        flow.moved_places
            .iter()
            .any(|place| place.root == "pair" && place.fields == vec![0]),
        "the frozen aggregate drop state lost the conditional field move: {:#?}",
        flow.moved_places
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
fn enum_reference_results_preserve_variant_invariant_caller_paths() {
    let core = core_for(
        "core-result-reference-origin@0.1.0",
        "pub enum Result<T, E> { Ok(T), Err(E) } pub fn as_ref<'a, A, E>(value: &'a Result<A, E>) -> Result<&'a A, &'a E> { () } pub fn main<'a>(value: &'a Result<i64, i64>) -> Result<&'a i64, &'a i64> { as_ref(value) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let Some(CoreKind::Call {
        reference_contract,
        reference_origin,
        ..
    }) = core
        .expressions
        .iter()
        .find(|expression| matches!(expression.kind, CoreKind::Call { .. }))
        .map(|expression| &expression.kind)
    else {
        panic!("reference helper call must retain its direct-call provenance");
    };
    for origin in [reference_contract, reference_origin] {
        let grandiose_stage0::CallReferenceOrigin::Paths(paths) = origin else {
            panic!("reference result must not become opaque: {origin:#?}");
        };
        assert_eq!(paths.len(), 1, "{paths:#?}");
        assert_eq!(paths[0].result_fields, vec![0]);
        assert_eq!(paths[0].argument, 0);
        assert!(paths[0].argument_fields.is_empty());
    }
}

#[test]
fn contextual_u32_comparisons_lower_to_typed_vm_primitives() {
    let package = PackageKey("core-u32-comparison-mir@0.1.0".into());
    let source = "infixl 20 <=; pub fn main(value: u32) -> bool { value <= 1114111 }";
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
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(definition.key, &core, &flow);
    assert!(lowered.diagnostics.is_empty(), "{:#?}", lowered.diagnostics);
    let mir = lowered
        .function
        .expect("u32 comparison should lower to MIR");
    assert!(
        mir.entry_block()
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::ConstU32 { .. }))
    );
    assert!(
        mir.entry_block()
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::U32Le { .. }))
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
        environment,
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
    assert_eq!(environment.captures.len(), 1);
    assert_eq!(environment.captures[0].name, "value");
    assert_eq!(environment.captures[0].mode, CaptureMode::Copy);
}

#[test]
fn typed_closures_preserve_enclosing_lifetime_binders() {
    let package = PackageKey("core-closure-lifetime@0.1.0".into());
    let source = "pub fn main<'a>(value: &'a i64) -> i64 { let identity = (item: &'a i64) -> &'a i64 { item }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = &interface.definitions[0];
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
        .find(|expression| matches!(expression.kind, CoreKind::Closure { .. }))
        .expect("typed closure");
    let Type::Callable {
        parameters, result, ..
    } = &closure.ty
    else {
        panic!("typed closure did not receive a callable type")
    };
    assert!(matches!(
        parameters.as_slice(),
        [Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }]
    ));
    assert!(matches!(
        result.as_ref(),
        Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }
    ));
}

#[test]
fn typed_closures_normalize_structural_const_arithmetic_in_type_contracts() {
    let package = PackageKey("core-closure-const-arithmetic@0.1.0".into());
    let source = "pub struct Tag<n: u32> {} pub fn main() -> i64 { let identity = (value: Tag<1 + 2>) -> Tag<6 / 2> { value }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{body:#?}");
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
        .find(|expression| matches!(expression.kind, CoreKind::Closure { .. }))
        .expect("typed closure");
    let Type::Callable {
        parameters, result, ..
    } = &closure.ty
    else {
        panic!("typed closure did not receive a callable type")
    };
    assert!(matches!(
        parameters.as_slice(),
        [Type::Nominal { arguments, .. }] if arguments == &vec![GenericArgument::ConstU32(3)]
    ));
    assert!(matches!(
        result.as_ref(),
        Type::Nominal { arguments, .. } if arguments == &vec![GenericArgument::ConstU32(3)]
    ));
}

#[test]
fn typed_closures_normalize_associated_constants_in_nominal_generic_slots() {
    let core = core_for(
        "core-associated-const@0.1.0",
        "trait Width { const Value: u32 = 3; } struct Chosen<n: u32> {} impl Width for i64 { const Value = 7; } pub fn main() -> i64 { let identity = (value: Chosen<<i64 as Width>::Value>) -> Chosen<<i64 as Width>::Value> { value }; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let closure = core
        .expressions
        .iter()
        .find(|expression| matches!(expression.kind, CoreKind::Closure { .. }))
        .expect("typed closure");
    let Type::Callable {
        parameters, result, ..
    } = &closure.ty
    else {
        panic!("typed closure did not receive a callable type")
    };
    assert!(matches!(
        parameters.as_slice(),
        [Type::Nominal { arguments, .. }] if arguments == &vec![GenericArgument::ConstU32(7)]
    ));
    assert!(matches!(
        result.as_ref(),
        Type::Nominal { arguments, .. } if arguments == &vec![GenericArgument::ConstU32(7)]
    ));
}

#[test]
fn typed_closures_retain_mixed_nominal_annotation_identity_through_aliases() {
    let core = core_for(
        "core-closure-mixed-nominal-alias@0.1.0",
        "effect Trace { note(); } pub struct Mixed<'a, e: EffectRow, n: u32, q: Quantity, T> {} type Alias = Mixed<'static, {Trace}, 7, [1, 2], i64>; pub fn main() -> i64 { let identity = (value: Alias) -> Mixed<'static, {Trace}, 7, [1, 2], i64> { value }; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let closure = core
        .expressions
        .iter()
        .find(|expression| matches!(expression.kind, CoreKind::Closure { .. }))
        .expect("typed closure");
    let Type::Callable {
        parameters, result, ..
    } = &closure.ty
    else {
        panic!("typed closure did not receive a callable type")
    };
    let matches_mixed = |value: &Type| {
        matches!(
            value,
            Type::Nominal { arguments, .. }
                if matches!(
                    arguments.as_slice(),
                    [
                        GenericArgument::Lifetime(Lifetime::Static),
                        GenericArgument::EffectRow(row),
                        GenericArgument::ConstU32(7),
                        GenericArgument::ConstQuantity(quantity),
                        GenericArgument::Type(Type::Scalar(ScalarType::I64)),
                    ] if row.effects.len() == 1 && *quantity == Quantity::new(1, Some(2)).unwrap()
                )
        )
    };
    assert!(matches_mixed(&parameters[0]));
    assert!(matches_mixed(result));
}

#[test]
fn typed_closures_substitute_mixed_generic_alias_annotation_identity() {
    let core = core_for(
        "core-closure-mixed-nominal-generic-alias@0.1.0",
        "pub struct Mixed<'a, e: EffectRow, n: u32, q: Quantity, T> {} type Alias<'a, e: EffectRow, n: u32, q: Quantity, T> = Mixed<'a, e, n, q, T>; pub fn main<'a, e: EffectRow, n: u32, q: Quantity, T>() -> i64 { let identity = (value: Alias<'a, e, n, q, T>) -> Mixed<'a, e, n, q, T> { value }; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let closure = core
        .expressions
        .iter()
        .find(|expression| matches!(expression.kind, CoreKind::Closure { .. }))
        .expect("typed closure");
    let Type::Callable {
        parameters, result, ..
    } = &closure.ty
    else {
        panic!("typed closure did not receive a callable type")
    };
    let matches_generic = |value: &Type| {
        matches!(
            value,
            Type::Nominal { arguments, .. }
                if matches!(arguments.as_slice(), [
                    GenericArgument::Lifetime(Lifetime::Generic(0)),
                    GenericArgument::EffectRow(row),
                    GenericArgument::ConstGeneric { index: 2, kind: grandiose_stage0::ConstKind::U32 },
                    GenericArgument::ConstGeneric { index: 3, kind: grandiose_stage0::ConstKind::Quantity },
                    GenericArgument::Type(Type::Generic(4)),
                ] if row.tail == Some(grandiose_stage0::EffectTail::Generic(1)))
        )
    };
    assert!(matches_generic(&parameters[0]));
    assert!(matches_generic(result));
}

#[test]
fn typed_closure_nominal_annotations_diagnose_wrong_kind_and_arity() {
    let core = core_for(
        "core-closure-nominal-annotation-errors@0.1.0",
        "pub struct Tag<n: u32> {} pub fn main() -> i64 { let wrong_kind = (value: Tag<i64>) -> i64 { 0 }; let wrong_arity = (value: Tag) -> i64 { 0 }; 0 }",
    );
    assert!(
        core.diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G4158")
            .count()
            >= 2,
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_closures_reject_unbound_lifetime_annotations() {
    let package = PackageKey("core-closure-unbound-lifetime@0.1.0".into());
    let source = "pub fn main() -> i64 { let identity = (item: &'a i64) -> i64 { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
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
            .any(|diagnostic| diagnostic.code == "G4170"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_closures_reject_lifetime_binders_in_type_position() {
    let package = PackageKey("core-closure-lifetime-type@0.1.0".into());
    let source = "pub fn main<'a>() -> i64 { let invalid = (item: 'a) -> i64 { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
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
            .any(|diagnostic| diagnostic.code == "G4172"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_closures_reject_const_binders_in_type_position() {
    let package = PackageKey("core-closure-const-type@0.1.0".into());
    let source = "pub fn main<n: u32>() -> i64 { let invalid = (item: n) -> i64 { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
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
            .any(|diagnostic| diagnostic.code == "G4173"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn concrete_associated_type_projections_normalize_in_typed_closure_contracts() {
    let package = PackageKey("core-associated-projection@0.1.0".into());
    let source = "trait Iterator { type Item; } struct Range<T> {} impl<T> Iterator for Range<T> { type Item = T; } pub fn main() -> i64 { let identity = (value: <Range<Text> as Iterator>::Item) -> Text { value }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    assert!(body.diagnostics.is_empty(), "{body:#?}");
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::Text)
    )));
}

#[test]
fn trait_associated_type_defaults_normalize_in_source_contracts() {
    let core = core_for(
        "core-associated-default-source",
        "trait Source { type Item = Text; } struct Value {} impl Source for Value {} pub fn main() -> i64 { let identity = (value: <Value as Source>::Item) -> Text { value }; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == Type::Scalar(ScalarType::Text)
    )));
}

#[test]
fn generic_trait_associated_type_defaults_normalize_in_source_contracts() {
    let core = core_for(
        "core-associated-generic-default-source",
        "trait Convert { type Output<U> = U; } struct Value {} impl Convert for Value {} pub fn main() -> i64 { let identity = (value: <Value as Convert>::Output<Text>) -> Text { value }; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == Type::Scalar(ScalarType::Text)
    )));
}

#[test]
fn explicit_associated_type_source_definition_overrides_a_default() {
    let core = core_for(
        "core-associated-default-override-source",
        "trait Source { type Item = Text; } struct Value {} impl Source for Value { type Item = i64; } pub fn main() -> i64 { let identity = (value: <Value as Source>::Item) -> i64 { value }; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == Type::Scalar(ScalarType::I64)
    )));
}

#[test]
fn concrete_gat_projections_normalize_in_typed_closure_contracts() {
    let package = PackageKey("core-gat-projection@0.1.0".into());
    let source = "trait Apply { type Output<T>; } struct Wrapper {} impl Apply for Wrapper { type Output<T> = T; } pub fn main() -> i64 { let identity = (value: <Wrapper as Apply>::Output<Text>) -> Text { value }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    assert!(body.diagnostics.is_empty(), "{body:#?}");
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::Text)
    )));
}

#[test]
fn mixed_kind_trait_heads_normalize_in_typed_closure_contracts() {
    let package = PackageKey("core-mixed-trait-projection@0.1.0".into());
    let source = "effect Trace { note(); } trait Select<'a, e: EffectRow, n: u32> { type Output; } struct Value {} impl Select<'static, {Trace}, 7> for Value { type Output = Text; } pub fn main() -> i64 { let identity = (value: <Value as Select<'static, {Trace}, 7>>::Output) -> Text { value }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    assert!(body.diagnostics.is_empty(), "{body:#?}");
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == Type::Scalar(ScalarType::Text)
    )));
}

#[test]
fn structural_const_associated_projections_normalize_in_typed_closure_contracts() {
    let package = PackageKey("core-const-gat-projection@0.1.0".into());
    let source = "trait Apply { type Output<n: u32>; } struct Wrapper {} impl Apply for Wrapper { type Output<n: u32> = Text; } pub fn main() -> i64 { let identity = (value: <Wrapper as Apply>::Output<7>) -> Text { value }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    assert!(body.diagnostics.is_empty(), "{body:#?}");
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::Text)
    )));
}

#[test]
fn associated_effect_rows_are_rejected_by_the_type_projection_surface() {
    let package = PackageKey("core-associated-effect-row@0.1.0".into());
    let source = "trait HasEffects { type Effects: EffectRow; } struct Value {} impl HasEffects for Value { type Effects = {}; } pub fn main() -> i64 { let value = (input: <Value as HasEffects>::Effects) -> i64 { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
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
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4149"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn concrete_associated_effect_rows_normalize_in_typed_closure_contracts() {
    let package = PackageKey("core-closure-associated-effect-row@0.1.0".into());
    let source = "effect Trace { note(); } trait Capability { type Effects: EffectRow; } struct Value {} impl Capability for Value { type Effects = {Trace}; } pub fn main() -> i64 { let worker = () -> i64 / { <Value as Capability>::Effects } { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let main = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let trace = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Trace"))
        .expect("Trace definition")
        .key;
    let body = BodySyntax::parse(&lexed, source, main.body.expect("main body"));
    let core = TypedBody::elaborate(
        main,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        &expression.ty,
        grandiose_stage0::Type::Callable { effects, .. }
            if effects.effects.iter().any(|effect| effect.definition == trace)
    )));
}

#[test]
fn typed_closure_contracts_preserve_generic_effect_instances() {
    let package = PackageKey("core-closure-generic-effect@0.1.0".into());
    let source = "effect Trace<T> { note(value: T); } pub fn main() -> i64 { let worker = () -> i64 / { Trace<Text> } { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let main = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let trace = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Trace"))
        .expect("Trace definition")
        .key;
    let body = BodySyntax::parse(&lexed, source, main.body.expect("main body"));
    let core = TypedBody::elaborate(
        main,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        &expression.ty,
        grandiose_stage0::Type::Callable { effects, .. }
            if effects.effects.iter().any(|effect| effect.definition == trace
                && effect.arguments == [grandiose_stage0::GenericArgument::Type(grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::Text))])
    )));
}

#[test]
fn typed_closure_contracts_preserve_enclosing_open_effect_row_tails() {
    let package = PackageKey("core-closure-open-effect-row@0.1.0".into());
    let source = "pub fn relay<e: EffectRow>() -> i64 / { | e } { let worker = () -> i64 / { | e } { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let relay = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .expect("relay definition");
    let body = BodySyntax::parse(&lexed, source, relay.body.expect("relay body"));
    let core = TypedBody::elaborate(
        relay,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        &expression.ty,
        grandiose_stage0::Type::Callable { effects, .. }
            if effects.tail == Some(grandiose_stage0::EffectTail::Generic(0))
    )));
}

#[test]
fn typed_closure_rejects_ordinary_generic_as_effect_row_tail() {
    let package = PackageKey("core-closure-invalid-effect-row@0.1.0".into());
    let source = "pub fn relay<T>() -> i64 { let worker = () -> i64 / { | T } { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let relay = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .expect("relay definition");
    let body = BodySyntax::parse(&lexed, source, relay.body.expect("relay body"));
    let core = TypedBody::elaborate(
        relay,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4115"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_closure_body_checks_against_its_own_effect_contract() {
    let package = PackageKey("core-closure-effect-boundary@0.1.0".into());
    let source = "effect Trace { note(); } pub fn outer() -> i64 { let worker = () -> i64 / {Trace} { Trace::note(); 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let outer = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("outer"))
        .expect("outer definition");
    let body = BodySyntax::parse(&lexed, source, outer.body.expect("outer body"));
    let core = TypedBody::elaborate(
        outer,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_closure_body_rejects_effects_missing_from_its_own_contract() {
    let package = PackageKey("core-closure-closed-effect-boundary@0.1.0".into());
    let source = "effect Trace { note(); } pub fn outer() -> i64 / {Trace} { let worker = () -> i64 { Trace::note(); 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let outer = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("outer"))
        .expect("outer definition");
    let body = BodySyntax::parse(&lexed, source, outer.body.expect("outer body"));
    let core = TypedBody::elaborate(
        outer,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn concrete_associated_effect_rows_normalize_at_call_boundaries() {
    let package = PackageKey("core-associated-effect-row-normalization@0.1.0".into());
    let source = "effect Trace { note(); } trait Capability { type Effects: EffectRow; } struct Value {} impl Capability for Value { type Effects = {Trace}; } pub fn worker() -> i64 / { <Value as Capability>::Effects } { 1 } pub fn main() -> i64 / { Trace } { worker() }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
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
}

#[test]
fn typed_core_forwards_symbolic_associated_effect_rows_with_the_same_evidence() {
    let package = PackageKey("core-symbolic-associated-effect-row-forwarding@0.1.0".into());
    let source = "trait Capability { type Effects: EffectRow; } pub fn worker<T>(value: T) -> i64 / { <T as Capability>::Effects } where T: Capability { 1 } pub fn relay<T>(value: T) -> i64 / { <T as Capability>::Effects } where T: Capability { worker(value) }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_core_rejects_symbolic_associated_effect_rows_without_subset_evidence() {
    let package = PackageKey("core-symbolic-associated-effect-row-mismatch@0.1.0".into());
    let source = "trait First { type Effects: EffectRow; } trait Second { type Effects: EffectRow; } pub fn worker<T>(value: T) -> i64 / { <T as First>::Effects } where T: First { 1 } pub fn relay<T>(value: T) -> i64 / { <T as Second>::Effects } where T: First, T: Second { worker(value) }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .unwrap();
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
            .any(|diagnostic| diagnostic.code == "G4155"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn generic_associated_effect_rows_normalize_item_arguments() {
    let package = PackageKey("core-gat-effect-row-normalization@0.1.0".into());
    let source = "effect Trace<T> { note(value: T); } trait Capability { type Effects<T>: EffectRow; } struct Value {} impl Capability for Value { type Effects<T> = {Trace<T>}; } pub fn worker() -> i64 / { <Value as Capability>::Effects<Text> } { 1 } pub fn main() -> i64 / { Trace<Text> } { worker() }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
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
}

#[test]
fn placeflow_copies_a_duplicable_closure_capture_when_the_closure_is_created() {
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
    let flow = PlaceFlow::analyze_with_interface(&core, &signatures);
    assert!(
        flow.diagnostics.is_empty(),
        "{flow:#?}"
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
    assert_eq!(
        clauses[0].payload_types,
        vec![grandiose_stage0::Type::Scalar(
            grandiose_stage0::ScalarType::I64
        )]
    );
    assert_eq!(clauses[0].bindings[0].0, "value");
    assert!(matches!(
        clauses[0].resumption,
        CoreHandlerResumption::Explicit { ref name, .. } if name == "resume"
    ));
}

#[test]
fn typed_core_interprets_with_wildcard_as_resumption_discard() {
    let package = PackageKey("core-handler-with-wildcard@0.1.0".into());
    let source = "effect Log { [0, 1] write(value: i64) -> i64; } pub fn main() -> i64 { handle Log::write(1) { Log::write(value) with _ => 0 } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
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
        .expect("handler clause");
    assert!(matches!(
        clause.resumption,
        CoreHandlerResumption::Discard { .. }
    ));
}

#[test]
fn typed_core_rejects_a_continuation_that_shadows_a_payload_binder() {
    let package = PackageKey("core-handler-duplicate-continuation@0.1.0".into());
    let source = "effect Log { [1, 1] write(value: i64) -> i64; } pub fn main() -> i64 { handle Log::write(1) { Log::write(value) with value => value(0) } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(
        body.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4017"),
        "parser accepted duplicate handler binder: {:#?}",
        body.diagnostics
    );
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4160"),
        "typed Core accepted duplicate handler binder: {:#?}",
        core.diagnostics
    );
}

#[test]
fn handler_coverage_tracks_direct_operations_but_calls_require_total_protocol_coverage() {
    let package = PackageKey("core-handler-coverage@0.1.0".into());
    let source = "effect Console { read() -> i64; write(value: i64) -> i64; } effect Stop { abort() -> !; } pub fn worker() -> i64 / Console { Console::write(0) } pub fn partial() -> i64 { handle Console::read() { Console::read() => 1 } } pub fn partial_call() -> i64 { handle worker() { Console::read() => 1 } } pub fn terminal() -> i64 { handle Stop::abort() { Stop::abort() with resume => 42 } }";
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
        partial_core.diagnostics.is_empty(),
        "{:#?}",
        partial_core.diagnostics
    );

    let partial_call = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("partial_call"))
        .unwrap();
    let partial_call_body = BodySyntax::parse(&lexed, source, partial_call.body.unwrap());
    let partial_call_core =
        TypedBody::elaborate(partial_call, &partial_call_body, &index, &signatures);
    assert!(
        partial_call_core
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "partial handler unexpectedly discharged a whole-protocol callable: {:#?}",
        partial_call_core.diagnostics
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
fn handler_pattern_matrix_rejects_unreachable_rows_and_accepts_closed_bool_coverage() {
    let total = core_for(
        "core-handler-pattern-matrix-total@0.1.0",
        "effect Stop { die(value: Bool) -> !; } pub fn main() -> i64 { handle Stop::die(true) { Stop::die(true) => 1, Stop::die(false) => 2 } }",
    );
    assert!(total.diagnostics.is_empty(), "{:#?}", total.diagnostics);
    let flow = PlaceFlow::analyze(&total);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    let mir = MirLowering::lower(
        DefKey(Digest::of_bytes(b"core-handler-pattern-matrix-total")),
        &total,
        &flow,
    )
    .function
    .expect("total terminal handler lowers to MIR");
    assert!(mir.blocks.iter().flat_map(|block| &block.instructions).any(|instruction| {
        matches!(instruction, MirInstruction::PatternTest { pattern: MirPattern::Literal(value), .. } if value == "true")
    }));
    let artifact = grandiose_stage0::emit_vm(&mir).expect("pattern handler emits VM");
    let verified =
        grandiose_stage0::decode_and_verify_artifact(&grandiose_stage0::encode_artifact(&artifact))
            .expect("pattern handler VM artifact verifies");
    assert_eq!(verified.run_i64().expect("VM executes pattern dispatch"), 1);

    let unreachable = core_for(
        "core-handler-pattern-matrix-unreachable@0.1.0",
        "effect Stop { die(value: Bool) -> !; } pub fn main() -> i64 { handle Stop::die(true) { Stop::die(true) => 1, Stop::die(true) => 2, Stop::die(false) => 3 } }",
    );
    assert!(
        unreachable
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4175"),
        "unreachable terminal handler pattern was not diagnosed: {:#?}",
        unreachable.diagnostics
    );
}

#[test]
fn result_carried_bool_literals_and_patterns_remain_source_level_control() {
    let core = core_for(
        "core-result-bool-literals@0.1.0",
        "enum Result<T, E> { Ok(T), Err(E) } type Bool = Result<(), ()>; pub fn main(value: Bool) -> Bool { handle value { true => true, false => false } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let Some(completion) = core
        .expressions
        .iter()
        .find(|expression| matches!(expression.kind, CoreKind::Completion { .. }))
    else {
        panic!("result-carried Bool handle must lower to completion dispatch");
    };
    let CoreKind::Completion { clauses, .. } = &completion.kind else {
        unreachable!();
    };
    assert!(
        matches!(clauses[0].pattern, CorePattern::Enum { variant: 0, .. }),
        "{clauses:#?}"
    );
    assert!(matches!(
        clauses[1].pattern,
        CorePattern::Enum { variant: 1, .. }
    ));
    for clause in clauses {
        assert!(matches!(
            core.expression(clause.body).kind,
            CoreKind::Enum { fields: ref values, .. } if values.len() == 1
        ));
    }
}

#[test]
fn nominal_bool_control_accepts_concrete_integer_comparisons_and_terminal_handlers() {
    let comparison = core_for(
        "core-nominal-bool-integer-comparison@0.1.0",
        "enum Result<T, E> { Ok(T), Err(E) } type Bool = Result<(), ()>; infixl 20 <=; pub fn main(value: u32) -> Bool { handle value <= 1114111 { true => true, false => false } }",
    );
    assert!(
        comparison.diagnostics.is_empty(),
        "{:#?}",
        comparison.diagnostics
    );
    assert!(comparison.expressions.iter().any(|expression| {
        matches!(
            expression.kind,
            CoreKind::IntrinsicCall { ref operator, ref arguments }
                if operator == "<="
                    && arguments.len() == 2
                    && comparison.expression(arguments[1]).ty == Type::Scalar(ScalarType::U32)
        )
    }));

    let reversed_comparison = core_for(
        "core-nominal-bool-reversed-integer-comparison@0.1.0",
        "enum Result<T, E> { Ok(T), Err(E) } type Bool = Result<(), ()>; infixl 20 <; pub fn main(value: u32) -> Bool { handle value < 55296 { true => true, false => 57343 < value } }",
    );
    assert!(
        reversed_comparison.diagnostics.is_empty(),
        "{:#?}",
        reversed_comparison.diagnostics
    );
    assert!(reversed_comparison.expressions.iter().any(|expression| {
        matches!(
            expression.kind,
            CoreKind::IntrinsicCall { ref operator, ref arguments }
                if operator == "<"
                    && arguments.len() == 2
                    && reversed_comparison.expression(arguments[0]).ty == Type::Scalar(ScalarType::U32)
                    && reversed_comparison.expression(arguments[1]).ty == Type::Scalar(ScalarType::U32)
        )
    }));

    let terminal_handler = core_for(
        "core-nominal-bool-terminal-handler@0.1.0",
        "enum Result<T, E> { Ok(T), Err(E) } type Bool = Result<(), ()>; effect Branch { select(value: u32) -> ! } pub fn main(value: u32) -> Bool { handle Branch::select(value) { Branch::select(0) => false, Branch::select(_) => true } }",
    );
    assert!(
        terminal_handler.diagnostics.is_empty(),
        "{:#?}",
        terminal_handler.diagnostics
    );
    assert_eq!(
        terminal_handler.expression(terminal_handler.root).ty,
        terminal_handler
            .expressions
            .iter()
            .find_map(|expression| {
                matches!(expression.kind, CoreKind::Enum { .. }).then(|| expression.ty.clone())
            })
            .expect("terminal handler Bool literals lower to the nominal carrier")
    );
}

#[test]
fn source_infix_callable_contextualizes_a_higher_order_fallback_closure() {
    let core = core_for(
        "core-infix-lazy-fallback@0.1.0",
        "enum Result<T, E> { Ok(T), Err(E) } type Bool = Result<(), ()>; infixr 1 else; if<A, E, B, F>(condition: Result<A, E>, body: F) -> Result<B, E> where F: Fn<(), Output = B> { condition } else<A, E, F>(value: Result<A, E>, fallback: F) -> A where F: Fn<(), Output = A> { fallback() } pub fn main<'a, A, E>(condition: Bool, value: &'a Result<A, E>) -> &'a Result<A, E> { if(condition) { value } else { value } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert_eq!(
        core.expressions
            .iter()
            .filter(|expression| matches!(expression.kind, CoreKind::Closure { .. }))
            .count(),
        2,
        "both lazy branches must receive the direct Fn contract"
    );
    assert!(matches!(
        core.expression(core.root).ty,
        Type::Reference { .. },
    ));
}

#[test]
fn canonical_option_some_alias_lowers_to_its_enum_constructor() {
    let core = core_for(
        "core-option-some-alias@0.1.0",
        "enum Result<T, E> { Ok(T), Err(E) } type Option<T> = Result<T, ()>; let Option::Some = Result::Ok; pub fn main() -> Option<u8> { Option::Some(7) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            expression.kind,
            CoreKind::Enum { fields: ref values, .. } if values.len() == 1
        )
    }));
}

#[test]
fn contextual_if_accepts_affine_condition_payloads() {
    let core = core_for(
        "core-contextual-if-structural-use@0.1.0",
        "enum Result<T, E> { Ok(T), Err(E) } if<A, E, B, F>(condition: Result<A, E>, body: F) -> Result<B, E> where F: Fn<(), Output = B>, A: Use<[0, 1]> { condition } pub fn main() -> Result<i64, ()> { if(Result::Ok(())) { 7 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn direct_float_calls_contextualize_signed_numeric_literals() {
    let core = core_for(
        "core-contextual-signed-float-literal@0.1.0",
        "fn accept(value: f32) -> f32 { value } pub fn main() -> f32 { accept(-128.0) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            expression.kind,
            CoreKind::IntrinsicCall { ref operator, .. } if operator == "-"
        )
    }));
}

#[test]
fn handler_pattern_matrix_rejects_duplicate_unbounded_literal_rows() {
    let core = core_for(
        "core-handler-pattern-unbounded-literal@0.1.0",
        "effect Stop { die(value: i64) -> !; } pub fn main() -> i64 { handle Stop::die(41) { Stop::die(41) => 1, Stop::die(41) => 2, Stop::die(value) => 3 } }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4175"),
        "duplicate i64 handler literal was not diagnosed: {:#?}",
        core.diagnostics
    );
}

#[test]
fn nested_partial_handlers_compose_to_discharge_a_callable_effect_contract() {
    let source = "effect Choice { first() -> i64; second() -> i64; } pub fn worker() -> i64 / Choice { Choice::first() } pub fn main() -> i64 / Choice { handle { handle worker() { Choice::first() => 10 } } { Choice::second() => 20 } }";
    let core = core_for("core-composed-partial-handler-contract@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);

    let clauses = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Handle { clauses, .. }
                if clauses.iter().any(|clause| clause.operation == 0) =>
            {
                Some(clauses)
            }
            _ => None,
        })
        .expect("inner partial handler");
    let contract = clauses[0]
        .continuation
        .as_ref()
        .expect("nonterminal handler continuation contract");
    assert_eq!(contract.direct_uses, 1, "tail resume is one use");
    assert!(
        contract.effects.effects.is_empty(),
        "nested partial coverage failed to subtract Choice from the continuation row: {contract:#?}"
    );
}

#[test]
fn handler_clause_reintroduces_its_effect_while_preserving_an_open_continuation_row() {
    let core = core_for(
        "core-handler-clause-open-row@0.1.0",
        "effect Ask { [0,1] ask() -> i64; } pub fn main<e: EffectRow>() -> i64 / {Ask | e} { handle Ask::ask() { Ask::ask() => Ask::ask() } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let clauses = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Handle { clauses, .. } => Some(clauses),
            _ => None,
        })
        .expect("handler Core node");
    let clause = clauses.first().expect("Ask clause");
    let continuation = clause
        .continuation
        .as_ref()
        .expect("nonterminal continuation contract");
    assert!(continuation.effects.effects.is_empty());
    assert_eq!(continuation.effects.tail, Some(EffectTail::Generic(0)));
    assert!(matches!(
        core.expression(clause.body).kind,
        CoreKind::Perform { .. }
    ));
}

#[test]
fn handler_contract_rejects_implicit_or_explicit_resume_when_zero_uses_are_required() {
    let tail = core_for(
        "core-handler-zero-tail@0.1.0",
        "effect Stop { [0,0] stop() -> i64; } pub fn main() -> i64 { handle Stop::stop() { Stop::stop() => 0 } }",
    );
    assert!(
        tail.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6005"),
        "implicit tail resume ignored a zero-use contract: {:#?}",
        tail.diagnostics
    );

    let explicit = core_for(
        "core-handler-zero-explicit@0.1.0",
        "effect Stop { [0,0] stop() -> i64; } pub fn main() -> i64 { handle Stop::stop() { Stop::stop() with k => k(0) } }",
    );
    assert!(
        explicit
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6005"),
        "explicit resume ignored a zero-use contract: {:#?}",
        explicit.diagnostics
    );
}

#[test]
fn handler_contract_rejects_dropping_a_required_explicit_resumption() {
    let core = core_for(
        "core-handler-required-explicit@0.1.0",
        "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => 0 } }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4178"),
        "required explicit resumption was silently discarded: {:#?}",
        core.diagnostics
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
            CoreKind::Closure { environment, .. } => Some(&environment.captures),
            _ => None,
        })
        .expect("handler clause closure was not elaborated");
    assert_eq!(closure.len(), 1);
    assert_eq!(closure[0].name, "value");
}

#[test]
fn handler_resumption_cannot_escape_through_a_nested_closure_capture() {
    let package = PackageKey("core-handler-resumption-escape@0.1.0".into());
    let source = "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => { let delayed = (ignored: i64) -> i64 { let saved = k; 0 }; 0 } } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4174"),
        "nested closure captured a handler continuation: {:#?}",
        core.diagnostics
    );
    let captures = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Closure { environment, .. } => Some(&environment.captures),
            _ => None,
        })
        .expect("nested closure");
    assert!(
        captures.iter().any(|capture| capture.name == "k"),
        "regression fixture did not capture the handler resumption: {captures:#?}"
    );
}

#[test]
fn handler_resumption_alias_preserves_the_same_snapshot_identity() {
    let package = PackageKey("core-handler-resumption-alias@0.1.0".into());
    let source = "effect Ask { [1, 1] ask() -> i64; } effect Log { [1, 1] log(value: i64) -> i64; } pub fn main() -> i64 / Log { handle { let answer = Ask::ask(); Log::log(answer) } { Ask::ask() with k => { let saved = k; saved(41) } } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let snapshots = core
        .expressions
        .iter()
        .filter_map(|expression| match &expression.kind {
            CoreKind::Resumption { id, .. } => Some(*id),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(snapshots.len(), 2, "alias must remain explicit in Core");
    assert_eq!(
        snapshots[0], snapshots[1],
        "alias changed snapshot identity"
    );
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    let mir = MirLowering::lower(definition.key, &core, &flow);
    assert!(mir.diagnostics.is_empty(), "{:#?}", mir.diagnostics);
    let function = mir.function.expect("aliased snapshot must lower");
    let instructions = function
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
        .collect::<Vec<_>>();
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::CaptureResumption { .. })),
        "MIR erased the first-class snapshot: {instructions:#?}"
    );
    let snapshot = instructions
        .iter()
        .find_map(|instruction| match instruction {
            MirInstruction::CaptureResumption { dst, .. } => Some(*dst),
            _ => None,
        })
        .expect("MIR captured the alias above");
    assert!(
        matches!(
            &function.locals[snapshot.0 as usize].ty,
            Type::Callable { effects, .. } if !effects.effects.is_empty()
        ),
        "the snapshot lost its residual outward effects: {:#?}",
        function.locals[snapshot.0 as usize]
    );
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::ResumeSnapshot { .. })),
        "MIR resumed through an implicit frame instead of the snapshot: {instructions:#?}"
    );
}

#[test]
fn nested_local_shadowing_does_not_turn_an_ordinary_value_into_a_resumption() {
    let package = PackageKey("core-handler-resumption-shadow@0.1.0".into());
    let source = "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => { let shadow = (k: i64) -> i64 { k }; let ignored = shadow(0); k(42) } } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        !core
            .diagnostics
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G4174" | "G4175")),
        "a shadowing local was mistaken for the outer resumption: {:#?}",
        core.diagnostics
    );
}

#[test]
fn a_nested_handler_payload_can_shadow_an_outer_resumption_for_capture_analysis() {
    let package = PackageKey("core-handler-resumption-capture-shadow@0.1.0".into());
    let source = "effect Ask { [1, 1] ask() -> i64; } effect Inner { [1, 1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => { let inside = handle Inner::ask(1) { Inner::ask(k) => { let delayed = (ignored: i64) -> i64 { k }; 0 } }; k(42) } } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        !core
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4174"),
        "a closure captured the nested payload, not the outer resumption: {:#?}",
        core.diagnostics
    );
    let closure = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Closure { environment, .. }
                if environment
                    .captures
                    .iter()
                    .any(|capture| capture.name == "k") =>
            {
                Some(&environment.captures)
            }
            _ => None,
        })
        .expect("nested payload closure");
    assert_eq!(closure[0].name, "k");
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
            CoreKind::Closure { environment, .. } => Some(&environment.captures),
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
        grandiose_stage0::GenericArgument::Type(grandiose_stage0::Type::Scalar(
            grandiose_stage0::ScalarType::I64
        ))
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
fn handler_effect_application_arity_is_diagnosed_as_an_operation_arm() {
    let source = "effect State<S> { get() -> S; } pub fn main() -> i64 { handle State<i64>::get() { State<i64, Text>::get() => 0 } }";
    let package = PackageKey("core-handler-effect-arity@0.1.0".into());
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
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4163"),
        "misapplied handler protocol was not diagnosed as an operation arm: {:#?}",
        core.diagnostics
    );
}

#[test]
fn effect_operation_generic_kind_mismatches_reach_the_contract_boundary() {
    let core = core_for(
        "core-effect-generic-kind@0.1.0",
        "effect State<T> { get() -> T; } pub fn main() -> i64 { State<'static>::get() }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4152"),
        "lifetime syntax was not preserved to effect generic-contract checking: {:#?}",
        core.diagnostics
    );
}

#[test]
fn placeflow_joins_handler_arms_conservatively_after_dynamic_selection() {
    let package = PackageKey("core-handler-flow@0.1.0".into());
    let source = "effect Console { read(value: Bool) -> i64; } pub fn main() -> i64 { let value = 7; handle Console::read(true) { Console::read(true) => move value, Console::read(false) => 0 }; value }";
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
fn normalized_quantity_bounds_drive_finite_resumption_core_and_mir_contracts() {
    let package = PackageKey("core-handler-quantity-arithmetic@0.1.0".into());
    let source = "effect Ask<budget: Quantity> { [1 + 1, 3 - 1] ask() -> i64; } pub fn main() -> i64 { handle Ask<[2, 2]>::ask() { Ask<[2, 2]>::ask() with resume => resume(40) + resume(41) } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let continuation = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Handle { clauses, .. } => clauses.first()?.continuation.as_ref(),
            _ => None,
        })
        .expect("handler continuation contract");
    assert_eq!(continuation.invocation, Quantity::new(2, Some(2)).unwrap());
    assert_eq!(continuation.direct_uses, 2);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .expect("finite normalized resumption lowers to MIR");
    assert!(mir.validate().is_ok(), "{mir:#?}");
    assert!(
        mir.blocks.len() >= 2,
        "finite replay must retain an executable MIR schedule: {mir:#?}"
    );
}

#[test]
fn nested_handler_arms_preserve_outer_resumption_use_tracking() {
    let core = core_for(
        "core-nested-resumption-use-tracking@0.1.0",
        "effect Ask { [1,1] ask() -> i64; } effect Ping { [1,1] ping() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with outer => handle Ping::ping() { Ping::ping() with inner => { let value = inner(41); outer(value) } } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let mut uses = core
        .expressions
        .iter()
        .filter_map(|expression| match &expression.kind {
            CoreKind::Handle { clauses, .. } => clauses.first()?.continuation.as_ref(),
            _ => None,
        })
        .map(|continuation| continuation.direct_uses)
        .collect::<Vec<_>>();
    uses.sort_unstable();
    assert_eq!(uses, vec![1, 1]);
}

#[test]
fn nested_handler_arms_reject_excess_outer_resumption_uses() {
    let core = core_for(
        "core-nested-resumption-use-rejection@0.1.0",
        "effect Ask { [1,1] ask() -> i64; } effect Ping { [1,1] ping() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with outer => handle Ping::ping() { Ping::ping() with inner => { let value = inner(41); outer(value) + outer(value) } } } }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6005"),
        "the outer [1, 1] continuation must observe both nested calls: {:#?}",
        core.diagnostics
    );
}

#[test]
fn normalized_quantity_bounds_reject_implicit_one_shot_resumption() {
    let core = core_for(
        "core-handler-quantity-arithmetic-rejection@0.1.0",
        "effect Ask<budget: Quantity> { [1 + 1, 3 - 1] ask() -> i64; } pub fn main() -> i64 { handle Ask<[2, 2]>::ask() { Ask<[2, 2]>::ask() => 42 } }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6005"),
        "tail resumption must not be admitted by a normalized exact-two contract: {:#?}",
        core.diagnostics
    );
}

#[test]
fn affine_discarded_resumption_lowers_to_a_runtime_handler_cancellation() {
    let package = PackageKey("core-handler-cancel@0.1.0".into());
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask(_) => 42 } }";
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
        .expect("affine cancellation lowers to MIR");
    assert!(mir.blocks.iter().any(|block| {
        block
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::Cancel { .. }))
    }));
}

#[test]
fn mir_lowering_rejects_cancellation_that_violates_a_frozen_required_resume_contract() {
    let mut core = core_for(
        "core-handler-frozen-cleanup-contract@0.1.0",
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask() with _ => 7 } }",
    );
    let clause = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Handle { clauses, .. } => clauses.first_mut(),
            _ => None,
        })
        .expect("fixture must elaborate one handler clause");
    // Simulate a malformed post-Core transformation. The static-to-MIR
    // boundary must not lower a zero-use cleanup when the frozen contract has
    // been forged to require exactly one continuation use.
    clause
        .continuation
        .as_mut()
        .expect("discarded arm retains its continuation contract")
        .invocation = Quantity::ONCE;
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    let lowered = MirLowering::lower(
        grandiose_stage0::DefKey(grandiose_stage0::Digest::of_bytes(
            b"frozen-handler-cleanup-contract",
        )),
        &core,
        &flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "G6002"
                    && diagnostic.message.contains("resumption quantity disagrees")
            }),
        "lowering accepted cancellation that contradicted its frozen contract: {lowered:#?}"
    );
}

#[test]
fn escapeflow_allows_returning_an_incoming_reference_without_deriving_a_body_loan() {
    let source = "pub fn main(value: &i64) -> &i64 { value }";
    let core = core_for("core-escape-incoming-reference@0.1.0", source);
    let flow = PlaceFlow::analyze(&core);
    let escapes = EscapeFlow::analyze(&core, &flow);
    assert!(escapes.diagnostics.is_empty(), "{:#?}", escapes.diagnostics);
}

#[test]
fn escapeflow_rejects_storing_a_body_loan_through_external_reference_storage() {
    let core = core_for(
        "core-external-store-drop-check@0.1.0",
        "pub fn main(slot: &mut &i64) -> i64 { let value = 1; *slot = &value; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let escapes = EscapeFlow::analyze(&core, &flow);
    assert!(
        escapes
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5022"),
        "frozen Core let a body-local loan enter caller-owned storage: {escapes:#?}"
    );
}

#[test]
fn escapeflow_fails_closed_for_a_forged_nested_external_store_place() {
    let package = PackageKey("core-forged-nested-external-store@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let reference = Type::Reference {
        mutability: grandiose_stage0::Mutability::Shared,
        lifetime: Lifetime::Elided,
        referent: Box::new(Type::Scalar(ScalarType::I64)),
    };
    let slot = Type::Reference {
        mutability: grandiose_stage0::Mutability::Unique,
        lifetime: Lifetime::Elided,
        referent: Box::new(Type::Nominal {
            definition: DefKey(Digest::of_bytes(b"forged-external-holder")),
            arguments: vec![],
        }),
    };
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![("slot".into(), slot.clone())],
        expressions: vec![
            CoreExpr {
                kind: CoreKind::Local("slot".into()),
                ty: slot,
                span,
            },
            CoreExpr {
                kind: CoreKind::Literal("1".into()),
                ty: Type::Scalar(ScalarType::I64),
                span,
            },
            CoreExpr {
                kind: CoreKind::Let {
                    name: "value".into(),
                    value: CoreId(1),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Local("value".into()),
                ty: Type::Scalar(ScalarType::I64),
                span,
            },
            CoreExpr {
                kind: CoreKind::Borrow {
                    unique: false,
                    value: CoreId(3),
                },
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Assign {
                    place: CorePlace::Field {
                        base: Box::new(CorePlace::Deref {
                            reference: CoreId(0),
                            ty: Type::Nominal {
                                definition: DefKey(Digest::of_bytes(b"forged-external-holder")),
                                arguments: vec![],
                            },
                            unique: true,
                        }),
                        index: 0,
                        field_count: 1,
                        ty: reference,
                    },
                    value: CoreId(4),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Literal("0".into()),
                ty: Type::Scalar(ScalarType::I64),
                span,
            },
            CoreExpr {
                kind: CoreKind::Block(vec![CoreId(2), CoreId(5), CoreId(6)]),
                ty: Type::Scalar(ScalarType::I64),
                span,
            },
        ],
        root: CoreId(7),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(body.validate().is_empty(), "{:#?}", body.validate());
    let flow = PlaceFlow::analyze(&body);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let escapes = EscapeFlow::analyze(&body, &flow);
    assert!(
        escapes
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5022"),
        "frozen nested external store was not checked before lowering: {escapes:#?}"
    );
}

#[test]
fn call_lifetime_instantiation_preserves_a_generic_reference_relationship() {
    let source = r#"
        pub fn relay<'a>(value: &'a i64) -> &'a i64 { value }
        pub fn main() -> i64 {
            let value = 1;
            let loan = &value;
            let forwarded = relay(loan);
            forwarded;
            0
        }
    "#;
    let core = core_for("core-call-lifetime-instantiation@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(
        core.expressions.iter().any(|expression| matches!(
            expression.ty,
            Type::Reference {
                lifetime: Lifetime::Elided,
                ..
            }
        )),
        "callee lifetime was not instantiated into the caller: {core:#?}"
    );
}

#[test]
fn call_reference_provenance_tracks_tuple_and_nominal_result_paths() {
    let tuple = core_for(
        "core-call-reference-tuple-path@0.1.0",
        "pub fn relay<'a>(value: (&'a i64, i64)) -> (&'a i64, i64) { value } pub fn main() -> i64 { let value = 42; let pair = (&value, 0); let forwarded = relay(pair); 0 }",
    );
    assert!(tuple.diagnostics.is_empty(), "{:#?}", tuple.diagnostics);
    let tuple_call = tuple
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Call {
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(paths),
                ..
            } => Some(paths),
            _ => None,
        })
        .expect("tuple relay call provenance");
    assert_eq!(tuple_call.len(), 1);
    assert_eq!(tuple_call[0].result_fields, [0]);
    assert_eq!(tuple_call[0].argument, 0);
    assert_eq!(tuple_call[0].argument_fields, [0]);
    let tuple_flow = PlaceFlow::analyze(&tuple);
    assert!(tuple_flow.diagnostics.is_empty(), "{tuple_flow:#?}");

    let nominal = core_for(
        "core-call-reference-nominal-path@0.1.0",
        "pub struct Box<T> { value: T } pub fn relay<'a>(value: Box<&'a i64>) -> Box<&'a i64> { value } pub fn main() -> i64 { let value = 42; let boxed = Box { value: &value }; let forwarded = relay(boxed); 0 }",
    );
    assert!(nominal.diagnostics.is_empty(), "{:#?}", nominal.diagnostics);
    let nominal_flow = PlaceFlow::analyze(&nominal);
    assert!(nominal_flow.diagnostics.is_empty(), "{nominal_flow:#?}");
}

#[test]
fn generic_lifetime_relation_selects_the_precise_call_reference_argument() {
    let core = core_for(
        "core-call-reference-distinct-generic-lifetimes@0.1.0",
        "pub fn first<'a, 'b>(left: &'a i64, right: &'b i64) -> &'a i64 { left } pub fn main() -> i64 { let left = 1; let right = 2; let forwarded = first(&left, &right); left = 3; *forwarded }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        !flow
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "distinct generic lifetime relationship became opaque: {flow:#?}"
    );
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5007"),
        "call result did not retain the left argument's loan: {flow:#?}"
    );
}

#[test]
fn callable_contract_traverses_nominal_generic_reference_fields_before_opening() {
    let core = core_for(
        "core-call-reference-nominal-generic-contract@0.1.0",
        "type Ref = &i64; pub struct Pair<T> { value: T } pub struct Envelope<T> { pair: Pair<T> } pub fn relay<T>(value: Envelope<T>) -> Envelope<T> { value } pub fn main() -> Envelope<&i64> { let value = 1; let pair = Pair { value: &value }; let envelope = Envelope { pair: pair }; relay<Ref>(envelope) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let paths = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Call {
                reference_contract: grandiose_stage0::CallReferenceOrigin::Paths(paths),
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(origin),
                ..
            } => Some((paths, origin)),
            _ => None,
        })
        .expect("nominal callable contract did not freeze its reference field path");
    assert_eq!(paths.0[0].result_fields, [0, 0]);
    assert_eq!(paths.0[0].argument_fields, [0, 0]);
    assert_eq!(paths.1, paths.0);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        !flow
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "nominal generic reference path became opaque: {flow:#?}"
    );
}

#[test]
fn inferred_generic_aggregate_reference_paths_refine_after_instantiation() {
    let core = core_for(
        "core-call-reference-inferred-generic-aggregate@0.1.0",
        "pub fn relay<T>(value: T) -> T { value } pub fn main() -> (&i64, i64) { let value = 1; let pair = (&value, 0); relay(pair) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let call = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Call {
                reference_contract: grandiose_stage0::CallReferenceOrigin::Opaque,
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(paths),
                ..
            } => Some(paths),
            _ => None,
        })
        .expect("inferred generic aggregate did not refine its concrete reference path");
    assert_eq!(call[0].result_fields, [0]);
    assert_eq!(call[0].argument_fields, [0]);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        !flow
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "inferred generic aggregate result stayed opaque: {flow:#?}"
    );
}

#[test]
fn opaque_generic_result_shapes_distinguish_concrete_scalars_from_enum_reference_payloads() {
    let concrete = core_for(
        "core-opaque-reference-shape-concrete-generic@0.1.0",
        "pub enum Maybe<T> { Some(T), None } pub fn relay<T>(value: Maybe<T>) -> Maybe<T> { value } pub fn main() -> bool { let value = relay<i64>(Maybe<i64>::Some(41)); value is Maybe<i64>::Some(_) }",
    );
    assert!(
        concrete.diagnostics.is_empty(),
        "{:#?}",
        concrete.diagnostics
    );
    let (origin, shape) = concrete
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Call {
                reference_origin,
                reference_shape,
                ..
            } => Some((reference_origin, reference_shape)),
            _ => None,
        })
        .expect("generic enum call did not reach frozen Core");
    assert!(matches!(
        origin,
        grandiose_stage0::CallReferenceOrigin::None
    ));
    assert_eq!(*shape, grandiose_stage0::CallReferenceShape::None);
    assert!(
        !PlaceFlow::analyze(&concrete)
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "concrete non-reference generic materialization inherited declaration opacity"
    );

    let opaque = core_for(
        "core-opaque-reference-shape-enum-payload@0.1.0",
        "pub enum Maybe<T> { Some(T), None } pub fn relay<T>(value: Maybe<T>) -> Maybe<T> { value } pub fn main() -> Maybe<&i64> { let local = 1; relay(Maybe::Some(&local)) }",
    );
    assert!(opaque.diagnostics.is_empty(), "{:#?}", opaque.diagnostics);
    let (origin, shape) = opaque
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Call {
                reference_origin,
                reference_shape,
                ..
            } => Some((reference_origin, reference_shape)),
            _ => None,
        })
        .expect("opaque enum result call did not reach frozen Core");
    let grandiose_stage0::CallReferenceOrigin::Paths(paths) = origin else {
        panic!("variant-invariant enum payload lost frozen provenance: {origin:#?}");
    };
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].result_fields, [0]);
    assert_eq!(paths[0].argument, 0);
    assert_eq!(paths[0].argument_fields, [0]);
    assert_eq!(*shape, grandiose_stage0::CallReferenceShape::CallerPaths);
    let flow = PlaceFlow::analyze(&opaque);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    assert!(
        EscapeFlow::analyze(&opaque, &flow)
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "a variant-invariant reference payload still must not escape a body-local loan"
    );
}

#[test]
fn opaque_projection_results_defer_until_their_generic_head_is_instantiated() {
    let mut core = core_for(
        "core-opaque-reference-open-projection@0.1.0",
        "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(41) }",
    );
    let expression = core
        .expressions
        .iter_mut()
        .find(|expression| matches!(expression.kind, CoreKind::Call { .. }))
        .expect("generic call did not reach frozen Core");
    let CoreKind::Call {
        reference_origin,
        reference_shape,
        ..
    } = &mut expression.kind
    else {
        unreachable!("selected call expression")
    };
    *reference_origin = grandiose_stage0::CallReferenceOrigin::Opaque;
    *reference_shape = grandiose_stage0::CallReferenceShape::OpaquePotentiallyReference;
    expression.ty = Type::Projection {
        subject: Box::new(Type::Generic(0)),
        trait_definition: DefKey(Digest::of_bytes(b"opaque-open-projection-trait")),
        trait_arguments: vec![
            GenericArgument::Type(Type::Generic(1)),
            GenericArgument::EffectRow(EffectRow {
                effects: BTreeSet::new(),
                projections: vec![],
                tail: Some(EffectTail::Generic(2)),
            }),
        ],
        name: "Output".into(),
        item_generic_kinds: vec![],
        item_arguments: vec![],
    };

    assert!(
        !PlaceFlow::analyze(&core)
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "an open projection head was rejected before a concrete instance exists"
    );
    assert!(
        !EscapeFlow::analyze(&core, &PlaceFlow::analyze(&core))
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "escape checking did not defer an open projection head"
    );
}

#[test]
fn forged_opaque_result_shape_cannot_bypass_core_or_mir_validation() {
    let mut core = core_for(
        "core-forged-opaque-reference-shape@0.1.0",
        "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(41) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let shape = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Call {
                reference_shape, ..
            } => Some(reference_shape),
            _ => None,
        })
        .expect("generic scalar call did not reach frozen Core");
    *shape = grandiose_stage0::CallReferenceShape::OpaquePotentiallyReference;
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4187"),
        "forged opaque result shape was accepted by Core: {:#?}",
        core.validate()
    );
    let flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-opaque-reference-shape")),
        &core,
        &flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR accepted a forged opaque result shape: {lowered:#?}"
    );
}

#[test]
fn forged_nominal_callable_contract_cannot_retarget_a_sibling_argument() {
    let mut core = core_for(
        "core-forged-nominal-call-reference-relation@0.1.0",
        "type Ref = &i64; type FlagRef = &Bool; pub struct Pair<T> { value: T } pub fn first<T, U>(left: Pair<T>, right: Pair<U>) -> Pair<T> { left } pub fn main() -> Pair<&i64> { let left = 1; let right = true; let left_pair = Pair { value: &left }; let right_pair = Pair { value: &right }; first<Ref, FlagRef>(left_pair, right_pair) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let (contract, origin) = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Call {
                reference_contract: grandiose_stage0::CallReferenceOrigin::Paths(contract),
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(origin),
                ..
            } => Some((contract, origin)),
            _ => None,
        })
        .expect("nominal callable relation did not reach frozen Core");
    assert_eq!(contract[0].argument, 0);
    origin[0].argument = 1;
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4187"),
        "forged nominal relation retargeted a sibling argument: {:#?}",
        core.validate()
    );
    let flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-nominal-call-reference-relation")),
        &core,
        &flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR accepted a forged nominal callable relation: {lowered:#?}"
    );
}

#[test]
fn forged_call_reference_paths_fail_closed_before_ownership() {
    let mut core = core_for(
        "core-forged-call-reference-path@0.1.0",
        "pub fn relay<'a>(value: (&'a i64, i64)) -> (&'a i64, i64) { value } pub fn main() -> i64 { let value = 1; let pair = (&value, 0); let forwarded = relay(pair); *forwarded.0 }",
    );
    let call = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Call {
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(paths),
                ..
            } => Some(paths),
            _ => None,
        })
        .expect("relay call provenance");
    call[0].argument = 99;
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4187"),
        "forged call provenance path was accepted: {:#?}",
        core.validate()
    );
}

#[test]
fn call_reference_provenance_preserves_return_and_suspension_escape_obligations() {
    let returned = core_for(
        "core-call-reference-return-escape@0.1.0",
        "pub fn relay<'a>(value: &'a i64) -> &'a i64 { value } pub fn main() -> &i64 { let value = 1; relay(&value) }",
    );
    assert!(
        returned.diagnostics.is_empty(),
        "{:#?}",
        returned.diagnostics
    );
    let returned_flow = PlaceFlow::analyze(&returned);
    let returned_escape = EscapeFlow::analyze(&returned, &returned_flow);
    assert!(
        returned_escape
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "a relayed body-local reference escaped through a call result: {returned_escape:#?}"
    );

    let suspended = core_for(
        "core-call-reference-suspension-escape@0.1.0",
        "effect Save { [0, 1] save(value: &i64); } pub fn relay<'a>(value: &'a i64) -> &'a i64 { value } pub fn main() -> i64 / {Save} { let value = 1; handle Save::save(relay(&value)) { Save::save(_) with _ => () }; 0 }",
    );
    assert!(
        suspended.diagnostics.is_empty(),
        "{:#?}",
        suspended.diagnostics
    );
    let suspended_flow = PlaceFlow::analyze(&suspended);
    let suspended_escape = EscapeFlow::analyze(&suspended, &suspended_flow);
    assert!(
        suspended_escape
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5015"),
        "a cancellation handler hid a relayed body-local reference from suspension checking: {suspended_escape:#?}"
    );
}

#[test]
fn performed_operations_freeze_generic_reference_provenance() {
    let core = core_for(
        "core-perform-reference-generic@0.1.0",
        "effect Relay<T> { [0, 1] relay(value: &T) -> &T; } pub fn main() -> &i64 / {Relay<i64>} { let value = 1; Relay<i64>::relay(&value) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let perform = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Perform {
                effect,
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(paths),
                ..
            } => Some((effect, paths)),
            _ => None,
        })
        .expect("generic effect performance did not retain reference provenance");
    assert_eq!(perform.0.arguments.len(), 1);
    assert_eq!(perform.1.len(), 1);
    assert_eq!(perform.1[0].result_fields, Vec::<u32>::new());
    assert_eq!(perform.1[0].argument, 0);
    assert_eq!(perform.1[0].argument_fields, Vec::<u32>::new());

    let flow = PlaceFlow::analyze(&core);
    let escapes = EscapeFlow::analyze(&core, &flow);
    assert!(
        escapes
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "performed reference result hid a body-local return: {escapes:#?}"
    );
}

#[test]
fn forged_perform_effect_row_inference_cannot_cross_the_core_boundary() {
    let mut core = core_for(
        "core-forged-perform-effect-row-inference@0.1.0",
        "effect Relay<e: EffectRow> { [0, 1] relay(value: i64) -> i64; } pub fn main() -> i64 / {Relay<{}>} { Relay<{}>::relay(42) }",
    );
    let perform = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Perform { effect, .. } => Some(effect),
            _ => None,
        })
        .expect("generic effect operation did not reach Core");
    perform.arguments[0] = GenericArgument::EffectRow(EffectRow {
        effects: BTreeSet::new(),
        projections: vec![],
        tail: Some(EffectTail::Infer(EffectVar(0))),
    });
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4181"),
        "an unresolved effect row in performed-operation metadata reached frozen Core: {:#?}",
        core.validate()
    );
    let flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-perform-effect-row-inference")),
        &core,
        &flow,
    );
    assert!(lowered.function.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR lowering must independently reject a forged performed-operation row"
    );
}

#[test]
fn performed_operations_freeze_payload_callable_contracts_for_quantity_checking() {
    let package = PackageKey("core-perform-payload-quantity@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let callable_type = |invocation| Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![Type::Scalar(ScalarType::I64)],
        result: Box::new(Type::Scalar(ScalarType::I64)),
        effects: EffectRow::empty(),
        invocation,
    };
    for quantity in [Quantity::AFFINE, Quantity::new(2, Some(2)).unwrap()] {
        let callback = callable_type(quantity);
        let mut core = TypedBody {
            safety: grandiose_stage0::Safety::Safe,
            unsafe_scopes: Default::default(),
            unsafe_implementations: Default::default(),
            parameters: vec![("callback".into(), callback.clone())],
            expressions: vec![
                CoreExpr {
                    kind: CoreKind::Local("callback".into()),
                    ty: callback.clone(),
                    span,
                },
                CoreExpr {
                    kind: CoreKind::Perform {
                        effect: EffectInstance {
                            definition: DefKey(Digest::of_bytes(b"payload-quantity-effect")),
                            arguments: vec![],
                        },
                        operation: 0,
                        payload_types: vec![callback.clone()],
                        arguments: vec![CoreId(0)],
                        terminal: false,
                        reference_contract: grandiose_stage0::CallReferenceOrigin::None,
                        reference_origin: grandiose_stage0::CallReferenceOrigin::None,
                        reference_shape: grandiose_stage0::CallReferenceShape::None,
                    },
                    ty: Type::Unit,
                    span,
                },
            ],
            root: CoreId(1),
            diagnostics: vec![],
            recovered: false,
        };
        assert!(core.validate().is_empty(), "{:#?}", core.validate());
        let flow = PlaceFlow::analyze(&core);
        assert!(flow.diagnostics.is_empty(), "{flow:#?}");
        let uses = UseFlow::analyze(&core, &flow);
        assert!(uses.diagnostics.is_empty(), "{uses:#?}");
        assert!(uses.callable_escapes.iter().any(|escape| {
            escape.name == "callback"
                && escape.required == Some(quantity)
                && escape.actual == Quantity::ONCE
        }));

        // A forged ABI may not retarget the transfer to a wider or narrower
        // payload contract after Core was frozen.
        {
            let CoreKind::Perform { payload_types, .. } = &mut core.expressions[1].kind else {
                unreachable!("forged effect performance")
            };
            payload_types[0] = callable_type(Quantity::ONCE);
        }
        assert!(
            core.validate()
                .iter()
                .any(|diagnostic| diagnostic.code == "G4183"),
            "forged payload quantity contract was accepted: {:#?}",
            core.validate()
        );
        {
            let CoreKind::Perform { payload_types, .. } = &mut core.expressions[1].kind else {
                unreachable!("forged effect performance")
            };
            payload_types.clear();
        }
        assert!(
            core.validate().iter().any(|diagnostic| {
                diagnostic.code == "G4183"
                    && diagnostic.message.contains("payload contract entries")
            }),
            "forged payload arity contract was accepted: {:#?}",
            core.validate()
        );
    }
}

#[test]
fn forged_perform_reference_provenance_fails_core_validation() {
    let mut core = core_for(
        "core-forged-perform-reference@0.1.0",
        "effect Relay { [0, 1] relay(value: &i64) -> &i64; } pub fn main() -> &i64 / {Relay} { let value = 1; Relay::relay(&value) }",
    );
    let origin = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Perform {
                reference_origin, ..
            } => Some(reference_origin),
            _ => None,
        })
        .expect("performed operation did not reach Core");
    *origin = grandiose_stage0::CallReferenceOrigin::None;
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4187"),
        "forged performed-operation provenance was accepted: {:#?}",
        core.validate()
    );
}

#[test]
fn effect_operation_contract_freezes_the_selected_generic_lifetime_path() {
    let mut core = core_for(
        "core-perform-distinct-lifetime-contract@0.1.0",
        "effect Select<'a, 'b> { [0, 1] choose(left: &'a i64, right: &'b i64) -> &'a i64; } pub fn main<'a, 'b>(left: &'a i64, right: &'b i64) -> &'a i64 / {Select<'a, 'b>} { Select<'a, 'b>::choose(left, right) }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let (contract, origin) = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Perform {
                reference_contract,
                reference_origin,
                ..
            } => Some((reference_contract, reference_origin)),
            _ => None,
        })
        .expect("effect operation did not retain a frozen lifetime contract");
    assert!(
        matches!(contract, grandiose_stage0::CallReferenceOrigin::Paths(paths) if paths.len() == 1 && paths[0].argument == 0)
    );
    assert_eq!(origin, contract);
    *origin =
        grandiose_stage0::CallReferenceOrigin::Paths(vec![grandiose_stage0::CallReferencePath {
            result_fields: vec![],
            argument: 1,
            argument_fields: vec![],
        }]);
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4187"),
        "forged effect operation retargeted a distinct generic lifetime: {:#?}",
        core.validate()
    );
    let flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(
            b"forged-effect-operation-lifetime-relation",
        )),
        &core,
        &flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR accepted a forged effect operation lifetime relation: {lowered:#?}"
    );
}

#[test]
fn mixed_static_and_caller_reference_results_preserve_only_caller_paths() {
    let call = core_for(
        "core-mixed-static-call-reference@0.1.0",
        "pub fn pair<'a>(stable: &'static i64, value: &'a i64) -> (&'static i64, &'a i64) { (stable, value) } pub fn main(stable: &'static i64) -> i64 { let local = 1; let result = pair(stable, &local); 0 }",
    );
    assert!(call.diagnostics.is_empty(), "{:#?}", call.diagnostics);
    let call_paths = call
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Call {
                reference_contract: grandiose_stage0::CallReferenceOrigin::Paths(contract),
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(origin),
                ..
            } => Some((contract, origin)),
            _ => None,
        })
        .expect("mixed call result was treated as opaque");
    assert_eq!(call_paths.0.len(), 1);
    assert_eq!(call_paths.0[0].result_fields, [1]);
    assert_eq!(call_paths.0[0].argument, 1);
    assert_eq!(call_paths.1, call_paths.0);
    assert!(
        !PlaceFlow::analyze(&call)
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "mixed call result lost its caller reference path"
    );

    let perform = core_for(
        "core-mixed-static-perform-reference@0.1.0",
        "effect Pair<'a> { [0, 1] pair(stable: &'static i64, value: &'a i64) -> (&'static i64, &'a i64); } pub fn main<'a>(stable: &'static i64, value: &'a i64) -> i64 / {Pair<'a>} { let result = Pair<'a>::pair(stable, value); 0 }",
    );
    assert!(perform.diagnostics.is_empty(), "{:#?}", perform.diagnostics);
    let paths = perform
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Perform {
                reference_contract: grandiose_stage0::CallReferenceOrigin::Paths(contract),
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(origin),
                ..
            } => Some((contract, origin)),
            _ => None,
        })
        .expect("mixed effect result was treated as opaque");
    assert_eq!(paths.0.len(), 1);
    assert_eq!(paths.0[0].result_fields, [1]);
    assert_eq!(paths.0[0].argument, 1);
    assert_eq!(paths.1, paths.0);
    assert!(
        !PlaceFlow::analyze(&perform)
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "mixed effect result lost its caller reference path"
    );
}

#[test]
fn placeflow_seeds_hidden_reference_leaves_from_the_parameter_interface() {
    let source = "pub struct Window<'a> { private storage: &'a i64 } pub struct Wrapped<'a> { private padding: i64, private window: Window<'a> } pub fn project<'a>(value: Wrapped<'a>) -> &'a i64 { value.window.storage } pub fn main<'a>(value: Wrapped<'a>) -> i64 { let result = project(value); *result }";
    let (core, signatures) = core_and_signatures_for("parameter-layout-provenance@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze_with_interface(&core, &signatures);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert!(flow.events.iter().any(|event| matches!(&event.kind, FlowEventKind::Reborrow(root) if root == "value")));
    // A caller-path assertion alone is not proof that an opaque parameter
    // actually contains a reference. The no-interface entry remains closed.
    assert!(PlaceFlow::analyze(&core).diagnostics.iter().any(|error| error.code == "G5023"));
    let lifted = PlaceFlow::analyze_lifted_with_interface(&core, core.root, &core.parameters, &signatures);
    assert!(lifted.diagnostics.is_empty(), "{:#?}", lifted.diagnostics);

    let source = "pub struct Window<'a> { private storage: &'a mut i64 } pub fn project<'a>(value: Window<'a>) -> &'a mut i64 { value.storage } pub fn main<'a>(value: Window<'a>) -> i64 { let result = project(value); *value.storage = 3; *result }";
    let (core, signatures) = core_and_signatures_for("parameter-layout-unique-conflict@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze_with_interface(&core, &signatures);
    assert!(flow.diagnostics.iter().any(|error| matches!(error.code, "G5001" | "G5004")), "{:#?}", flow.diagnostics);
}

#[test]
fn placeflow_seeds_caller_reference_parameter_provenance() {
    let core = core_for(
        "core-caller-parameter-reborrow@0.1.0",
        "pub fn main(slot: &mut i64) -> i64 { let child = &mut *slot; *child }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        !flow
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5006"),
        "caller-owned reference parameter did not seed a reborrow parent: {flow:#?}"
    );

    let conflicting = core_for(
        "core-caller-parameter-reborrow-conflict@0.1.0",
        "pub fn main(slot: &mut i64) -> i64 { let child = &mut *slot; *slot = 2; *child }",
    );
    assert!(
        conflicting.diagnostics.is_empty(),
        "{:#?}",
        conflicting.diagnostics
    );
    assert!(
        PlaceFlow::analyze(&conflicting)
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "live child reborrow did not suspend the caller-owned parent"
    );
}

#[test]
fn handler_payload_reference_alias_preserves_its_parent_loan() {
    let core = core_for(
        "core-handler-payload-reference-provenance@0.1.0",
        "effect Relay { [0, 1] relay(value: &mut i64) -> i64; } pub fn main() -> i64 { let value = 1; let parent = &mut value; handle Relay::relay(parent) { Relay::relay(payload) with _ => { let child = &mut *payload; *child } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        !flow
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5006"),
        "handler payload lost the caller loan before its reborrow: {flow:#?}"
    );
}

#[test]
fn placeflow_allows_and_tracks_a_reborrow_through_an_aggregate_reference_field() {
    let core = core_for(
        "core-aggregate-reference-reborrow@0.1.0",
        "pub struct Holder { loan: &mut i64, tag: i64 } pub fn main() -> i64 { let value = 1; let holder = Holder { loan: &mut value, tag: 0 }; let child = &mut *holder.loan; *child }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    assert!(
        flow.events.iter().any(|event| matches!(
            event.kind,
            FlowEventKind::Reborrow(ref root) if root == "value"
        )),
        "aggregate-held reborrow did not retain its backing place: {flow:#?}"
    );
}

#[test]
fn placeflow_rejects_access_through_aggregate_parent_while_unique_child_reborrow_is_live() {
    let core = core_for(
        "core-aggregate-reference-reborrow-conflict@0.1.0",
        "pub struct Holder { loan: &mut i64, tag: i64 } pub fn main() -> i64 { let value = 1; let holder = Holder { loan: &mut value, tag: 0 }; let child = &mut *holder.loan; let observed = *holder.loan; *child + observed }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "a live child reborrow did not suspend aggregate-held parent access: {flow:#?}"
    );
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"aggregate-reference-reborrow-conflict")),
        &core,
        &flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6001"),
        "MIR accepted the aggregate reborrow conflict that PlaceFlow rejected: {lowered:#?}"
    );
}

#[test]
fn placeflow_releases_aggregate_reborrows_after_their_last_handler_use() {
    let core = core_for(
        "core-aggregate-reference-reborrow-handler-join@0.1.0",
        "pub struct Holder { loan: &mut i64, tag: i64 } effect Tick { [1, 1] tick() -> i64; } pub fn main() -> i64 { let value = 1; let holder = Holder { loan: &mut value, tag: 0 }; let child = &mut *holder.loan; handle Tick::tick() { Tick::tick() => *child }; *holder.loan }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    assert!(
        flow.events.iter().any(
            |event| matches!(&event.kind, FlowEventKind::EndBorrow(owner) if owner == "child")
        ),
        "the aggregate reborrow was not released at its handler-join NLL frontier: {flow:#?}"
    );
}

#[test]
fn placeflow_preserves_enum_payload_reference_origins_across_handler_boundaries() {
    let core = core_for(
        "core-enum-reference-reborrow-handler@0.1.0",
        "pub enum Holder { Held(&mut i64), Empty } effect Tick { [0, 1] tick() -> i64; } pub fn main() -> i64 { let value = 1; let holder = Holder::Held(&mut value); handle holder is Holder::Held(parent) { true => { let child = & *(*parent); handle Tick::tick() { Tick::tick() => *child }; *(*parent) }; false => 0 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    assert!(
        flow.events
            .iter()
            .any(|event| matches!(&event.kind, FlowEventKind::Reborrow(root) if root == "value")),
        "enum payload reborrow did not retain its backing place: {flow:#?}"
    );
    assert!(
        flow.events.iter().any(
            |event| matches!(&event.kind, FlowEventKind::EndBorrow(owner) if owner == "child")
        ),
        "enum payload reborrow was not released after its handler use: {flow:#?}"
    );
}

#[test]
fn forged_array_reference_slots_keep_reborrow_and_escape_provenance() {
    let package = PackageKey("core-forged-array-reference-provenance@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let i64 = Type::Scalar(ScalarType::I64);
    let reference = Type::Reference {
        mutability: grandiose_stage0::Mutability::Unique,
        lifetime: Lifetime::Elided,
        referent: Box::new(i64.clone()),
    };
    let mut body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![
            CoreExpr {
                kind: CoreKind::Literal("1".into()),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Let {
                    name: "value".into(),
                    value: CoreId(0),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Local("value".into()),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Borrow {
                    unique: true,
                    value: CoreId(2),
                },
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Array(vec![CoreId(3)]),
                ty: Type::Array(Box::new(reference.clone())),
                span,
            },
            CoreExpr {
                kind: CoreKind::Let {
                    name: "holder".into(),
                    value: CoreId(4),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Local("holder".into()),
                ty: Type::Array(Box::new(reference.clone())),
                span,
            },
            CoreExpr {
                kind: CoreKind::Field {
                    base: CoreId(6),
                    index: 0,
                    field_count: 1,
                },
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Deref(CoreId(7)),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Borrow {
                    unique: true,
                    value: CoreId(8),
                },
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Let {
                    name: "child".into(),
                    value: CoreId(9),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Local("child".into()),
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Deref(CoreId(11)),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Block(vec![CoreId(1), CoreId(5), CoreId(10), CoreId(12)]),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Block(vec![CoreId(1), CoreId(4)]),
                ty: Type::Array(Box::new(reference)),
                span,
            },
        ],
        root: CoreId(13),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(body.validate().is_empty(), "{:#?}", body.validate());
    let flow = PlaceFlow::analyze(&body);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    assert!(
        flow.events
            .iter()
            .any(|event| matches!(&event.kind, FlowEventKind::Reborrow(root) if root == "value")),
        "array element did not retain its frozen backing loan: {flow:#?}"
    );

    // A separately rooted view simulates a decoded/frozen body that returns
    // the aggregate directly.  EscapeFlow must still see the body-local loan
    // even though the array layout itself is not a source-level record.
    body.root = CoreId(14);
    let escaped_flow = PlaceFlow::analyze(&body);
    let escapes = EscapeFlow::analyze(&body, &escaped_flow);
    assert!(
        escapes
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "forged array return lost its body-local reference provenance: {escapes:#?}"
    );
}

#[test]
fn forged_aggregate_reference_carrier_cannot_be_replaced_while_child_reborrow_is_live() {
    let package = PackageKey("core-forged-reborrow-carrier-replacement@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let i64 = Type::Scalar(ScalarType::I64);
    let reference = Type::Reference {
        mutability: grandiose_stage0::Mutability::Unique,
        lifetime: Lifetime::Elided,
        referent: Box::new(i64.clone()),
    };
    let array = Type::Array(Box::new(reference.clone()));
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![
            CoreExpr {
                kind: CoreKind::Literal("1".into()),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Let {
                    name: "first".into(),
                    value: CoreId(0),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Local("first".into()),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Borrow {
                    unique: true,
                    value: CoreId(2),
                },
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Array(vec![CoreId(3)]),
                ty: array.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Let {
                    name: "holder".into(),
                    value: CoreId(4),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Local("holder".into()),
                ty: array.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Field {
                    base: CoreId(6),
                    index: 0,
                    field_count: 1,
                },
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Deref(CoreId(7)),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Borrow {
                    unique: true,
                    value: CoreId(8),
                },
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Let {
                    name: "child".into(),
                    value: CoreId(9),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Literal("2".into()),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Let {
                    name: "second".into(),
                    value: CoreId(11),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Local("second".into()),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Borrow {
                    unique: true,
                    value: CoreId(13),
                },
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Assign {
                    place: CorePlace::Field {
                        base: Box::new(CorePlace::Local {
                            name: "holder".into(),
                            ty: array.clone(),
                        }),
                        index: 0,
                        field_count: 1,
                        ty: reference.clone(),
                    },
                    value: CoreId(14),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Local("child".into()),
                ty: reference.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Deref(CoreId(16)),
                ty: i64.clone(),
                span,
            },
            CoreExpr {
                kind: CoreKind::Block(vec![
                    CoreId(1),
                    CoreId(5),
                    CoreId(10),
                    CoreId(12),
                    CoreId(15),
                    CoreId(17),
                ]),
                ty: i64,
                span,
            },
        ],
        root: CoreId(18),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(body.validate().is_empty(), "{:#?}", body.validate());
    let flow = PlaceFlow::analyze(&body);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "forged aggregate-carrier replacement bypassed the reborrow check: {flow:#?}"
    );
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-reborrow-carrier-replacement")),
        &body,
        &flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6001"),
        "MIR accepted a forged replacement of a suspended reference carrier: {lowered:#?}"
    );
}

#[test]
fn handler_payload_reference_survives_completion_and_return_escape_checks() {
    let core = core_for(
        "core-handler-payload-reference-escape@0.1.0",
        "effect Relay { [0, 1] relay(value: &i64) -> &i64; } pub fn main() -> &i64 { let value = 1; handle Relay::relay(&value) { completed => completed, Relay::relay(payload) with _ => payload } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let escapes = EscapeFlow::analyze(&core, &flow);
    assert!(
        escapes
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "handler payload/completion hid a body-local reference: {escapes:#?}"
    );
}

#[test]
fn resumed_handler_reference_result_keeps_effect_payload_provenance() {
    let core = core_for(
        "core-handler-resumption-reference-provenance@0.1.0",
        "effect Relay { [1, 1] relay(value: &i64) -> &i64; } pub fn main() -> &i64 { let value = 1; handle Relay::relay(&value) { completed => completed, Relay::relay(payload) with resume => resume(payload) } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let escapes = EscapeFlow::analyze(&core, &flow);
    assert!(
        escapes
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "resumption result hid its effect payload reference: {escapes:#?}"
    );
    assert!(
        !escapes
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "resumption lost frozen reference provenance: {escapes:#?}"
    );
}

#[test]
fn rigid_lifetime_contracts_reject_short_borrows_at_return_assignment_and_aggregate_boundaries() {
    let returned = core_for(
        "core-return-outlives@0.1.0",
        "pub fn main<'a>() -> &'a i64 { let value = 1; &value }",
    );
    assert!(
        returned
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "{:#?}",
        returned.diagnostics
    );

    let assigned = core_for(
        "core-assignment-outlives@0.1.0",
        "pub fn main<'a>(slot: &'a i64) -> i64 { let value = 1; slot = &value; 0 }",
    );
    assert!(
        assigned
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "{:#?}",
        assigned.diagnostics
    );

    let aggregate = core_for(
        "core-aggregate-outlives@0.1.0",
        "pub fn main<'a>() -> (&'a i64, ) { let value = 1; (&value, ) }",
    );
    assert!(
        aggregate
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "{:#?}",
        aggregate.diagnostics
    );
}

#[test]
fn call_lifetime_contract_rejects_a_short_argument_for_static_reference() {
    let source = r#"
        pub fn needs_static(value: &'static i64) -> i64 { 0 }
        pub fn main() -> i64 { let value = 1; needs_static(&value) }
    "#;
    let core = core_for("core-call-static-outlives@0.1.0", source);
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn callable_reference_parameters_are_checked_contravariantly() {
    let accepted = core_for(
        "core-callable-reference-variance@0.1.0",
        r#"
            pub fn accepts_any(value: &i64) -> i64 { 0 }
            pub fn requires_static(callback: (&'static i64) -> i64) -> i64 { 0 }
            pub fn main() -> i64 { requires_static(accepts_any) }
        "#,
    );
    assert!(
        accepted.diagnostics.is_empty(),
        "{:#?}",
        accepted.diagnostics
    );

    let rejected = core_for(
        "core-callable-reference-variance-rejected@0.1.0",
        r#"
            pub fn accepts_static(value: &'static i64) -> i64 { 0 }
            pub fn requires_any(callback: (&i64) -> i64) -> i64 { 0 }
            pub fn main() -> i64 { requires_any(accepts_static) }
        "#,
    );
    assert!(
        rejected
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "{:#?}",
        rejected.diagnostics
    );
}

#[test]
fn higher_ranked_call_opens_its_bound_lifetime_without_leaking_it() {
    let valid = core_for(
        "core-hrtb-call@0.1.0",
        "pub fn main(callback: for<'a> (&'a i64) -> &'a i64) -> i64 { let value = 1; let loan = &value; callback(loan); 0 }",
    );
    assert!(valid.diagnostics.is_empty(), "{:#?}", valid.diagnostics);

    let escaping = core_for(
        "core-hrtb-escape@0.1.0",
        "pub fn main(callback: for<'a> () -> &'a i64) -> i64 { callback(); 0 }",
    );
    assert!(
        escaping
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5019"),
        "{:#?}",
        escaping.diagnostics
    );
}

#[test]
fn frozen_core_rejects_bound_lifetimes_that_escape_callable_binders() {
    let package = PackageKey("core-forged-hrtb-escape@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let escaped = Type::Reference {
        mutability: grandiose_stage0::Mutability::Shared,
        lifetime: Lifetime::Bound { depth: 0, index: 0 },
        referent: Box::new(Type::Scalar(ScalarType::I64)),
    };
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Literal("0".into()),
            ty: escaped,
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };

    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4184"),
        "a bound lifetime outside a callable binder passed frozen Core validation"
    );
    let flow = PlaceFlow::analyze(&body);
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-hrtb-bound-lifetime")),
        &body,
        &flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR accepted an escaped higher-ranked lifetime: {lowered:#?}"
    );

    let scoped = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![CoreExpr {
            kind: CoreKind::Literal("0".into()),
            ty: Type::Callable {
                safety: grandiose_stage0::Safety::Safe,
                lifetime_binders: 1,
                parameters: vec![Type::Reference {
                    mutability: grandiose_stage0::Mutability::Shared,
                    lifetime: Lifetime::Bound { depth: 0, index: 0 },
                    referent: Box::new(Type::Scalar(ScalarType::I64)),
                }],
                result: Box::new(Type::Reference {
                    mutability: grandiose_stage0::Mutability::Shared,
                    lifetime: Lifetime::Bound { depth: 0, index: 0 },
                    referent: Box::new(Type::Scalar(ScalarType::I64)),
                }),
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
            },
            span,
        }],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(
        !scoped
            .validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4184"),
        "a bound lifetime under its callable binder was rejected"
    );
}

#[test]
fn typed_closures_elaborate_stacked_higher_ranked_binders() {
    let core = core_for(
        "core-stacked-hrtb-closure@0.1.0",
        "pub fn main() -> i64 { let callback = (value: for<'a> for<'b> (&'a i64, &'b i64) -> &'a i64) -> i64 { 0 }; 0 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let closure = core
        .expressions
        .iter()
        .find(|expression| matches!(expression.kind, CoreKind::Closure { .. }))
        .expect("typed closure");
    let Type::Callable { parameters, .. } = &closure.ty else {
        panic!("expected outer typed closure")
    };
    assert!(matches!(
        parameters.as_slice(),
        [Type::Callable { safety: grandiose_stage0::Safety::Safe, lifetime_binders: 2, parameters, result, .. }]
            if matches!(parameters.as_slice(), [
                Type::Reference { lifetime: Lifetime::Bound { depth: 0, index: 0 }, .. },
                Type::Reference { lifetime: Lifetime::Bound { depth: 0, index: 1 }, .. },
            ]) && matches!(result.as_ref(), Type::Reference { lifetime: Lifetime::Bound { depth: 0, index: 0 }, .. })
    ));
}

#[test]
fn selected_trait_methods_share_the_call_lifetime_constraint_boundary() {
    let source = r#"
        trait Relay {
            fn relay<'a>(receiver: i64, value: &'a i64) -> &'a i64;
        }
        impl Relay for i64 {
            fn relay<'a>(receiver: i64, value: &'a i64) -> &'a i64 { value }
        }
        pub fn main() -> i64 {
            let value = 1;
            let loan = &value;
            Relay::relay(0, loan);
            0
        }
    "#;
    let core = core_for("core-trait-method-lifetime-call@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);

    let rejected = core_for(
        "core-trait-method-static-call@0.1.0",
        r#"
            trait StaticRelay { fn relay(receiver: i64, value: &'static i64) -> i64; }
            impl StaticRelay for i64 {
                fn relay(receiver: i64, value: &'static i64) -> i64 { 0 }
            }
            pub fn main() -> i64 { let value = 1; StaticRelay::relay(0, &value) }
        "#,
    );
    assert!(
        rejected
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "{:#?}",
        rejected.diagnostics
    );
}

#[test]
fn trait_method_generic_lifetime_relation_freezes_the_selected_payload_path() {
    let core = core_for(
        "core-trait-method-distinct-lifetime-relation@0.1.0",
        "trait First { fn first<'a, 'b>(receiver: i64, left: &'a i64, right: &'b i64) -> &'a i64; } impl First for i64 { fn first<'a, 'b>(receiver: i64, left: &'a i64, right: &'b i64) -> &'a i64 { left } } pub fn main() -> i64 { let left = 1; let right = 2; let forwarded = First::first(0, &left, &right); left = 3; *forwarded }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let paths = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Call {
                reference_origin: grandiose_stage0::CallReferenceOrigin::Paths(paths),
                ..
            } => Some(paths),
            _ => None,
        })
        .expect("trait method call did not retain its frozen relation");
    assert_eq!(paths[0].argument, 1);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        !flow
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5023"),
        "trait method generic relation became opaque: {flow:#?}"
    );
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5007"),
        "trait method result did not preserve the selected caller loan: {flow:#?}"
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
            } if effect_arguments == &[grandiose_stage0::GenericArgument::Type(grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::I64))]
        )
    ));
}

#[test]
fn closures_seal_distinct_owner_scoped_environment_brands() {
    let core = core_for(
        "core-callable-environment-brand@0.1.0",
        "pub fn main(value: i64) -> i64 { let first = (x: i64) -> i64 { value + x }; let second = (x: i64) -> i64 { value + x }; 0 }",
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
    assert_eq!(environments.len(), 2);
    assert!(environments.iter().all(|environment| environment.sealed));
    assert!(environments.iter().all(|environment| {
        environment.runs_in.sealed
            && environment.runs_in.environment == environment.brand
            && environment.runs_in.callable == environment.brand.callable
            && environment.runs_in.post_states == environment.post_states
    }));
    assert_eq!(environments[0].brand.owner, environments[1].brand.owner);
    assert_ne!(environments[0].brand, environments[1].brand);
    assert_eq!(environments[0].captures[0].name, "value");
    let flow = PlaceFlow::analyze(&core);
    let mir = MirLowering::lower(environments[0].brand.owner, &core, &flow)
        .function
        .expect("sealed closures lower to MIR");
    let brands = mir
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction {
            MirInstruction::MakeCallable {
                environment: Some(environment),
                ..
            } => Some(environment.brand),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        brands,
        environments
            .iter()
            .map(|environment| environment.brand)
            .collect::<Vec<_>>()
    );
}

#[test]
fn typed_core_rejects_replayed_capture_environment_brand() {
    let package = PackageKey("core-replayed-environment@0.1.0".into());
    let span = Span {
        file: FileKey::new(&package, "src/main.glorious"),
        start: 0,
        end: 1,
    };
    let body = TypedBody {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_scopes: Default::default(),
        unsafe_implementations: Default::default(),
        parameters: vec![],
        expressions: vec![
            CoreExpr {
                kind: CoreKind::Closure {
                    callable: CallableId(1),
                    parameters: vec![],
                    environment: CaptureEnvironment {
                        brand: EnvironmentBrand {
                            owner: grandiose_stage0::DefKey(grandiose_stage0::Digest::of_bytes(
                                b"foreign-owner",
                            )),
                            callable: CallableId(0),
                        },
                        captures: vec![],
                        post_states: vec![],
                        runs_in: RunsInEvidence {
                            environment: EnvironmentBrand {
                                owner: grandiose_stage0::DefKey(
                                    grandiose_stage0::Digest::of_bytes(b"foreign-owner"),
                                ),
                                callable: CallableId(0),
                            },
                            callable: CallableId(0),
                            effects: EffectRow::empty(),
                            post_states: vec![],
                            sealed: true,
                        },
                        sealed: true,
                    },
                    body: CoreId(1),
                },
                ty: Type::Unit,
                span,
            },
            CoreExpr {
                kind: CoreKind::Literal("0".into()),
                ty: Type::Scalar(grandiose_stage0::ScalarType::I64),
                span,
            },
        ],
        root: CoreId(0),
        diagnostics: vec![],
        recovered: false,
    };
    assert!(
        body.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4183")
    );
}

#[test]
fn capture_environments_seal_and_validate_mode_derived_post_states() {
    let mut core = core_for(
        "core-capture-post-state@0.1.0",
        "pub fn main() -> i64 { let value = 42; let read = () -> i64 { value }; read() }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let valid_flow = PlaceFlow::analyze(&core);
    assert!(valid_flow.diagnostics.is_empty(), "{valid_flow:#?}");
    let environment = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Closure { environment, .. } => Some(environment),
            _ => None,
        })
        .expect("closure environment");
    assert_eq!(environment.captures.len(), 1);
    assert_eq!(environment.post_states.len(), 1);
    assert_eq!(
        environment.captures[0].name,
        environment.post_states[0].name
    );
    assert_eq!(
        environment.captures[0].mode,
        environment.post_states[0].mode
    );

    environment.post_states[0].mode = CaptureMode::Move;
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4183"),
        "forged capture post-state passed Typed Core validation"
    );
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5020"),
        "PlaceFlow accepted a forged capture post-state: {flow:#?}"
    );
    let lowered = MirLowering::lower(
        DefKey(Digest::of_bytes(b"forged-capture-post-state")),
        &core,
        &valid_flow,
    );
    assert!(
        lowered.function.is_none()
            && lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G6000"),
        "MIR accepted a forged capture post-state: {lowered:#?}"
    );
}

#[test]
fn typed_core_rejects_runs_in_evidence_with_a_forged_effect_contract() {
    let mut core = core_for(
        "core-runs-in-effect-contract@0.1.0",
        "effect Log { note(); } pub fn main() -> i64 { let action = () -> i64 / {Log} { Log::note(); 0 }; 0 }",
    );
    let environment = core
        .expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Closure { environment, .. } => Some(environment),
            _ => None,
        })
        .expect("effectful closure environment");
    assert!(!environment.runs_in.effects.effects.is_empty());
    environment.runs_in.effects = EffectRow::empty();
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4183"),
        "forged RunsIn effect evidence passed Typed Core validation"
    );
    let flow = PlaceFlow::analyze(&core);
    let escape = EscapeFlow::analyze(&core, &flow);
    assert!(
        escape
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5014"),
        "escape checking trusted forged RunsIn evidence: {escape:#?}"
    );
}

#[test]
fn partial_move_inside_a_closure_copies_a_duplicable_aggregate_capture_root() {
    let mut core = core_for(
        "core-partial-move-capture@0.1.0",
        "pub struct Pair { value: i64, other: i64 } pub fn main(pair: Pair) -> i64 { let read = () -> i64 { let value = move pair.value; value }; read() }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    {
        let environment = core
            .expressions
            .iter_mut()
            .find_map(|expression| match &mut expression.kind {
                CoreKind::Closure { environment, .. } => Some(environment),
                _ => None,
            })
            .expect("closure environment");
        assert_eq!(environment.captures.len(), 1);
        assert_eq!(environment.captures[0].name, "pair");
        assert_eq!(environment.captures[0].mode, CaptureMode::Copy);
        assert_eq!(environment.post_states[0].mode, CaptureMode::Copy);
    }
    assert!(core.validate().is_empty(), "{:#?}", core.validate());
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");

    // The capture root and its post-state form one frozen ownership
    // contract. A forged shared post-state would leave the aggregate usable
    // after a closure can consume one of its fields.
    core.expressions
        .iter_mut()
        .find_map(|expression| match &mut expression.kind {
            CoreKind::Closure { environment, .. } => Some(environment),
            _ => None,
        })
        .expect("closure environment")
        .post_states[0]
        .mode = CaptureMode::SharedBorrow;
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4183"),
        "forged partial-move capture state passed Typed Core validation"
    );
    assert!(
        PlaceFlow::analyze(&core)
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5020"),
        "PlaceFlow accepted a forged partial-move capture state"
    );
}

#[test]
fn escapeflow_fails_closed_on_a_forged_nested_aggregate_projection_path() {
    let mut core = core_for(
        "core-forged-nested-aggregate-path@0.1.0",
        r#"
            pub struct Inner { value: &i64 }
            pub struct Outer { inner: Inner, tag: i64 }
            pub fn main() -> i64 {
                let outer = Outer { inner: Inner { value: &0 }, tag: 0 };
                let first = 1;
                outer.inner.value = &first;
                let second = 2;
                outer.inner.value = &second;
                0
            }
        "#,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let assignment = core
        .expressions
        .iter_mut()
        .filter_map(|expression| match &mut expression.kind {
            CoreKind::Assign { place, .. } => Some(place),
            _ => None,
        })
        .nth(1)
        .expect("second nested assignment");
    let CorePlace::Field { field_count, .. } = assignment else {
        panic!("nested assignment must retain a field place")
    };
    *field_count = 2;
    let escapes = EscapeFlow::analyze(&core, &flow);
    assert!(
        escapes
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5021"),
        "forged nested field layout lost provenance without a diagnostic: {escapes:#?}"
    );
}

#[test]
fn handler_clauses_and_resumptions_receive_distinct_callable_brands() {
    let core = core_for(
        "core-handler-callable-brand@0.1.0",
        "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => k(7) } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let clauses = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Handle { clauses, .. } => Some(clauses),
            _ => None,
        })
        .expect("handler Core node");
    let clause = &clauses[0];
    assert!(matches!(clause.brand, CallableBrand::HandlerClause { .. }));
    assert!(matches!(
        clause
            .continuation
            .as_ref()
            .map(|continuation| continuation.brand),
        Some(CallableBrand::Continuation { .. })
    ));
}

#[test]
fn is_pattern_tests_publish_sealed_scoped_refinement_facts() {
    let core = core_for(
        "core-refinement-environment@0.1.0",
        "pub fn main(value: i64) -> bool { value is bound }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let refinement = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::PatternTest { refinement, .. } => Some(refinement),
            _ => None,
        })
        .expect("pattern test Core node");
    assert!(refinement.sealed);
    assert_eq!(refinement.subject.as_deref(), Some("value"));
    assert_eq!(refinement.bindings, ["bound"]);
    let flow = PlaceFlow::analyze(&core);
    assert_eq!(flow.refinements.len(), 1);
    assert_eq!(flow.refinements[0].brand, refinement.brand);
    assert_eq!(flow.refinements[0].bindings, ["bound"]);
}

#[test]
fn positive_is_completion_arm_opens_nominal_refinement_bindings() {
    let core = core_for(
        "core-is-nominal-refinement-branch@0.1.0",
        "pub enum Result { Ok(i64), Err } pub fn main(value: Result) -> i64 { handle value is Result::Ok(found) { true => found; false => 0 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let clauses = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Completion { clauses, .. } => Some(clauses),
            _ => None,
        })
        .expect("completion branch over the is test");
    assert!(clauses[0].refinement.is_some());
    assert_eq!(
        clauses[0].bindings,
        [("found".into(), Type::Scalar(ScalarType::I64))]
    );
    assert!(clauses[1].refinement.is_none());
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert!(
        !flow.final_states.contains_key("found"),
        "branch-local refinement binder escaped its post-state join: {flow:#?}"
    );
}

#[test]
fn negative_is_completion_arm_cannot_observe_positive_refinement_bindings() {
    let core = core_for(
        "core-is-refinement-negative-scope@0.1.0",
        "pub enum Result { Ok(i64), Err } pub fn main(value: Result) -> i64 { handle value is Result::Ok(found) { true => found; false => found } }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4104"),
        "negative refinement branch unexpectedly resolved a positive-only binder: {:#?}",
        core.diagnostics
    );
}

#[test]
fn is_refinement_binders_cannot_shadow_incoming_post_state_names() {
    let core = core_for(
        "core-is-refinement-post-state-shadow@0.1.0",
        "pub enum Result { Ok(i64), Err } pub fn main(value: Result) -> i64 { let found = 7; handle value is Result::Ok(found) { true => found; false => 0 } }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4170"),
        "ambiguous refinement post-state shadowing was accepted: {:#?}",
        core.diagnostics
    );
}

#[test]
fn is_refinement_binders_cannot_escape_in_nested_closures() {
    let core = core_for(
        "core-is-refinement-closure-escape@0.1.0",
        "pub enum Result { Ok(i64), Err } pub fn main(value: Result) -> i64 { handle value is Result::Ok(found) { true => { let delayed = (ignored: i64) -> i64 { found }; 0 }; false => 0 } }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4171"),
        "refinement binder unexpectedly escaped in a closure: {:#?}",
        core.diagnostics
    );
}

#[test]
fn labels_mint_owner_scoped_brands_and_erase_when_no_transfer_is_taken() {
    let core = core_for(
        "core-label-brand@0.1.0",
        "pub fn main() -> i64 { label done { 42 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let brand = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand),
            _ => None,
        })
        .expect("label Core node");
    let flow = PlaceFlow::analyze(&core);
    let mir = MirLowering::lower(brand.owner, &core, &flow);
    assert!(mir.diagnostics.is_empty(), "{:#?}", mir.diagnostics);
}

#[test]
fn transfers_are_scoped_and_lower_to_a_verified_nonlocal_mir_edge() {
    let core = core_for(
        "core-label-transfer@0.1.0",
        "pub fn main() -> i64 { label done { transfer done 42; 0 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| {
        matches!(expression.kind, CoreKind::Transfer { .. }) && expression.ty == Type::Never
    }));
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("label Core node");
    let lowered = MirLowering::lower(owner, &core, &flow);
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "direct lexical transfer lowers to MIR: {:#?}",
            lowered.diagnostics
        )
    });
    assert!(matches!(
        &mir.blocks[0].terminator,
        grandiose_stage0::MirTerminator::Leave { cleanup, .. }
            if cleanup.moved_places.is_empty() && cleanup.active_loans.is_empty()
    ));
    let artifact = grandiose_stage0::emit_vm(&mir).expect("emit label edge");
    let verified = grandiose_stage0::verify_vm(artifact).expect("verify label edge");
    assert_eq!(verified.run_i64().expect("run label edge"), 42);
}

#[test]
fn closures_cannot_capture_an_enclosing_label_transfer_target() {
    let core = core_for(
        "core-label-transfer-closure-escape@0.1.0",
        "pub fn main() -> i64 { label done { let delayed = (value: i64) -> i64 { transfer done value }; 0 } }",
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4179"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn nested_labels_can_transfer_to_an_enclosing_brand_through_the_vm_edge() {
    let core = core_for(
        "core-nested-label-transfer@0.1.0",
        "pub fn main() -> i64 { label outer { label inner { transfer outer 42; 0 }; 1 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("outer label");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("nested transfer lowers");
    let verified =
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).expect("emit nested transfer"))
            .expect("verify nested transfer");
    assert_eq!(verified.run_i64().expect("run nested transfer"), 42);
}

#[test]
fn bound_label_transfer_rejoins_its_source_continuation_before_vm_execution() {
    let core = core_for(
        "core-bound-label-transfer@0.1.0",
        "pub fn main() -> i64 { let answer = label done { transfer done 40; 0 }; answer + 2 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("bound label transfer lowers");
    assert!(matches!(
        mir.blocks[0].terminator,
        grandiose_stage0::MirTerminator::Leave { .. }
    ));
    assert!(
        mir.blocks[1]
            .instructions
            .iter()
            .any(|instruction| matches!(
                instruction,
                grandiose_stage0::MirInstruction::AddI64 { .. }
            ))
    );
    let verified = grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap()).unwrap();
    assert_eq!(verified.run_i64().unwrap(), 42);
}

#[test]
fn label_transfer_used_as_a_binary_operand_rejoins_through_typed_mir() {
    let core = core_for(
        "core-operand-label-transfer@0.1.0",
        "pub fn main() -> i64 { label done { transfer done 40; 0 } + 2 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("operand transfer lowers without G6012");
    assert!(mir.blocks.len() >= 2);
    assert!(matches!(
        mir.blocks[0].terminator,
        grandiose_stage0::MirTerminator::Leave { .. }
    ));
    assert_eq!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn binary_operand_transfer_emits_a_cleanup_carrying_leave_edge() {
    let core = core_for(
        "core-binary-label-transfer@0.1.0",
        "pub fn main() -> i64 { label done { 1 + transfer done 42 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("strict binary transfer lowers");
    assert!(matches!(
        &mir.blocks[0].terminator,
        grandiose_stage0::MirTerminator::Leave { cleanup, .. }
            if cleanup.moved_places == flow.moved_places
                && cleanup.active_loans == flow.active_loans
    ));
    assert!(matches!(
        mir.blocks[0].instructions.as_slice(),
        [
            grandiose_stage0::MirInstruction::ConstI64 { value: 1, .. },
            ..
        ]
    ));
    assert_eq!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn lazy_label_transfer_uses_a_boolean_join_for_the_skipped_branch() {
    let core = core_for(
        "core-lazy-label-transfer@0.1.0",
        "pub fn main() -> Bool { label done { false or transfer done true } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("lazy label transfer lowers");
    assert!(matches!(
        &mir.blocks[0].terminator,
        grandiose_stage0::MirTerminator::SwitchBool {
            then_target,
            then_arguments,
            else_target,
            else_arguments,
            ..
        } if *then_target == grandiose_stage0::MirBlockId(2)
            && then_arguments.len() == 1
            && *else_target == grandiose_stage0::MirBlockId(1)
            && else_arguments.is_empty()
    ));
    assert!(matches!(
        &mir.blocks[1].terminator,
        grandiose_stage0::MirTerminator::Leave { target, cleanup, .. }
            if *target == grandiose_stage0::MirBlockId(2)
                && cleanup.moved_places == flow.moved_places
                && cleanup.active_loans == flow.active_loans
    ));
    assert_eq!(mir.blocks[2].parameters.len(), 1);
    assert!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_bool()
            .unwrap()
    );
}

#[test]
fn nested_completion_label_transfer_keeps_ordered_normal_and_leave_edges() {
    let core = core_for(
        "core-nested-completion-label-transfer@0.1.0",
        "pub fn main() -> i64 { label done { 1 + handle 40 { 40 => transfer done 42, _ => 0 } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("nested completion label transfer lowers");
    assert!(mir.blocks.iter().any(|block| matches!(
        &block.terminator,
        grandiose_stage0::MirTerminator::Leave { target, cleanup, .. }
            if *target == grandiose_stage0::MirBlockId(1)
                && cleanup.moved_places == flow.moved_places
                && cleanup.active_loans == flow.active_loans
    )));
    assert!(mir.blocks.iter().any(|block| matches!(
        &block.terminator,
        grandiose_stage0::MirTerminator::Goto { target, arguments }
            if *target == grandiose_stage0::MirBlockId(1) && arguments.len() == 1
    )));
    assert_eq!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn label_operand_transfer_preserves_preceding_left_to_right_computation() {
    let core = core_for(
        "core-operand-label-prefix@0.1.0",
        "pub fn main() -> i64 { 1 + label done { transfer done 40; 0 } + 1 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("operand transfer preserves prefix");
    assert!(matches!(
        mir.blocks[0].instructions.as_slice(),
        [
            grandiose_stage0::MirInstruction::ConstI64 { value: 1, .. },
            ..
        ]
    ));
    assert_eq!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn inner_label_transfer_rejoins_its_enclosing_label_expression() {
    let core = core_for(
        "core-inner-label-transfer@0.1.0",
        "pub fn main() -> i64 { label outer { label inner { transfer inner 40; 0 } + 2 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("outer label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("inner transfer lowers through enclosing label");
    assert!(matches!(
        mir.blocks[0].terminator,
        grandiose_stage0::MirTerminator::Leave { .. }
    ));
    assert_eq!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn nested_label_transfer_preserves_cleanup_and_the_outer_continuation() {
    let core = core_for(
        "core-nested-bound-label-cleanup@0.1.0",
        "pub fn main() -> i64 { let value = 1; let answer = label outer { label inner { move value; transfer outer 40; 0 }; 1 }; answer + 2 }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let outer = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } if brand.label == 0 => Some(brand),
            _ => None,
        })
        .expect("outer label brand");
    let mir = MirLowering::lower(outer.owner, &core, &flow)
        .function
        .expect("nested bound transfer lowers");
    let grandiose_stage0::MirTerminator::Leave { brand, cleanup, .. } = &mir.blocks[0].terminator
    else {
        panic!("nested transfer must lower to Leave")
    };
    assert_eq!(*brand, outer);
    assert_eq!(cleanup.moved_places, flow.moved_places);
    assert_eq!(cleanup.active_loans, flow.active_loans);
    let artifact = grandiose_stage0::emit_vm(&mir).expect("emit nested cleanup leave");
    assert!(
        artifact
            .function
            .instructions
            .iter()
            .any(|instruction| matches!(
                instruction,
                grandiose_stage0::VmInstruction::Leave { cleanup, .. } if cleanup.validate()
            ))
    );
    assert_eq!(
        grandiose_stage0::verify_vm(artifact)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn leave_edges_carry_canonical_placeflow_cleanup_evidence() {
    let core = core_for(
        "core-label-cleanup-plan@0.1.0",
        "pub fn main() -> i64 { let value = 1; label done { move value; transfer done 42; 0 } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let brand = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand),
            _ => None,
        })
        .expect("label");
    let mir = MirLowering::lower(brand.owner, &core, &flow)
        .function
        .expect("cleanup leave lowers");
    let grandiose_stage0::MirTerminator::Leave {
        brand: leave_brand,
        cleanup,
        ..
    } = &mir.blocks[0].terminator
    else {
        panic!("label transfer must use a Leave terminator")
    };
    assert_eq!(*leave_brand, brand);
    assert_eq!(cleanup.moved_places, flow.moved_places);
    assert_eq!(cleanup.active_loans, flow.active_loans);
    grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).expect("emit leave"))
        .expect("verify proof-erased cleanup leave");
}

#[test]
fn handler_clause_label_transfer_preserves_brand_cleanup_and_vm_frame_exit() {
    let core = core_for(
        "core-handler-label-transfer@0.1.0",
        "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { label done { handle Ask::ask() { Ask::ask() => transfer done 42 } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("outer label owner");
    let lowered = MirLowering::lower(owner, &core, &flow);
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "handler clause transfer lowers through Leave: {:#?}",
            lowered.diagnostics
        )
    });
    assert!(matches!(
        mir.blocks[2].terminator,
        grandiose_stage0::MirTerminator::Leave { .. }
    ));
    let artifact = grandiose_stage0::emit_vm(&mir).expect("emit handler leave");
    assert!(
        artifact
            .function
            .instructions
            .iter()
            .any(|instruction| matches!(
                instruction,
                grandiose_stage0::VmInstruction::Leave { .. }
            ))
    );
    assert_eq!(
        grandiose_stage0::verify_vm(artifact)
            .expect("verify frame-aware leave")
            .run_i64()
            .expect("run frame-aware leave"),
        42
    );
}

#[test]
fn frozen_mir_move_paths_preserve_shadowed_bindings_and_cleanup_identity() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let value = Pair { left: 1, right: 2 }; { let value = Pair { left: 3, right: 4 }; move value.left; 0 }; label done { move value.left; transfer done 42; 0 } }";
    let (core, signatures) =
        core_and_signatures_for("core-frozen-mir-shadowed-move-paths@0.1.0", source);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    assert_eq!(
        flow.bindings
            .iter()
            .filter(|binding| binding.spelling == "value")
            .count(),
        2
    );
    assert_eq!(flow.final_move_paths.len(), flow.moved_places.len());
    for (&path, fact) in flow.final_move_paths.iter().zip(&flow.moved_places) {
        let mut fields = Vec::new();
        let mut cursor = Some(path);
        let mut binding = None;
        while let Some(current) = cursor {
            let node = &flow.move_paths[current.0 as usize];
            binding.get_or_insert(node.binding);
            assert_eq!(binding, Some(node.binding));
            if let Some(field) = node.field {
                fields.push(field);
            }
            cursor = node.parent;
        }
        fields.reverse();
        assert_eq!(fields, fact.fields);
        assert_eq!(
            flow.bindings[binding.expect("move binding").0 as usize].spelling,
            fact.root
        );
    }
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("label owner");
    let mut mir = MirLowering::lower_with_bodies_and_signatures(
        owner,
        &core,
        &flow,
        &BTreeMap::new(),
        Some(&signatures),
    )
        .function
        .expect("shadowed cleanup lowers");
    let grandiose_stage0::MirTerminator::Leave { cleanup, .. } = &mir.blocks[0].terminator else {
        panic!("label transfer must retain cleanup")
    };
    assert_eq!(cleanup.moved_paths.len(), cleanup.moved_places.len());
    let cleanup_path = cleanup.moved_paths[0];
    let node = &mir.control.move_paths.paths[cleanup_path.0 as usize];
    let binding = &mir.control.move_paths.bindings[node.binding.0 as usize];
    assert_eq!(
        binding.source,
        flow.move_paths[flow.final_move_paths[0].0 as usize].binding
    );
    assert_eq!(binding.spelling, "value");
    assert!(
        node.parent.is_some(),
        "a field move must retain its root parent"
    );
    assert!(mir.validate().is_ok());
    assert_eq!(
        compile_with_destruction(source, &mir)
            .run_i64()
            .expect("shadowed cleanup result"),
        42
    );

    let root_path = mir
        .control
        .move_paths
        .paths
        .iter()
        .position(|path| path.parent.is_none())
        .expect("move-path root");
    let mut forged_root = mir.clone();
    forged_root.control.move_paths.paths[root_path].field = Some(0);
    assert!(
        forged_root
            .validate()
            .is_err_and(|error| error.contains("root with a field")),
        "a forged root must not gain a projection field"
    );

    let mut forged_parent = mir.clone();
    forged_parent.control.move_paths.paths[cleanup_path.0 as usize].parent = Some(cleanup_path);
    assert!(
        forged_parent
            .validate()
            .is_err_and(|error| error.contains("non-ancestral parent")),
        "a move path must not form a cycle"
    );

    let mut forged_binding = mir.clone();
    forged_binding.control.move_paths.paths[cleanup_path.0 as usize].binding =
        grandiose_stage0::MirPlaceBindingId(u32::MAX);
    assert!(
        forged_binding
            .validate()
            .is_err_and(|error| error.contains("absent binding")),
        "a move path must not target an absent binding"
    );

    let mut forged_provenance = mir.clone();
    forged_provenance.control.move_paths.bindings[0].source =
        grandiose_stage0::PlaceBindingId(u32::MAX);
    assert!(
        forged_provenance
            .validate()
            .is_err_and(|error| error.contains("non-dense PlaceFlow source")),
        "binding provenance must retain its dense source identity"
    );

    let mut mismatched_cleanup = mir.clone();
    let grandiose_stage0::MirTerminator::Leave { cleanup, .. } =
        &mut mismatched_cleanup.blocks[0].terminator
    else {
        unreachable!()
    };
    cleanup.moved_paths[0] = node.parent.expect("field path parent");
    assert!(
        mismatched_cleanup
            .validate()
            .is_err_and(|error| error.contains("disagrees with its legacy fields")),
        "cleanup paths must pair one-to-one with their legacy move facts"
    );

    let grandiose_stage0::MirTerminator::Leave { cleanup, .. } = &mut mir.blocks[0].terminator
    else {
        unreachable!()
    };
    cleanup.moved_paths[0] = grandiose_stage0::MirMovePathId(u32::MAX);
    assert!(
        mir.validate()
            .is_err_and(|error| error.contains("absent move path")),
        "stale typed cleanup identities must be rejected"
    );
}

/// This is the source-side counterpart to the hostile-MIR storage contracts.
/// A real body must run through a handler, move one aggregate projection,
/// retain the disjoint projection, and leave the
/// surrounding lexical label with a computed payload. It deliberately drives
/// the ordinary source/Core/PlaceFlow/MIR/VM path rather than constructing an
/// artificial MIR body.
#[test]
fn source_lowering_executes_handler_partial_move_and_label_leave() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64; }
        pub struct Pair { left: i64, right: i64 }
        pub fn main() -> i64 {
            label done {
                let pair = Pair { left: 1, right: 2 };
                move pair.left;
                handle Ask::ask() {
                    Ask::ask() => transfer done pair.right + 40
                }
            }
        }
    "#;
    let (core, signatures) =
        core_and_signatures_for("core-source-storage-handler-capture-label@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    assert!(
        flow.events.iter().any(|event| matches!(
            (&event.kind, &event.place),
            (FlowEventKind::Move(root), Some(place))
                if root == "pair" && place.root == "pair" && place.fields == vec![0]
        )),
        "the label/handler path must retain the moved aggregate projection: {flow:#?}"
    );
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("source label owner");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        owner,
        &core,
        &flow,
        &BTreeMap::new(),
        Some(&signatures),
    );
    let mir = lowered
        .function
        .unwrap_or_else(|| panic!("source body must lower: {:#?}", lowered.diagnostics));
    mir.validate()
        .unwrap_or_else(|error| panic!("source-produced MIR must validate: {error}\n{mir:#?}"));
    assert!(
        mir.blocks
            .iter()
            .any(|block| matches!(block.terminator, grandiose_stage0::MirTerminator::Leave { .. })),
        "the source label transfer must remain a MIR Leave: {mir:#?}"
    );
    assert_eq!(
        compile_with_destruction(source, &mir)
            .run_i64()
            .expect("source-produced VM must execute"),
        42
    );
}

#[test]
fn source_lowering_preserves_branch_correlated_drop_flags_across_handler_label_cleanup() {
    // Both dynamically selected handler arms partially move a distinct field,
    // reinitialize that aggregate, and leave the same label.  The lexical
    // prefix also keeps two other aggregate owners live.  Frozen MIR must
    // carry every owner through the label cleanup plan without confusing the
    // branch-correlated old field move with the reinitialized aggregate.
    let source = r#"
        effect Ask { [1, 1] ask(value: Bool) -> i64; }
        struct Pair { left: i64, right: i64 }
        pub fn main() -> i64 {
            label done {
                let first = Pair { left: 10, right: 11 };
                let pair = Pair { left: 3, right: 7 };
                let last = Pair { left: 8, right: 25 };
                handle Ask::ask(true) {
                    Ask::ask(true) => {
                        let moved = move pair.left;
                        pair = Pair { left: 4, right: 5 };
                        transfer done first.left + moved + pair.left + last.right
                    },
                    Ask::ask(false) => {
                        let moved = move pair.right;
                        pair = Pair { left: 6, right: 7 };
                        transfer done first.left + moved + pair.left + last.right
                    },
                    Ask::ask(_) => transfer done first.left + pair.left + last.right,
                }
            }
        }
    "#;
    let (core, signatures) =
        core_and_signatures_for("core-handler-label-branch-drop-flags@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("source label owner");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        owner,
        &core,
        &flow,
        &BTreeMap::new(),
        Some(&signatures),
    );
    let mir = lowered
        .function
        .unwrap_or_else(|| panic!("combined cleanup source must lower: {:#?}", lowered.diagnostics));
    mir.validate()
        .unwrap_or_else(|error| panic!("combined cleanup MIR must validate: {error}\n{mir:#?}"));
    let leaves = mir
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            grandiose_stage0::MirTerminator::Leave { cleanup, .. } => Some(cleanup),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(leaves.len(), 3, "one leave per handler arm: {mir:#?}");
    assert!(leaves.iter().all(|cleanup| cleanup.drop_flags.len() >= 3));
    assert!(
        mir.blocks.iter().flat_map(|block| &block.instructions).any(|instruction| {
            matches!(instruction, MirInstruction::DestroyIf { .. })
        }),
        "reinitialization must retain branch-safe conditional destruction: {mir:#?}"
    );
    let verified = compile_with_destruction(source, &mir);
    assert_eq!(
        verified
            .run_i64()
            .unwrap_or_else(|error| panic!("combined cleanup VM must execute: {error:#?}\n{verified:#?}")),
        42
    );
}

#[test]
fn source_lowering_drops_protected_custom_aggregate_once_after_forwarded_cancellation() {
    // The inner refutable arm forwards `ask(1)` while Probe remains owned by
    // the enclosing handled computation.  The outer `[0,1]` arm cancels that
    // continuation, so this source shape needs one Drop call on the outer
    // cancellation edge and must never duplicate it at the rejoin.
    let source = r#"
        effect Ask { [0, 1] ask(value: i64) -> i64; }
        struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0, 1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> {
            drop(&mut self) -> { *self.target = *self.target + 1; }
        }
        pub fn main() -> i64 {
            let count = 41;
            let result = handle {
                let probe = Probe { target: &mut count };
                handle Ask::ask(1) { Ask::ask(0, _) => 0 }
            } {
                Ask::ask(_, _) => 0,
            };
            count + result
        }
    "#;
    let package = PackageKey("core-forwarded-cancellation-drop@0.1.0".into());
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
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        definition.key,
        &core,
        &flow,
        &std::collections::BTreeMap::new(),
        Some(&signatures),
    );
    let mir = lowered
        .function
        .unwrap_or_else(|| panic!("forwarded cancellation must lower: {:#?}", lowered.diagnostics));
    mir.validate()
        .unwrap_or_else(|error| panic!("forwarded cancellation MIR must validate: {error}\n{mir:#?}"));
    assert!(
        mir.blocks.iter().any(|block| {
            block
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, MirInstruction::Forward { .. }))
        }),
        "the refutable inner arm must retain its real forwarding edge: {mir:#?}"
    );
    let outer_cancellation = mir
        .control
        .handlers
        .first()
        .expect("outer handler control entry")
        .target;
    let outer_drop_intents = mir.blocks[outer_cancellation.0 as usize]
        .instructions
        .iter()
        .filter(|instruction| matches!(instruction, MirInstruction::Drop { local }
            if matches!(mir.locals[local.0 as usize].ty, Type::Nominal { .. })))
        .count();
    assert_eq!(
        outer_drop_intents, 1,
        "the forwarded outer-cancellation path must retain exactly one Probe destruction boundary: {mir:#?}"
    );
    assert_eq!(compile_with_destruction(source, &mir).run_i64().unwrap(), 42);
}

#[test]
fn nested_handler_leave_preserves_the_outer_label_destination_contract() {
    let core = core_for(
        "core-nested-handler-label-contract@0.1.0",
        "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { label outer { label inner { handle Ask::ask() { Ask::ask() => transfer outer 42 } } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let outer = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } if brand.label == 0 => Some(brand),
            _ => None,
        })
        .expect("outer label brand");
    let lowered = MirLowering::lower(outer.owner, &core, &flow);
    let mir = lowered
        .function
        .unwrap_or_else(|| panic!("nested handler transfer lowers: {:#?}", lowered.diagnostics));
    assert!(matches!(
        mir.blocks[2].terminator,
        grandiose_stage0::MirTerminator::Leave { brand, .. } if brand == outer
    ));
    assert_eq!(
        grandiose_stage0::verify_vm(
            grandiose_stage0::emit_vm(&mir).expect("emit nested handler leave")
        )
        .expect("verify nested handler leave")
        .run_i64()
        .expect("run nested handler leave"),
        42
    );
}

#[test]
fn nested_generic_label_forward_rejoins_completion_after_refutable_handler() {
    let source = r#"
        escape<L>(destination: L, value: i64) -> !
        where L: Label<i64>
        {
            destination(value)
        }
        effect Ask { [1, 1] ask(value: i64) -> i64; }
        pub main() -> i64 {
            handle {
                @outer: i64 {
                    @inner: i64 {
                        handle {
                            handle Ask::ask(1) {
                                Ask::ask(0) with k => k(0),
                            }
                        } {
                            Ask::ask(value) => escape(@inner, value + 41),
                        }
                    }
                }
            } {
                value => value + 100,
            }
        }
    "#;
    let core = core_for("core-nested-generic-label-forward-completion@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } if brand.label == 0 => Some(brand.owner),
            _ => None,
        })
        .expect("outer label owner");
    let lowered = MirLowering::lower(owner, &core, &flow);
    let mir = lowered
        .function
        .unwrap_or_else(|| panic!("nested generic label forwarding lowers: {:#?}", lowered.diagnostics));
    mir.validate()
        .unwrap_or_else(|error| panic!("nested generic label MIR validates: {error}\n{mir:#?}"));
    let entry = &mir.blocks[0].instructions;
    let token = entry
        .iter()
        .position(|instruction| matches!(instruction, MirInstruction::MakeLabel { .. }))
        .expect("the lexical token is materialized before handlers");
    let handler = entry
        .iter()
        .position(|instruction| matches!(instruction, MirInstruction::InstallHandler { .. }))
        .expect("the forwarded path installs handlers");
    assert!(token < handler, "label token must predate handler depth capture: {mir:#?}");
    assert!(mir.blocks.iter().any(|block| block
        .instructions
        .iter()
        .any(|instruction| matches!(instruction, MirInstruction::Forward { .. }))),
        "refutable inner arm must retain Forward: {mir:#?}");
    let artifact = grandiose_stage0::emit_vm(&mir).expect("MIR emits VM");
    let verified = grandiose_stage0::decode_and_verify_artifact(
        &grandiose_stage0::encode_artifact(&artifact),
    )
    .expect("encoded dynamic-label forwarding VM verifies");
    assert!(matches!(
        verified.run_i64(),
        Err(grandiose_stage0::VmArtifactError::CallRequiresProgram)
    ));
}

#[test]
fn nested_generic_label_forward_checks_each_refutable_payload_before_rejoin() {
    let source = r#"
        escape<L>(destination: L, value: i64) -> !
        where L: Label<i64>
        {
            destination(value)
        }
        effect Ask { [1, 1] ask(flag: Bool, value: i64) -> i64; }
        pub main() -> i64 {
            handle {
                @outer: i64 {
                    @inner: i64 {
                        handle {
                            handle Ask::ask(true, 1) {
                                Ask::ask(true, 0) with k => k(0),
                            }
                        } {
                            Ask::ask(flag, value) => escape(@inner, value + 41),
                        }
                    }
                }
            } {
                value => value + 100,
            }
        }
    "#;
    let core = core_for("core-nested-generic-label-multi-payload@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } if brand.label == 0 => Some(brand.owner),
            _ => None,
        })
        .expect("outer label owner");
    let lowered = MirLowering::lower(owner, &core, &flow);
    let mir = lowered
        .function
        .unwrap_or_else(|| panic!("multi-payload forwarding lowers: {:#?}", lowered.diagnostics));
    mir.validate()
        .unwrap_or_else(|error| panic!("multi-payload forwarding MIR validates: {error}\n{mir:#?}"));
    let pattern_blocks = mir
        .blocks
        .iter()
        .filter(|block| block
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::PatternTest { .. })))
        .count();
    assert_eq!(pattern_blocks, 2, "both payload positions need ordered CFG tests: {mir:#?}");
    assert!(mir.blocks.iter().any(|block| block
        .instructions
        .iter()
        .any(|instruction| matches!(instruction, MirInstruction::Forward { .. }))));
    let artifact = grandiose_stage0::emit_vm(&mir).expect("MIR emits VM");
    let verified = grandiose_stage0::decode_and_verify_artifact(
        &grandiose_stage0::encode_artifact(&artifact),
    )
    .expect("multi-payload forwarding bytecode verifies");
    assert!(matches!(
        verified.run_i64(),
        Err(grandiose_stage0::VmArtifactError::CallRequiresProgram)
    ));
}

#[test]
fn nested_generic_label_forward_cancellation_cleans_before_completion_rejoin() {
    let source = r#"
        escape<L>(destination: L, value: i64) -> !
        where L: Label<i64>
        {
            destination(value)
        }
        effect Ask { [0, 1] ask(flag: Bool, value: i64) -> i64; }
        struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0, 1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> {
            drop(&mut self) -> { *self.target = *self.target + 1; }
        }
        pub main() -> i64 {
            let count = 40;
            handle {
                @outer: i64 {
                    @inner: i64 {
                        let probe = Probe { target: &mut count };
                        handle {
                            handle Ask::ask(true, 1) {
                                Ask::ask(true, 0) with k => k(0),
                            }
                        } {
                            Ask::ask(flag, value) with _ => escape(@inner, value + 41),
                        }
                    }
                }
            } {
                value => count + value + 100,
            }
        }
    "#;
    let package = PackageKey("core-nested-generic-label-forward-cleanup@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        definition.key,
        &core,
        &flow,
        &std::collections::BTreeMap::new(),
        Some(&signatures),
    );
    let mir = lowered
        .function
        .unwrap_or_else(|| panic!("cleanup forwarding lowers: {:#?}", lowered.diagnostics));
    mir.validate()
        .unwrap_or_else(|error| panic!("cleanup forwarding MIR validates: {error}\n{mir:#?}"));
    assert_eq!(
        mir.blocks[1]
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, MirInstruction::Drop { local }
                if matches!(mir.locals[local.0 as usize].ty, Type::Nominal { .. })))
            .count(),
        1,
        "the dynamic rejoin must retain one Probe destruction boundary before completion: {mir:#?}"
    );
    assert_eq!(compile_with_destruction(source, &mir).run_i64().unwrap(), 183);
}

#[test]
fn nested_generic_label_replay_forward_rejoins_completion_with_single_cleanup() {
    let source = r#"
        escape<L>(destination: L, value: i64) -> !
        where L: Label<i64>
        {
            destination(value)
        }
        effect Ask { [2, 2] ask(flag: Bool, value: i64) -> i64; }
        struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0, 1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> {
            drop(&mut self) -> { *self.target = *self.target + 1; }
        }
        pub main() -> i64 {
            let count = 40;
            handle {
                @outer: i64 {
                    @inner: i64 {
                        let probe = Probe { target: &mut count };
                        handle {
                            handle Ask::ask(true, 1) {
                                Ask::ask(true, 0) with k => {
                                    let first = k(0);
                                    let second = k(0);
                                    escape(@inner, first + second)
                                },
                            }
                        } {
                            Ask::ask(flag, value) with k => {
                                let first = k(10);
                                let second = k(20);
                                escape(@inner, value + first + second + 41)
                            },
                        }
                    }
                }
            } {
                value => count + value + 100,
            }
        }
    "#;
    let package = PackageKey("core-replay-forward-label-cleanup@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        definition.key,
        &core,
        &flow,
        &std::collections::BTreeMap::new(),
        Some(&signatures),
    );
    let mir = lowered.function.unwrap();
    mir.validate()
        .unwrap_or_else(|error| panic!("replayed forwarding MIR validates: {error}\n{mir:#?}"));
    assert_eq!(
        mir.blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter(|instruction| matches!(instruction, MirInstruction::InstallHandler {
                continuation: grandiose_stage0::MirContinuationPolicy::Replay { uses: 2 },
                ..
            }))
            .count(),
        2,
        "both forwarded handler frames retain the exact replay budget: {mir:#?}"
    );
    assert_eq!(
        mir.blocks
            .iter()
            .filter(|block| block.instructions.iter().any(|instruction| matches!(instruction, MirInstruction::PatternTest { .. })))
            .count(),
        2,
        "a late multi-payload refutation must retain both ordered tests: {mir:#?}"
    );
    assert!(mir.blocks.iter().any(|block| block
        .instructions
        .iter()
        .any(|instruction| matches!(instruction, MirInstruction::Forward { .. }))));
    assert_eq!(
        mir.blocks[1]
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, MirInstruction::Drop { local }
                if matches!(mir.locals[local.0 as usize].ty, Type::Nominal { .. })))
            .count(),
        1,
        "the generic-label rejoin retains one Probe destruction boundary before completion: {mir:#?}"
    );
    assert_eq!(compile_with_destruction(source, &mir).run_i64().unwrap(), 213);
}

#[test]
fn interprocedural_replay_forwards_after_a_late_payload_then_cancels() {
    // The first inner payload pattern accepts `true`, while the second
    // refutes `1`. The decision graph must test both payloads before it
    // forwards to the outer exact replayer; each replayed residual then
    // reaches the sibling cancellation clause.
    let source = r#"
        effect Console {
            [2, 2] read(flag: Bool, value: i64) -> i64;
            [0, 1] write(value: i64) -> i64;
        }
        pub fn relay(flag: Bool, value: i64) -> i64 / Console {
            let read = Console::read(flag, value);
            Console::write(read)
        }
        pub fn main() -> i64 {
            handle {
                handle relay(true, 1) {
                    Console::read(true, 0) with k => k(1) + k(2);
                    Console::write(_) with _ => 40;
                }
            } {
                Console::read(_, _) with k => k(20) + k(21);
            }
        }
    "#;
    let package = PackageKey("core-late-payload-replay-cancellation@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        definition.key,
        &core,
        &flow,
        &std::collections::BTreeMap::new(),
        Some(&signatures),
    );
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "late-payload replay/cancellation must lower: {:#?}",
            lowered.diagnostics
        )
    });
    mir.validate().unwrap_or_else(|error| {
        panic!("late-payload replay/cancellation MIR validates: {error}\n{mir:#?}")
    });
    assert_eq!(
        mir.blocks
            .iter()
            .filter(|block| block.instructions.iter().any(|instruction| matches!(
                instruction,
                MirInstruction::PatternTest { .. }
            )))
            .count(),
        2,
        "both refutable payload positions must have ordered MIR tests: {mir:#?}"
    );
    assert_eq!(
        mir.blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter(|instruction| matches!(
                instruction,
                MirInstruction::InstallHandler {
                    continuation: grandiose_stage0::MirContinuationPolicy::Replay { uses: 2 },
                    ..
                }
            ))
            .count(),
        2,
        "the inner and outer frames must retain exact replay budgets: {mir:#?}"
    );
    assert!(mir.blocks.iter().any(|block| block
        .instructions
        .iter()
        .any(|instruction| matches!(instruction, MirInstruction::Forward { .. }))));
    assert!(mir.blocks.iter().any(|block| block
        .instructions
        .iter()
        .any(|instruction| matches!(instruction, MirInstruction::Cancel { .. }))));
    let artifact = grandiose_stage0::emit_vm(&mir).expect("late-payload MIR emits VM");
    grandiose_stage0::decode_and_verify_artifact(&grandiose_stage0::encode_artifact(&artifact))
        .expect("late-payload replay/cancellation VM bytecode verifies");
}

#[test]
fn deep_replay_cancellation_checks_all_three_payloads_in_both_partial_rows() {
    let source = r#"
        effect Console {
            [2, 2] read(flag: Bool, middle: i64, final: i64) -> i64;
            [0, 1] write(value: i64) -> i64;
        }
        pub fn relay(flag: Bool, middle: i64, final: i64) -> i64 / Console {
            let read = Console::read(flag, middle, final);
            Console::write(read)
        }
        pub fn main() -> i64 {
            handle {
                handle {
                    handle relay(true, 1, 2) {
                        Console::read(true, 1, 0) with k => k(1) + k(2);
                        Console::write(_) with _ => 40;
                    }
                } {
                    Console::read(true, 1, 0) with k => k(3) + k(4);
                }
            } {
                value => value + 1;
                Console::read(_, _, _) with k => k(20) + k(21);
            }
        }
    "#;
    let package = PackageKey("core-deep-third-payload-cancellation@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        definition.key,
        &core,
        &flow,
        &std::collections::BTreeMap::new(),
        Some(&signatures),
    );
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "deep third-payload replay/cancellation must lower: {:#?}",
            lowered.diagnostics
        )
    });
    mir.validate().unwrap_or_else(|error| {
        panic!("deep third-payload replay/cancellation MIR validates: {error}\n{mir:#?}")
    });
    assert_eq!(
        mir.blocks
            .iter()
            .filter(|block| block.instructions.iter().any(|instruction| matches!(
                instruction,
                MirInstruction::PatternTest { .. }
            )))
            .count(),
        6,
        "both partial rows must retain an ordered test for each payload: {mir:#?}"
    );
    assert_eq!(
        mir.blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter(|instruction| matches!(instruction, MirInstruction::Forward { .. }))
            .count(),
        2,
        "both partial rows must preserve independent forwarding edges: {mir:#?}"
    );
    assert!(mir.blocks.iter().any(|block| block
        .instructions
        .iter()
        .any(|instruction| matches!(instruction, MirInstruction::Cancel { .. }))));
    let artifact = grandiose_stage0::emit_vm(&mir).expect("deep third-payload MIR emits VM");
    grandiose_stage0::decode_and_verify_artifact(&grandiose_stage0::encode_artifact(&artifact))
        .expect("deep third-payload cancellation VM bytecode verifies");
}

#[test]
fn reentrant_replay_checks_a_late_third_payload_before_labelled_completion() {
    let source = r#"
        effect Ask { [2, 2] ask(flag: Bool, middle: i64, final: i64) -> i64; }
        effect Tick { [2, 2] tick() -> i64; }
        effect Audit { [2, 2] note(value: i64) -> i64; }
        pub fn relay() -> i64 / {Ask, Tick} {
            let tick = Tick::tick();
            let asked = Ask::ask(true, 1, 2);
            tick + asked
        }
        pub fn audit(value: i64) -> i64 / Audit { Audit::note(value) }
        pub fn main() -> i64 {
            handle {
                handle {
                    label done {
                        handle {
                            handle {
                                handle {
                                    handle relay() {
                                        Ask::ask(true, 1, 0) with k => k(1) + k(2)
                                    }
                                } {
                                    value => value + 1;
                                    Tick::tick() with k => k(10) + k(20)
                                }
                            } {
                                Ask::ask(_, _, _) with k => k(30) + k(40)
                            }
                        } {
                            value => transfer done value
                        }
                    }
                } {
                    value => { let audited = audit(value); audited + 100 }
                }
            } {
                Audit::note(_) with k => k(1) + k(2)
            }
        }
    "#;
    let package = PackageKey("core-third-payload-reentrant-label@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        definition.key,
        &core,
        &flow,
        &std::collections::BTreeMap::new(),
        Some(&signatures),
    );
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "third-payload reentrant labelled completion must lower: {:#?}",
            lowered.diagnostics
        )
    });
    mir.validate().unwrap_or_else(|error| {
        panic!("third-payload reentrant MIR validates: {error}\n{mir:#?}")
    });
    assert_eq!(
        mir.blocks
            .iter()
            .filter(|block| block.instructions.iter().any(|instruction| matches!(
                instruction,
                MirInstruction::PatternTest { .. }
            )))
            .count(),
        3,
        "the partial Ask row must retain an ordered test for all three payloads: {mir:#?}"
    );
    assert!(mir.blocks.iter().any(|block| block
        .instructions
        .iter()
        .any(|instruction| matches!(instruction, MirInstruction::Forward { .. }))));
    assert!(mir.blocks.iter().any(|block| matches!(
        block.terminator,
        grandiose_stage0::MirTerminator::Leave { .. }
    )));
    assert_eq!(
        mir.blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter(|instruction| matches!(
                instruction,
                MirInstruction::InstallHandler {
                    continuation: grandiose_stage0::MirContinuationPolicy::Replay { uses: 2 },
                    ..
                }
            ))
            .count(),
        4,
        "Ask, Tick, and retained Audit replay frames must remain distinct: {mir:#?}"
    );
    compile_with_destruction(source, &mir);
}

#[test]
fn direct_completion_clause_label_transfer_runs_after_handler_uninstall() {
    let core = core_for(
        "core-completion-label-transfer@0.1.0",
        "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { label done { handle Ask::ask() { value => transfer done value, Ask::ask() => 42 } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("outer label owner");
    let lowered = MirLowering::lower(owner, &core, &flow);
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "completion transfer lowers through Leave: {:#?}",
            lowered.diagnostics
        )
    });
    assert!(
        mir.blocks[0]
            .instructions
            .iter()
            .any(|instruction| matches!(
                instruction,
                grandiose_stage0::MirInstruction::UninstallHandler
            ))
    );
    assert!(matches!(
        mir.blocks[1].terminator,
        grandiose_stage0::MirTerminator::Leave { .. }
    ));
    let artifact = grandiose_stage0::emit_vm(&mir).expect("emit completion leave");
    assert_eq!(
        grandiose_stage0::verify_vm(artifact)
            .expect("verify completion leave")
            .run_i64()
            .expect("run completion leave"),
        42
    );
}

#[test]
fn projected_terminal_contract_rejoins_nested_completion_through_a_label() {
    let source = "effect Stop<T> { stop(value: T) -> !; } trait Capability { type Effects: EffectRow; } impl Capability for i64 { type Effects = {Stop<i64>}; } pub fn leaf(value: i64) -> ! / { <i64 as Capability>::Effects } { Stop<i64>::stop(value) } pub fn main() -> i64 { label done { handle { handle leaf(42) { Stop<i64>::stop(value) => value } } { value => transfer done value } } }";
    let package = PackageKey("core-projected-terminal-completion-label@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let index = DefinitionIndex::from_interface(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(definition, &body, &index, &signatures);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let effects = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Call { callee, .. } => match &core.expression(callee).ty {
                Type::Callable { effects, .. } => Some(effects),
                _ => None,
            },
            _ => None,
        })
        .expect("the terminal helper call has a callable effect contract");
    assert!(
        effects.projections.is_empty() && effects.effects.len() == 1,
        "the concrete associated effect-row contract must normalize before MIR: {effects:#?}"
    );
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("label owner");
    let leaf = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("leaf"))
        .expect("leaf definition");
    let leaf_body = BodySyntax::parse(&lexed, source, leaf.body.expect("leaf body"));
    let leaf_core = TypedBody::elaborate(leaf, &leaf_body, &index, &signatures);
    assert!(leaf_core.diagnostics.is_empty(), "{:#?}", leaf_core.diagnostics);
    let mut bodies = BTreeMap::new();
    bodies.insert(leaf.key, leaf_core);
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        owner,
        &core,
        &flow,
        &bodies,
        Some(&signatures),
    );
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "projected terminal completion/label must lower: {:#?}",
            lowered.diagnostics
        )
    });
    mir.validate().unwrap_or_else(|error| {
        panic!("projected terminal completion/label MIR validates: {error}\n{mir:#?}")
    });
    assert!(mir.blocks.iter().any(|block| matches!(
        block.terminator,
        grandiose_stage0::MirTerminator::Leave { .. }
    )));
    let artifact = grandiose_stage0::emit_vm(&mir).expect("projected terminal label MIR emits VM");
    assert_eq!(
        grandiose_stage0::verify_vm(artifact)
            .expect("projected terminal label VM verifies")
            .run_i64()
            .expect("projected terminal label VM runs"),
        42
    );
}

#[test]
fn refutable_completion_label_transfer_has_explicit_match_and_fallback_cfg() {
    let core = core_for(
        "core-refutable-completion-label-transfer@0.1.0",
        "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { label done { handle Ask::ask() { 41 => transfer done 100, value => value, Ask::ask() => 41 } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("outer label owner");
    let lowered = MirLowering::lower(owner, &core, &flow);
    let mir = lowered.function.unwrap_or_else(|| {
        panic!(
            "refutable completion transfer lowers through CFG: {:#?}",
            lowered.diagnostics
        )
    });
    assert!(matches!(
        mir.blocks[1].terminator,
        grandiose_stage0::MirTerminator::SwitchBool { .. }
    ));
    assert!(matches!(
        mir.blocks[2].terminator,
        grandiose_stage0::MirTerminator::Leave { .. }
    ));
    assert!(matches!(
        mir.blocks[3].terminator,
        grandiose_stage0::MirTerminator::Return { .. }
    ));
    assert_eq!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        100
    );
}

#[test]
fn refutable_completion_label_transfer_preserves_unmatched_fallback() {
    let core = core_for(
        "core-refutable-completion-fallback@0.1.0",
        "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { label done { handle Ask::ask() { 41 => transfer done 100, value => value, Ask::ask() => 42 } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("outer label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("refutable completion fallback lowers");
    assert_eq!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn ordered_refutable_completion_transfers_chain_through_each_test() {
    let core = core_for(
        "core-ordered-completion-label-transfer@0.1.0",
        "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { label done { handle Ask::ask() { 1 => transfer done 101, 41 => transfer done 141, value => value, Ask::ask() => 41 } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("outer label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("ordered completion chain lowers");
    assert!(matches!(
        mir.blocks[1].terminator,
        grandiose_stage0::MirTerminator::SwitchBool {
            else_target: grandiose_stage0::MirBlockId(2),
            ..
        }
    ));
    assert!(matches!(
        mir.blocks[2].terminator,
        grandiose_stage0::MirTerminator::SwitchBool { .. }
    ));
    let grandiose_stage0::MirTerminator::Leave { brand, cleanup, .. } = &mir.blocks[3].terminator
    else {
        panic!("first matched completion arm must leave the enclosing label")
    };
    assert_eq!(brand.owner, owner);
    assert_eq!(cleanup.moved_places, flow.moved_places);
    assert_eq!(cleanup.active_loans, flow.active_loans);
    assert!(matches!(
        mir.blocks[4].terminator,
        grandiose_stage0::MirTerminator::Leave { .. }
    ));
    assert!(matches!(
        mir.blocks[5].terminator,
        grandiose_stage0::MirTerminator::Return { .. }
    ));
    assert_eq!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        141
    );
}

#[test]
fn ordered_refutable_completion_preserves_first_match_and_final_fallback() {
    for (package, source, expected) in [
        (
            "core-ordered-completion-first-match@0.1.0",
            "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { label done { handle Ask::ask() { 1 => transfer done 101, 41 => transfer done 141, value => value, Ask::ask() => 1 } } }",
            101,
        ),
        (
            "core-ordered-completion-final-fallback@0.1.0",
            "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { label done { handle Ask::ask() { 1 => transfer done 101, 41 => transfer done 141, value => value, Ask::ask() => 42 } } }",
            42,
        ),
    ] {
        let core = core_for(package, source);
        assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
        let flow = PlaceFlow::analyze(&core);
        let owner = core
            .expressions
            .iter()
            .find_map(|expression| match expression.kind {
                CoreKind::Label { brand, .. } => Some(brand.owner),
                _ => None,
            })
            .expect("outer label owner");
        let mir = MirLowering::lower(owner, &core, &flow)
            .function
            .expect("ordered completion source lowers");
        assert_eq!(
            grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
                .unwrap()
                .run_i64()
                .unwrap(),
            expected
        );
    }
}

#[test]
fn ordered_completion_fallback_transfer_leaves_after_all_tests_fail() {
    let core = core_for(
        "core-ordered-completion-fallback-transfer@0.1.0",
        "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { label done { handle Ask::ask() { 1 => 1, value => transfer done value, Ask::ask() => 42 } } }",
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let owner = core
        .expressions
        .iter()
        .find_map(|expression| match expression.kind {
            CoreKind::Label { brand, .. } => Some(brand.owner),
            _ => None,
        })
        .expect("outer label owner");
    let mir = MirLowering::lower(owner, &core, &flow)
        .function
        .expect("fallback transfer chain lowers");
    assert!(
        mir.blocks[0]
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::UninstallHandler))
    );
    assert!(matches!(
        mir.blocks[1].terminator,
        grandiose_stage0::MirTerminator::SwitchBool {
            else_target: grandiose_stage0::MirBlockId(3),
            ..
        }
    ));
    assert!(matches!(
        mir.blocks[2].terminator,
        grandiose_stage0::MirTerminator::Return { .. }
    ));
    let grandiose_stage0::MirTerminator::Leave { brand, cleanup, .. } = &mir.blocks[3].terminator
    else {
        panic!("final fallback must leave the enclosing label")
    };
    assert_eq!(brand.owner, owner);
    assert_eq!(cleanup.moved_places, flow.moved_places);
    assert_eq!(cleanup.active_loans, flow.active_loans);
    assert_eq!(
        grandiose_stage0::verify_vm(grandiose_stage0::emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}
