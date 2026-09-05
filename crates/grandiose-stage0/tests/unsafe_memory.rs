//! Raw-memory language contracts, independently of the Rust storage substrate.
//! Executable unsafe and VM/native ABI cases belong here as those layers land.

use std::collections::BTreeMap;

use grandiose_stage0::{
    BodySyntax, CoherenceSet, DeclarationScan, DefinitionIndex, ElaboratedHeader,
    ElaboratedInterface, ElaboratedTraitReference, EscapeFlow, FileKey, GenericArgument,
    InferContext, InterfaceSet, LexedFile, Lifetime, MirLowering, Mutability, PackageInterface,
    PackageKey, PlaceFlow, PointerMutability, Quantity, ScalarType, TraitAnswer, TraitGoal,
    TraitSolver, Type, TypeError, TypedBody, UseFlow,
};

fn pointer(mutability: PointerMutability, pointee: Type) -> Type {
    Type::RawPointer {
        mutability,
        pointee: Box::new(pointee),
    }
}

fn collect(source: &str) -> (LexedFile, PackageInterface, ElaboratedInterface) {
    let package = PackageKey("unsafe-memory@0.1.0".into());
    let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let collected = InterfaceSet::collect(package, "crate", &lexed, source, &scan);
    assert!(collected.diagnostics.is_empty(), "{collected:#?}");
    let signatures = ElaboratedInterface::elaborate(&collected.interface);
    assert!(signatures.diagnostics.is_empty(), "{signatures:#?}");
    (lexed, collected.interface, signatures)
}

fn elaborate_main(source: &str) -> (TypedBody, ElaboratedInterface) {
    let (lexed, interface, signatures) = collect(source);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let syntax = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    assert!(syntax.diagnostics.is_empty(), "{syntax:#?}");
    let core = TypedBody::elaborate(
        definition,
        &syntax,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    (core, signatures)
}

fn assert_valid_core(core: &TypedBody, signatures: &ElaboratedInterface) {
    assert!(core.diagnostics.is_empty(), "{core:#?}");
    assert!(!core.recovered, "{core:#?}");
    assert!(core.validate().is_empty(), "{:?}", core.validate());
    let flow = PlaceFlow::analyze_with_interface(core, signatures);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let uses = UseFlow::analyze_with_interface(core, &flow, signatures);
    assert!(uses.diagnostics.is_empty(), "{uses:#?}");
    let escapes = EscapeFlow::analyze(core, &flow);
    assert!(escapes.diagnostics.is_empty(), "{escapes:#?}");
}

#[test]
fn unsafe_callables_preserve_alias_generic_and_higher_ranked_contracts() {
    let (_, interface, signatures) = collect(
        "type Callback<T> = for<'a> unsafe (&'a T) -> &'a T; pub unsafe fn keep<'a, T>(x: &'a T) -> &'a T { x } fn main() -> Callback<i64> { keep }",
    );
    let keep = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("keep"))
        .unwrap();
    assert_eq!(
        keep.callable_header().unwrap().safety,
        grandiose_stage0::Safety::Unsafe
    );
    let instantiated = signatures
        .instantiate_callable_generic(
            keep.key,
            &[
                GenericArgument::Lifetime(Lifetime::Static),
                GenericArgument::Type(Type::Scalar(ScalarType::I64)),
            ],
        )
        .unwrap();
    assert_eq!(instantiated.safety, grandiose_stage0::Safety::Unsafe);
    let (core, _) = elaborate_main(
        "type Callback = for<'a> unsafe (&'a i64) -> &'a i64; unsafe fn keep<'a>(x: &'a i64) -> &'a i64 { x } fn main() -> Callback { keep }",
    );
    assert!(core.diagnostics.is_empty(), "{core:#?}");
    assert!(matches!(
        core.expression(core.root).ty,
        Type::Callable {
            safety: grandiose_stage0::Safety::Unsafe,
            lifetime_binders: 1,
            ..
        }
    ));
}

#[test]
fn unsafe_calls_require_explicit_scopes_even_inside_unsafe_functions() {
    for source in [
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { dangerous() }",
        "unsafe fn dangerous() -> i64 { 42 } unsafe fn main() -> i64 { dangerous() }",
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { unsafe { dangerous() }; dangerous() }",
        "fn main(callback: unsafe () -> i64) -> i64 { callback() }",
    ] {
        let (core, _) = elaborate_main(source);
        assert!(
            core.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G4201"),
            "unsafe call accepted: {source}\n{core:#?}"
        );
    }
    for source in [
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { unsafe { dangerous() } }",
        "unsafe fn dangerous() -> i64 { 42 } unsafe fn main() -> i64 { unsafe { dangerous() } }",
        "fn main(callback: unsafe () -> i64) -> i64 { unsafe { callback() } }",
        "fn main(callback: unsafe fn(i64) -> i64) -> i64 { unsafe { callback(42) } }",
    ] {
        let (core, signatures) = elaborate_main(source);
        assert_valid_core(&core, &signatures);
        assert!(!core.unsafe_scopes.is_empty());
    }
}

#[test]
fn unsafe_permission_is_not_captured_by_deferred_callable_or_handler_bodies() {
    for source in [
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { unsafe { let f = () -> i64 { dangerous() }; f() } }",
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { unsafe { let f = { x => dangerous() + x }; f(0) } }",
        "unsafe fn dangerous() -> i64 { 42 } fn run(f: () -> i64) -> i64 { f() } fn main() -> i64 { unsafe { run() { dangerous() } } }",
        "effect Ask { ask() -> i64; } unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { unsafe { handle Ask::ask() { Ask::ask() => dangerous() } } }",
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { unsafe { handle 0 { value => dangerous() } } }",
    ] {
        let (core, _) = elaborate_main(source);
        assert!(
            core.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G4201"),
            "ambient unsafe leaked: {source}\n{core:#?}"
        );
    }
    let (core, signatures) = elaborate_main(
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { unsafe { let f = () -> i64 { unsafe { dangerous() } }; f() } }",
    );
    assert_valid_core(&core, &signatures);
}

#[test]
fn unsafe_callable_cannot_be_relabelled_as_safe_by_aliases_or_fn_evidence() {
    for source in [
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> () -> i64 { dangerous }",
        "type Safe = () -> i64; type Unsafe = unsafe () -> i64; fn main(f: Unsafe) -> Safe { f }",
        "unsafe fn dangerous() -> i64 { 42 } fn run(f: () -> i64) -> i64 { f() } fn main() -> i64 { run(dangerous) }",
        "unsafe fn dangerous() -> i64 { 42 } fn run<F>(f: F) -> i64 where F: Fn<(), Output = i64> { f() } fn main() -> i64 { run(dangerous) }",
    ] {
        let (core, _) = elaborate_main(source);
        assert!(
            !core.diagnostics.is_empty(),
            "unsafe contract erased: {source}\n{core:#?}"
        );
    }
    let mut safe = Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Scalar(ScalarType::I64)),
        effects: grandiose_stage0::EffectRow::empty(),
        invocation: Quantity::ONCE,
    };
    let safe_fingerprint = InferContext::default()
        .type_fingerprint(safe.clone())
        .unwrap();
    let unsafe_callable = {
        let Type::Callable { safety, .. } = &mut safe else {
            unreachable!()
        };
        *safety = grandiose_stage0::Safety::Unsafe;
        safe.clone()
    };
    assert_ne!(
        safe_fingerprint,
        InferContext::default()
            .type_fingerprint(unsafe_callable.clone())
            .unwrap()
    );
    let relation = ElaboratedTraitReference {
        definition: grandiose_stage0::intrinsic_callable_trait_definition(),
        arguments: vec![GenericArgument::Type(Type::Unit)],
    };
    let (_, _, signatures) = collect("fn main() {}");
    let goal = TraitGoal {
        subject: unsafe_callable,
        relation,
    };
    let mut solver = TraitSolver::new(&signatures);
    assert_eq!(solver.solve(goal.clone()), TraitAnswer::NoSolution);
    assert_eq!(
        solver.solve_with_assumptions(goal.clone(), &[goal]),
        TraitAnswer::NoSolution
    );
}

#[test]
fn frozen_core_rechecks_unsafe_scope_paths_and_rejects_erased_scopes() {
    let (mut core, signatures) = elaborate_main(
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { unsafe { dangerous() } }",
    );
    assert_valid_core(&core, &signatures);
    let fingerprint = core.semantic_fingerprint();
    core.unsafe_scopes.clear();
    assert_ne!(fingerprint, core.semantic_fingerprint());
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4202")
    );
    core.unsafe_scopes
        .insert(grandiose_stage0::CoreId(u32::MAX));
    assert!(
        core.validate()
            .iter()
            .any(|diagnostic| diagnostic.message.contains("existing lexical block"))
    );

    let (mut closure, signatures) = elaborate_main(
        "unsafe fn dangerous() -> i64 { 42 } fn main() -> i64 { unsafe { let f = () -> i64 { unsafe { dangerous() } }; f() } }",
    );
    assert_valid_core(&closure, &signatures);
    let outer = closure.unsafe_scopes.iter().copied().max().unwrap();
    closure.unsafe_scopes.retain(|scope| *scope == outer);
    assert!(
        closure
            .validate()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4202"),
        "outer scope authorized deferred body"
    );
}

#[test]
fn unsafe_trait_implementations_and_method_contracts_require_exact_qualifiers() {
    let (_, _, signatures) = collect(
        "unsafe trait Stable { unsafe fn read(x: i64) -> i64; } unsafe impl Stable for i64 { unsafe fn read(x: i64) -> i64 { x } } impl !Stable for u8 {}",
    );
    assert!(signatures.definitions.values().any(|header| matches!(header, ElaboratedHeader::Trait(header) if header.safety == grandiose_stage0::Safety::Unsafe)));
    for source in [
        "unsafe trait Stable {} impl Stable for i64 {}",
        "trait Stable {} unsafe impl Stable for i64 {}",
        "unsafe trait Stable {} unsafe impl !Stable for i64 {}",
        "trait Stable { fn read(x: i64) -> i64; } impl Stable for i64 { unsafe fn read(x: i64) -> i64 { x } }",
        "trait Stable { unsafe fn read(x: i64) -> i64; } impl Stable for i64 { fn read(x: i64) -> i64 { x } }",
    ] {
        let package = PackageKey("unsafe-trait@0.1.0".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
        let scan = DeclarationScan::scan(&lexed, source);
        assert!(scan.diagnostics.is_empty(), "{scan:#?}");
        let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan);
        assert!(interface.diagnostics.is_empty(), "{interface:#?}");
        let signatures = ElaboratedInterface::elaborate(&interface.interface);
        assert!(
            signatures
                .diagnostics
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, "G4203" | "G4147")),
            "unsafe implementation accepted: {source}\n{signatures:#?}"
        );
    }
}

#[test]
fn mir_and_vm_keep_call_safety_separate_from_unsafe_implementation() {
    for (source, safety, unsafe_execution) in [
        (
            "unsafe fn main() -> i64 { 42 }",
            grandiose_stage0::Safety::Unsafe,
            false,
        ),
        (
            "fn main() -> i64 { unsafe { 42 } }",
            grandiose_stage0::Safety::Safe,
            true,
        ),
        (
            "unsafe fn main() -> i64 { unsafe { 42 } }",
            grandiose_stage0::Safety::Unsafe,
            true,
        ),
    ] {
        let (core, signatures) = elaborate_main(source);
        assert_valid_core(&core, &signatures);
        assert_eq!(core.safety, safety);
        let definition = *signatures.definitions.keys().next().unwrap();
        let flow = PlaceFlow::analyze(&core);
        let lowered = MirLowering::lower(definition, &core, &flow);
        assert!(lowered.diagnostics.is_empty(), "{lowered:#?}");
        let function = lowered.function.unwrap();
        assert_eq!(function.safety, safety);
        assert_eq!(function.unsafe_execution, unsafe_execution);
        let artifact = grandiose_stage0::vm_backend::emit(&function).unwrap();
        assert_eq!(artifact.function.safety, safety);
        assert_eq!(artifact.function.unsafe_execution, unsafe_execution);
        let verified = grandiose_stage0::verify_vm(artifact).unwrap();
        assert!(matches!(verified.run_i64(), Err(grandiose_stage0::VmArtifactError::UnsafeExecutionRequiresUnsafeApi)));
        // SAFETY: these complete source fixtures only return the constant 42.
        assert_eq!(unsafe { verified.run_i64_with_unsafe(grandiose_stage0::VmExecutionLimits::default()) }.unwrap(), 42);
    }
}

#[test]
fn unsafe_scopes_do_not_disable_effect_or_ownership_checks() {
    let (effects, _) = elaborate_main(
        "effect IO { act() -> i64; } unsafe fn dangerous() -> i64 / IO { 42 } fn main() -> i64 { unsafe { dangerous() } }",
    );
    assert!(
        !effects.diagnostics.is_empty(),
        "unsafe block erased an outward effect"
    );
    assert!(
        !effects
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4201")
    );
    let (linear, signatures) = elaborate_main(
        "struct Linear {} impl Use<[1,1]> for Linear {} fn main(x: Linear) -> (Linear, Linear) { unsafe { (x, x) } }",
    );
    assert!(linear.diagnostics.is_empty(), "{linear:#?}");
    let flow = PlaceFlow::analyze_with_interface(&linear, &signatures);
    let uses = UseFlow::analyze_with_interface(&linear, &flow, &signatures);
    assert!(
        !flow.diagnostics.is_empty() || !uses.diagnostics.is_empty(),
        "unsafe block duplicated an exactly-linear owner\n{flow:#?}\n{uses:#?}"
    );
    let (borrow, _) = elaborate_main("fn main() -> &i64 { unsafe { let x = 1; &x } }");
    let flow = PlaceFlow::analyze(&borrow);
    let escapes = EscapeFlow::analyze(&borrow, &flow);
    assert!(
        !borrow.diagnostics.is_empty() || !escapes.diagnostics.is_empty(),
        "unsafe block extended a local safe reference lifetime"
    );
}

#[test]
fn unsafe_trait_contract_does_not_make_safe_methods_unsafe_or_vice_versa() {
    let (safe_method, signatures) = elaborate_main(
        "unsafe trait Stable { fn read(x: i64) -> i64; } unsafe impl Stable for i64 { fn read(x: i64) -> i64 { x } } fn main() -> i64 { Stable::read(42) }",
    );
    assert_valid_core(&safe_method, &signatures);
    assert_eq!(safe_method.unsafe_implementations.len(), 1);
    let main_key = {
        let (_, interface, _) = collect(
            "unsafe trait Stable { fn read(x: i64) -> i64; } unsafe impl Stable for i64 { fn read(x: i64) -> i64 { x } } fn main() -> i64 { Stable::read(42) }",
        );
        interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some("main"))
            .unwrap()
            .key
    };
    let lowered = MirLowering::lower(main_key, &safe_method, &PlaceFlow::analyze(&safe_method));
    assert!(lowered.diagnostics.is_empty(), "{lowered:#?}");
    let function = lowered.function.unwrap();
    assert!(
        function.unsafe_execution,
        "unsafe implementation promises were silently omitted"
    );
    let candidate = grandiose_stage0::vm_backend::emit(&function).unwrap();
    assert!(candidate.function.unsafe_execution);
    let (unsafe_method, _) = elaborate_main(
        "trait Stable { unsafe fn read(x: i64) -> i64; } impl Stable for i64 { unsafe fn read(x: i64) -> i64 { x } } fn main() -> i64 { Stable::read(42) }",
    );
    assert!(
        unsafe_method
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4201"),
        "trait method lost its unsafe invocation requirement"
    );
    let (accepted, signatures) = elaborate_main(
        "trait Stable { unsafe fn read(x: i64) -> i64; } impl Stable for i64 { unsafe fn read(x: i64) -> i64 { x } } fn main() -> i64 { unsafe { Stable::read(42) } }",
    );
    assert_valid_core(&accepted, &signatures);
}

#[test]
fn callable_safety_survives_lifted_closures_and_mir_rejects_erased_indirect_permission() {
    let source = "fn main(f: unsafe () -> i64) -> i64 { unsafe { f() } }";
    let (core, signatures) = elaborate_main(source);
    assert_valid_core(&core, &signatures);
    let definition = *signatures.definitions.keys().next().unwrap();
    let lowered = MirLowering::lower(definition, &core, &PlaceFlow::analyze(&core));
    assert!(lowered.diagnostics.is_empty(), "{lowered:#?}");
    let mut function = lowered.function.unwrap();
    assert!(function.validate().is_ok(), "{function:#?}");
    function.unsafe_execution = false;
    assert!(
        function.validate().is_err(),
        "MIR unsafe indirect call lost its execution requirement"
    );

    let (core, signatures) = elaborate_main("fn main() -> unsafe () -> i64 { () -> i64 { 42 } }");
    assert_valid_core(&core, &signatures);
    let definition = *signatures.definitions.keys().next().unwrap();
    let lowered = MirLowering::lower(definition, &core, &PlaceFlow::analyze(&core));
    assert!(lowered.diagnostics.is_empty(), "{lowered:#?}");
    assert_eq!(lowered.lifted.len(), 1);
    assert_eq!(
        lowered.lifted.values().next().unwrap().safety,
        grandiose_stage0::Safety::Unsafe
    );
    let mut functions = lowered.lifted;
    functions.insert(definition, lowered.function.unwrap());
    let mut program = grandiose_stage0::MirProgram {
        entry: definition,
        functions,
        instances: BTreeMap::new(),
    };
    assert!(program.validate().is_ok(), "{program:#?}");
    let main = program.functions.get_mut(&definition).unwrap();
    for local in &mut main.locals {
        if let Type::Callable { safety, .. } = &mut local.ty {
            *safety = grandiose_stage0::Safety::Safe;
        }
    }
    assert!(
        program.validate().is_err(),
        "MIR callable materialization relabelled an unsafe target"
    );
}

#[test]
fn raw_pointer_inference_preserves_permission_and_checks_recursive_pointees() {
    let mut inference = InferContext::default();
    let hole = inference.fresh();
    let generic = pointer(PointerMutability::Mut, hole.clone());
    let concrete = pointer(PointerMutability::Mut, Type::Scalar(ScalarType::U8));
    inference.unify(generic.clone(), concrete.clone()).unwrap();
    assert_eq!(inference.zonk(generic).unwrap(), concrete);
    assert_eq!(inference.zonk(hole).unwrap(), Type::Scalar(ScalarType::U8));
    assert!(matches!(
        inference.unify(
            concrete.clone(),
            pointer(PointerMutability::Const, Type::Scalar(ScalarType::U8)),
        ),
        Err(TypeError::Mismatch { .. })
    ));
    assert!(matches!(
        inference.unify(
            concrete,
            Type::Reference {
                mutability: Mutability::Unique,
                lifetime: Lifetime::Elided,
                referent: Box::new(Type::Scalar(ScalarType::U8)),
            }
        ),
        Err(TypeError::Mismatch { .. })
    ));

    let recursive = inference.fresh();
    assert!(matches!(
        inference.unify(
            recursive.clone(),
            pointer(PointerMutability::Const, recursive),
        ),
        Err(TypeError::Occurs(_, _))
    ));
    let unresolved = inference.fresh();
    assert!(matches!(
        inference.type_fingerprint(pointer(PointerMutability::Mut, unresolved)),
        Err(TypeError::Unresolved(_))
    ));
}

#[test]
fn raw_pointer_fingerprints_keep_pointee_and_permission_identity() {
    let mut inference = InferContext::default();
    let values = [
        pointer(PointerMutability::Const, Type::Scalar(ScalarType::U8)),
        pointer(PointerMutability::Mut, Type::Scalar(ScalarType::U8)),
        pointer(PointerMutability::Const, Type::Scalar(ScalarType::U64)),
        Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Elided,
            referent: Box::new(Type::Scalar(ScalarType::U8)),
        },
    ];
    let fingerprints = values
        .into_iter()
        .map(|value| inference.type_fingerprint(value).unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(fingerprints.len(), 4);
}

#[test]
fn const_pointer_pointees_are_covariant_but_writable_pointees_are_invariant() {
    let (accepted, _) =
        elaborate_main("fn main<'a>(p: *const &'static i64) -> *const &'a i64 { p }");
    assert!(accepted.diagnostics.is_empty(), "{accepted:#?}");
    for source in [
        "fn main<'a>(p: *mut &'static i64) -> *mut &'a i64 { p }",
        "fn main<'a>(p: *const &'a i64) -> *const &'static i64 { p }",
        "fn main<'a>(p: *mut &'a i64) -> *mut &'static i64 { p }",
    ] {
        let (rejected, _) = elaborate_main(source);
        assert!(
            rejected
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G5017"),
            "invalid pointer variance accepted: {source}\n{rejected:#?}"
        );
    }
}

#[test]
fn pointee_lifetimes_cannot_escape_higher_ranked_callable_binders() {
    let (valid, _) = elaborate_main(
        "fn main(f: for<'a> (*const &'a i64) -> *const &'a i64, p: *const &'static i64) -> *const &'static i64 { f(p) }",
    );
    assert!(valid.diagnostics.is_empty(), "{valid:#?}");
    let (escaping, _) =
        elaborate_main("fn main(f: for<'a> () -> *const &'a i64) -> i64 { f(); 0 }");
    assert!(
        escaping
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5019"),
        "raw pointer hid escaping bound lifetime: {escaping:#?}"
    );
}

#[test]
fn raw_pointer_syntax_requires_an_explicit_permission_and_pointee() {
    for source in [
        "fn main(p: *i64) {}",
        "fn main(p: *mut) {}",
        "fn main(p: *const) {}",
    ] {
        let package = PackageKey("invalid-pointer@0.1.0".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
        let scan = DeclarationScan::scan(&lexed, source);
        let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan);
        assert!(
            !interface.diagnostics.is_empty(),
            "accepted malformed pointer: {source}"
        );
    }
}

#[test]
fn pointer_aliases_and_specialization_retain_nested_lifetime_and_type_arguments() {
    let (_, interface, signatures) =
        collect("type Ptr<'a, T> = *mut &'a T; fn keep<'a, T>(p: Ptr<'a, T>) -> Ptr<'a, T> { p }");
    let key = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("keep"))
        .unwrap()
        .key;
    let instantiated = signatures
        .instantiate_callable_generic(
            key,
            &[
                GenericArgument::Lifetime(Lifetime::Static),
                GenericArgument::Type(Type::Scalar(ScalarType::U64)),
            ],
        )
        .unwrap();
    let expected = pointer(
        PointerMutability::Mut,
        Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Static,
            referent: Box::new(Type::Scalar(ScalarType::U64)),
        },
    );
    assert_eq!(instantiated.parameters, [expected.clone()]);
    assert_eq!(instantiated.result, expected);
}

#[test]
fn trait_projections_normalize_inside_raw_pointer_instances() {
    let (_, interface, signatures) = collect(
        "trait Element { type Item; } impl Element for i64 { type Item = u8; } fn keep<T>(p: *const <T as Element>::Item) -> *const <T as Element>::Item where T: Element { p }",
    );
    let key = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("keep"))
        .unwrap()
        .key;
    let instantiated = signatures
        .instantiate_callable_generic(key, &[GenericArgument::Type(Type::Scalar(ScalarType::I64))])
        .unwrap();
    let result = TraitSolver::new(&signatures)
        .normalize_type(instantiated.result)
        .unwrap();
    assert_eq!(
        result,
        pointer(PointerMutability::Const, Type::Scalar(ScalarType::U8))
    );
}

#[test]
fn raw_pointer_copies_do_not_copy_or_borrow_the_pointee() {
    for source in [
        "struct Linear {} impl Use<[1,1]> for Linear {} fn main(p: *mut Linear) -> (*mut Linear, *mut Linear) { (p, p) }",
        "fn main<'a>(p: *const &'a mut i64) -> (*const &'a mut i64, *const &'a mut i64) { (p, p) }",
    ] {
        let (core, signatures) = elaborate_main(source);
        assert!(core.diagnostics.is_empty(), "{core:#?}");
        assert!(core.validate().is_empty(), "{:?}", core.validate());
        let flow = PlaceFlow::analyze(&core);
        assert!(flow.diagnostics.is_empty(), "{flow:#?}");
        let uses = UseFlow::analyze_with_interface(&core, &flow, &signatures);
        assert!(uses.diagnostics.is_empty(), "{uses:#?}");
        let escapes = EscapeFlow::analyze(&core, &flow);
        assert!(escapes.diagnostics.is_empty(), "{escapes:#?}");
        for expression in &core.expressions {
            if matches!(expression.ty, Type::RawPointer { .. }) {
                assert_eq!(
                    signatures.principal_use_interval(&expression.ty),
                    Some(Quantity::UNRESTRICTED)
                );
            }
        }
    }
}

#[test]
fn typed_closures_and_mir_preserve_raw_pointer_types() {
    let source =
        "fn main(p: *mut i64) -> *mut i64 { let f = (x: *mut i64) -> *mut i64 { x }; f(p) }";
    let (core, signatures) = elaborate_main(source);
    assert!(core.diagnostics.is_empty(), "{core:#?}");
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let key = signatures
        .definitions
        .iter()
        .find_map(|(key, header)| matches!(header, ElaboratedHeader::Callable(_)).then_some(*key))
        .unwrap();
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        key,
        &core,
        &flow,
        &BTreeMap::new(),
        Some(&signatures),
    );
    assert!(lowered.diagnostics.is_empty(), "{lowered:#?}");
    let function = lowered.function.unwrap();
    assert!(function.validate().is_ok(), "{function:#?}");
    assert_eq!(
        function.result,
        pointer(PointerMutability::Mut, Type::Scalar(ScalarType::I64))
    );
    let candidate = grandiose_stage0::vm_backend::emit(&function).unwrap();
    assert!(candidate.function.registers.iter().any(|ty| matches!(ty, grandiose_stage0::VmType::RawPointer { .. })));
    assert_eq!(candidate.schema, grandiose_stage0::STAGE0_VM_SCHEMA);
}

#[test]
fn raw_pointer_mutability_is_not_a_safe_conversion_or_dereference() {
    for source in [
        "fn main(p: *const i64) -> *mut i64 { p }",
        "fn main(p: *mut i64) -> i64 { *p }",
        "fn main(p: *mut i64) -> &mut i64 { p }",
    ] {
        let (core, _) = elaborate_main(source);
        assert!(
            !core.diagnostics.is_empty(),
            "safe code unexpectedly accepted: {source}"
        );
    }
}

#[test]
fn pointer_indirection_breaks_owned_layout_recursion_without_deriving_auto_traits() {
    let (_, interface, signatures) =
        collect("auto trait Marker {} struct Node { next: *mut Node }");
    let marker = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Marker"))
        .unwrap()
        .key;
    let mut solver = TraitSolver::new(&signatures);
    assert_eq!(
        solver.solve(TraitGoal {
            subject: pointer(PointerMutability::Const, Type::Scalar(ScalarType::I64)),
            relation: ElaboratedTraitReference {
                definition: marker,
                arguments: vec![]
            },
        }),
        TraitAnswer::NoSolution
    );
}

#[test]
fn coherence_finds_pointer_head_overlap_and_distinguishes_permissions() {
    for (source, overlaps) in [
        (
            "trait Marker {} impl<T> Marker for *mut T {} impl Marker for *mut i64 {}",
            true,
        ),
        (
            "trait Marker {} impl<T> Marker for *mut T {} impl<T> Marker for *const T {}",
            false,
        ),
        (
            "trait Marker {} impl<'a, T> !Marker for *const &'a T {}",
            false,
        ),
    ] {
        let (_, interface, _) = collect(source);
        let coherence =
            CoherenceSet::collect([&interface], &DefinitionIndex::from_interface(&interface));
        assert_eq!(
            coherence
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G3404"),
            overlaps,
            "{coherence:#?}"
        );
        assert!(
            !coherence
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G3407"),
            "{coherence:#?}"
        );
    }
}
