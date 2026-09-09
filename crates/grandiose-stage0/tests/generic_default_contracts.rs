use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath,
    PackageKey, SourceInput, StageZeroCompiler,
};

fn compile(source: &str) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    let package = PackageKey("generic-default-contracts@1".into());
    StageZeroCompiler::new().compile(CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"generic-default-contracts")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: Default::default(),
        capability_manifest: vec![],
        runtime_manifest: None,
    })
}

#[test]
fn unused_callable_and_nested_generic_defaults_are_checked() {
    for declaration in [
        "fn bad<T = T>() {}",
        "fn bad<T = U, U = i64>() {}",
        "fn bad<e: EffectRow = f, f: EffectRow = {}>() {}",
        "fn bad<'a = 'b, 'b = 'static>() {}",
        "fn bad<n: u32 = m * 0, m: u32 = 1>() {}",
        "struct Box(); impl Box { fn bad<T = T>() {} }",
        "trait Bad<T = T> {}",
        "trait Bad<A> { fn bad<T = T>(); }",
        "trait Bad<A> { type Item<T = T>; }",
        "effect Bad<T = T> { send(); }",
        "effect Bad<A> { send<T = T>(); }",
    ] {
        let source = format!("{declaration} pub fn main() -> i64 {{ 42 }}");
        let error = compile(&source).expect_err(declaration);
        assert!(error.diagnostics().iter().any(|diagnostic|
            diagnostic.code == "G3318" && diagnostic.message.contains("non-earlier binder")),
            "missing default dependency diagnostic for {declaration}: {error:?}");
    }
}

#[test]
fn nested_defaults_can_reference_earlier_outer_binders_and_self() {
    for declaration in [
        "fn good<T, U = T, e: EffectRow = {}, f: EffectRow = e>() {}",
        "struct Box<T>(T); impl<T> Box<T> { fn good<U = Self>() {} }",
        "trait Good<A, n: u32> { fn good<T = A, m: u32 = n + 1>(); type Item<T = Self>; }",
        "effect Good<A, n: u32> { send<T = A, m: u32 = n + 1>(); }",
    ] {
        let source = format!("{declaration} pub fn main() -> i64 {{ 42 }}");
        let outcome = compile(&source).unwrap_or_else(|error| panic!("{declaration}: {error:?}"));
        assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn callable_default_templates_preserve_declaring_identity_and_inherent_self() {
    use grandiose_stage0::{
        DeclarationScan, DefinitionIndex, ElaboratedInterface, FileKey, GenericArgument, InterfaceSet,
        LexedFile, Lifetime, Type,
    };
    let package = PackageKey("generic-default-templates@1".into());
    // Interface collection is module-local. Supply both module interfaces,
    // just as the source service does after discovering its module graph.
    let interfaces = [
        ("crate", "src/lib.glorious", "mod owner; struct Local();
            struct Holder<T>(T); impl<T> Holder<T> { pub fn build<U = Self>() {} }"),
        ("crate::owner", "src/owner.glorious", "pub struct Local(); type Alias = Local;
            pub fn freeze<T = Alias, F = for<'a> (&'a T) -> &'a T>();"),
    ].map(|(module, path, source)| {
        let file = FileKey::new(&package, path);
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        let collected = InterfaceSet::collect(package.clone(), module, &lexed, source, &scan);
        assert!(collected.diagnostics.is_empty(), "{:?}", collected.diagnostics);
        collected.interface
    });
    let index = DefinitionIndex::from_interfaces(&interfaces);
    let signatures = ElaboratedInterface::merge(interfaces.iter()
        .map(|interface| ElaboratedInterface::elaborate_with_index(interface, &index)));
    assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
    let definitions = interfaces.iter().flat_map(|interface| &interface.definitions).collect::<Vec<_>>();
    let named = |name: &str| definitions.iter().copied()
        .find(|definition| definition.name.as_deref() == Some(name))
        .unwrap_or_else(|| panic!("missing {name}; declarations: {:?}",
            definitions.iter().map(|definition| &definition.name).collect::<Vec<_>>()));
    let freeze = named("freeze");
    let local = definitions.iter().find(|definition|
        definition.name.as_deref() == Some("Local") && definition.module == freeze.module).unwrap();
    let defaults = &signatures.generic_defaults[&freeze.key];
    assert_eq!(defaults[0], Some(GenericArgument::Type(Type::Nominal {
        definition: local.key, arguments: vec![],
    })));
    let Some(GenericArgument::Type(Type::Callable { lifetime_binders, parameters, result, .. })) =
        &defaults[1] else { panic!("missing higher-ranked default: {:?}", defaults[1]); };
    assert_eq!(*lifetime_binders, 1);
    assert_eq!(&parameters[0], result.as_ref());
    assert!(matches!(&parameters[0], Type::Reference { lifetime: Lifetime::Bound { depth: 0, index: 0 }, referent, .. }
        if referent.as_ref() == &Type::Generic(0)));
    assert_eq!(signatures.generic_defaults[&named("Holder::build").key], vec![
        None,
        Some(GenericArgument::Type(Type::Nominal {
            definition: named("Holder").key,
            arguments: vec![GenericArgument::Type(Type::Generic(0))],
        })),
    ]);
}
