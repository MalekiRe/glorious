use grandiose_stage0::{
    DeclarationScan, DefinitionIndex, DefinitionNamespace, FileKey, InterfaceSet, LexedFile,
    LogicalPath, ModuleKey, Occurrence, OccurrenceRole, PackageKey, ReferenceIndex,
    ResolutionState, ScopeMap,
};

#[test]
fn journaled_scopes_restore_shadowed_bindings_exactly() {
    let mut scopes = ScopeMap::<String, u32>::default();
    scopes.enter();
    scopes.define("value".into(), 1);
    scopes.enter();
    scopes.define("value".into(), 2);
    assert_eq!(scopes.lookup(&"value".into()), Some(&2));
    assert!(scopes.leave());
    assert_eq!(scopes.lookup(&"value".into()), Some(&1));
    assert!(scopes.leave());
    assert_eq!(scopes.lookup(&"value".into()), None);
    assert!(!scopes.leave());
}

#[test]
fn qualified_paths_are_lexical_and_enforce_module_visibility() {
    let package = PackageKey("resolution@0.1.0".into());
    let root_source = "mod math; mod hidden;";
    let math_source = "pub fn answer() { () }";
    let hidden_source = "fn secret() { () }";
    let interface = |path: &str, source: &str| {
        let file = FileKey::new(&package, path);
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(
            package.clone(),
            match path {
                "src/lib.glorious" => "crate",
                "src/math/math.glorious" => "crate::math",
                "src/hidden/hidden.glorious" => "crate::hidden",
                _ => unreachable!(),
            },
            &lexed,
            source,
            &scan,
        )
        .interface
    };
    let root = interface("src/lib.glorious", root_source);
    let math = interface("src/math/math.glorious", math_source);
    let hidden = interface("src/hidden/hidden.glorious", hidden_source);
    let index = DefinitionIndex::from_interfaces([&root, &math, &hidden]);
    let owner = ModuleKey {
        package,
        path: "crate".into(),
    };

    assert!(matches!(
        index.resolve_path(
            DefinitionNamespace::Value,
            &owner,
            &["math".into(), "answer".into()],
        ),
        ResolutionState::Resolved(_)
    ));
    assert!(matches!(
        index.resolve_path(
            DefinitionNamespace::Value,
            &owner,
            &["crate".into(), "hidden".into(), "secret".into()],
        ),
        ResolutionState::Inaccessible(_)
    ));
}

#[test]
fn explicit_import_aliases_bind_in_their_declared_module_only() {
    let package = PackageKey("resolution-import@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "use math::answer as meaning;");
    let math = collect("crate::math", "pub fn answer() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &math]);
    let owner = ModuleKey {
        package,
        path: "crate".into(),
    };
    let imported = index.resolve_path(DefinitionNamespace::Value, &owner, &["meaning".into()]);
    assert!(
        matches!(imported, ResolutionState::Resolved(_)),
        "{imported:?}; {:#?}",
        root.definitions
    );
    assert!(matches!(
        index.resolve_path(DefinitionNamespace::Value, &owner, &["answer".into()]),
        ResolutionState::Unresolved
    ));
}

#[test]
fn interface_index_and_reference_index_share_one_stable_definition_identity() {
    let source = "pub fn answer() { () }";
    let package = PackageKey("resolution@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let index = DefinitionIndex::from_interface(&interface);
    let ResolutionState::Resolved(answer) = index.resolve(DefinitionNamespace::Value, "answer")
    else {
        panic!("answer must resolve uniquely")
    };
    let mut references = ReferenceIndex::default();
    references.record(Occurrence {
        span: lexed.tokens[1].span,
        namespace: DefinitionNamespace::Value,
        role: OccurrenceRole::Definition,
        state: ResolutionState::Resolved(answer),
    });
    references.canonicalize();
    assert_eq!(references.references(answer).len(), 1);
}
