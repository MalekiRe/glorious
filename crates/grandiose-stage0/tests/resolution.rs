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
fn journaled_scope_binding_identities_do_not_reuse_a_closed_scope_depth() {
    let mut scopes = ScopeMap::<String, u32>::default();
    scopes.enter();
    scopes.define("value".into(), 1);
    let outer = scopes.binding_generation(&"value".into()).unwrap();

    scopes.enter();
    scopes.define("saved".into(), 2);
    let first_sibling = scopes.binding_generation(&"saved".into()).unwrap();
    assert!(scopes.leave());

    scopes.enter();
    scopes.define("saved".into(), 3);
    let second_sibling = scopes.binding_generation(&"saved".into()).unwrap();
    assert_ne!(first_sibling, second_sibling);
    assert_ne!(outer, second_sibling);
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
fn private_nested_module_paths_do_not_leak_public_members_to_siblings_or_ancestors() {
    let package = PackageKey("resolution-private-module@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "mod outer; mod sibling;");
    let outer = collect("crate::outer", "mod hidden;");
    let hidden = collect("crate::outer::hidden", "pub fn escape() { () }");
    let sibling = collect("crate::sibling", "fn local() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &outer, &hidden, &sibling]);
    let owner = ModuleKey {
        package: package.clone(),
        path: "crate::sibling".into(),
    };
    let ancestor = ModuleKey {
        package: package.clone(),
        path: "crate".into(),
    };
    let declaring_module = ModuleKey {
        package,
        path: "crate::outer".into(),
    };
    let path = [
        "crate".into(),
        "outer".into(),
        "hidden".into(),
        "escape".into(),
    ];

    assert!(matches!(
        index.resolve_path(DefinitionNamespace::Value, &owner, &path),
        ResolutionState::Inaccessible(_)
    ));
    assert!(matches!(
        index.resolve_path(DefinitionNamespace::Value, &ancestor, &path),
        ResolutionState::Inaccessible(_)
    ));
    assert!(matches!(
        index.resolve_path(DefinitionNamespace::Value, &declaring_module, &path),
        ResolutionState::Resolved(_)
    ));
}

#[test]
fn public_module_edges_allow_public_members_but_not_private_members() {
    let package = PackageKey("resolution-public-module@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod api; mod sibling;");
    let api = collect("crate::api", "pub fn exposed() { () } fn hidden() { () }");
    let sibling = collect("crate::sibling", "fn local() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &api, &sibling]);
    let owner = ModuleKey {
        package,
        path: "crate::sibling".into(),
    };

    assert!(matches!(
        index.resolve_path(
            DefinitionNamespace::Value,
            &owner,
            &["crate".into(), "api".into(), "exposed".into()],
        ),
        ResolutionState::Resolved(_)
    ));
    assert!(matches!(
        index.resolve_path(
            DefinitionNamespace::Value,
            &owner,
            &["crate".into(), "api".into(), "hidden".into()],
        ),
        ResolutionState::Inaccessible(_)
    ));
}

#[test]
fn public_reexports_preserve_callers_visibility_authority() {
    let package = PackageKey("resolution-reexport-authority@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "mod outer; mod facade; mod caller;");
    let outer = collect("crate::outer", "mod hidden;");
    let hidden = collect("crate::outer::hidden", "pub fn escape() { () }");
    let facade = collect("crate::facade", "pub use crate::outer::hidden::escape;");
    let caller = collect("crate::caller", "fn local() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &outer, &hidden, &facade, &caller]);
    let owner = ModuleKey {
        package,
        path: "crate::caller".into(),
    };

    let state = index.resolve_path(
        DefinitionNamespace::Value,
        &owner,
        &["crate".into(), "facade".into(), "escape".into()],
    );
    assert!(
        matches!(state, ResolutionState::Inaccessible(_)),
        "{state:?}; {:#?}",
        facade.definitions
    );
}

#[test]
fn exported_public_reexports_are_rejected_before_any_body_uses_them() {
    let package = PackageKey("resolution-exported-reexport@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod outer; pub mod facade;");
    let outer = collect("crate::outer", "mod hidden;");
    let hidden = collect("crate::outer::hidden", "pub fn escape() { () }");
    let facade = collect("crate::facade", "pub use crate::outer::hidden::escape;");
    let index = DefinitionIndex::from_interfaces([&root, &outer, &hidden, &facade]);
    let diagnostics = index.validate_exported_imports();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].code, "G3317");
    assert!(diagnostics[0].message.contains("private module path"));
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
