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
fn nested_modules_inherit_private_items_from_enclosing_modules() {
    let package = PackageKey("resolution-lexical-private-item@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "struct Scratch {} mod compiler;");
    let compiler = collect("crate::compiler", "mod frontend;");
    let frontend = collect(
        "crate::compiler::frontend",
        "fn check(value: Scratch) { () }",
    );
    let index = DefinitionIndex::from_interfaces([&root, &compiler, &frontend]);
    let owner = ModuleKey {
        package,
        path: "crate::compiler::frontend".into(),
    };

    assert!(matches!(
        index.resolve_path(DefinitionNamespace::Type, &owner, &["Scratch".into()]),
        ResolutionState::Resolved(_)
    ));
}

#[test]
fn nested_modules_inherit_private_items_in_every_semantic_namespace() {
    let package = PackageKey("resolution-lexical-private-namespaces@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect(
        "crate",
        "fn value() { () } struct Token {} trait Gate {} effect Trace { note(); } mod compiler;",
    );
    let compiler = collect("crate::compiler", "mod frontend;");
    let frontend = collect("crate::compiler::frontend", "fn check() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &compiler, &frontend]);
    let owner = ModuleKey {
        package,
        path: "crate::compiler::frontend".into(),
    };

    for (namespace, name) in [
        (DefinitionNamespace::Value, "value"),
        (DefinitionNamespace::Type, "Token"),
        (DefinitionNamespace::Trait, "Gate"),
        (DefinitionNamespace::Effect, "Trace"),
    ] {
        assert!(
            matches!(
                index.resolve_path(namespace, &owner, &[name.into()]),
                ResolutionState::Resolved(_)
            ),
            "nested lexical module did not inherit private {namespace:?} `{name}`"
        );
    }
}

#[test]
fn nested_modules_can_import_enclosing_private_bindings_in_every_namespace() {
    let package = PackageKey("resolution-lexical-private-imports@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect(
        "crate",
        "mod api; mod compiler; use crate::api::{value, Token, Gate, Trace};",
    );
    let api = collect(
        "crate::api",
        "pub fn value() { () } pub struct Token {} pub trait Gate {} pub effect Trace { note(); }",
    );
    let compiler = collect("crate::compiler", "mod frontend;");
    let frontend = collect(
        "crate::compiler::frontend",
        "use value; use Token; use Gate; use Trace; fn check() { () }",
    );
    let index = DefinitionIndex::from_interfaces([&root, &api, &compiler, &frontend]);
    let owner = ModuleKey {
        package,
        path: "crate::compiler::frontend".into(),
    };
    assert!(
        index.validate_imports().is_empty(),
        "nested imports must retain enclosing private authority: {:#?}",
        index.validate_imports()
    );
    for (namespace, name) in [
        (DefinitionNamespace::Value, "value"),
        (DefinitionNamespace::Type, "Token"),
        (DefinitionNamespace::Trait, "Gate"),
        (DefinitionNamespace::Effect, "Trace"),
    ] {
        assert!(
            matches!(
                index.resolve_path(namespace, &owner, &[name.into()]),
                ResolutionState::Resolved(_)
            ),
            "nested imported {namespace:?} `{name}` did not resolve"
        );
    }
}

#[test]
fn private_module_import_aliases_are_lexical_to_descendants_not_siblings() {
    let package = PackageKey("resolution-lexical-private-module-import@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "mod api; mod outer; mod sibling;");
    let api = collect("crate::api", "pub fn answer() { () }");
    let outer = collect("crate::outer", "use crate::api as local; mod frontend;");
    let frontend = collect("crate::outer::frontend", "fn run() { () }");
    let sibling = collect("crate::sibling", "fn run() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &api, &outer, &frontend, &sibling]);
    let descendant = ModuleKey {
        package: package.clone(),
        path: "crate::outer::frontend".into(),
    };
    let sibling = ModuleKey {
        package,
        path: "crate::sibling".into(),
    };
    let path = ["local".into(), "answer".into()];
    assert!(matches!(
        index.resolve_path(DefinitionNamespace::Value, &descendant, &path),
        ResolutionState::Resolved(_)
    ));
    assert!(matches!(
        index.resolve_path(DefinitionNamespace::Value, &sibling, &path),
        ResolutionState::Unresolved | ResolutionState::Inaccessible(_)
    ));
}

#[test]
fn public_reexports_preserve_namespace_specific_visibility() {
    let package = PackageKey("resolution-reexport-namespaces@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod api; pub mod facade;");
    let api = collect(
        "crate::api",
        "pub fn value() { () } pub struct Token {} pub trait Gate {} pub effect Trace { note(); }",
    );
    let facade = collect(
        "crate::facade",
        "pub use crate::api::{value, Token, Gate, Trace};",
    );
    let index = DefinitionIndex::from_interfaces([&root, &api, &facade]);
    let requester = ModuleKey {
        package,
        path: "<dependency>".into(),
    };
    for (namespace, name) in [
        (DefinitionNamespace::Value, "value"),
        (DefinitionNamespace::Type, "Token"),
        (DefinitionNamespace::Trait, "Gate"),
        (DefinitionNamespace::Effect, "Trace"),
    ] {
        assert!(
            matches!(
                index.resolve_path(
                    namespace,
                    &requester,
                    &["crate".into(), "facade".into(), name.into()],
                ),
                ResolutionState::Resolved(_)
            ),
            "public {namespace:?} reexport `{name}` was not visible to a dependency"
        );
    }
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
    assert!(diagnostics[0].message.contains("private target"));
}

#[test]
fn exported_reexports_of_missing_targets_are_rejected_at_interface_freezing() {
    let package = PackageKey("resolution-exported-missing-reexport@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod facade;");
    let facade = collect("crate::facade", "pub use crate::missing::answer;");
    let index = DefinitionIndex::from_interfaces([&root, &facade]);

    let diagnostics = index.validate_exported_imports();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].code, "G3317");
    assert!(diagnostics[0].message.contains("missing target"));
}

#[test]
fn competing_module_aliases_remain_resolution_ambiguities_instead_of_looking_missing() {
    let package = PackageKey("resolution-module-alias-collision@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod left; pub mod right; mod facade;");
    let left = collect("crate::left", "pub mod api;");
    let right = collect("crate::right", "pub mod api;");
    let left_api = collect("crate::left::api", "pub fn left() { () }");
    let right_api = collect("crate::right::api", "pub fn right() { () }");
    let facade = collect(
        "crate::facade",
        "use crate::left::api as client; use crate::right::api as client;",
    );
    let index =
        DefinitionIndex::from_interfaces([&root, &left, &right, &left_api, &right_api, &facade]);
    let owner = ModuleKey {
        package,
        path: "crate::facade".into(),
    };

    let state = index.resolve_path(
        DefinitionNamespace::Value,
        &owner,
        &["client".into(), "left".into()],
    );
    assert!(
        matches!(state, ResolutionState::Ambiguous(ref candidates) if candidates.len() == 2),
        "a conflicting module alias must not select one branch or masquerade as missing: {state:?}"
    );
}

#[test]
fn exported_competing_module_aliases_are_rejected_while_freezing_the_interface() {
    let package = PackageKey("resolution-exported-module-alias-collision@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod left; pub mod right; pub mod facade;");
    let left = collect("crate::left", "pub mod api;");
    let right = collect("crate::right", "pub mod api;");
    let left_api = collect("crate::left::api", "pub fn left() { () }");
    let right_api = collect("crate::right::api", "pub fn right() { () }");
    let facade = collect(
        "crate::facade",
        "pub use crate::left::api as client; pub use crate::right::api as client;",
    );
    let index =
        DefinitionIndex::from_interfaces([&root, &left, &right, &left_api, &right_api, &facade]);

    assert!(
        index.validate_exported_imports().iter().any(|diagnostic| {
            diagnostic.code == "G3318" && diagnostic.message.contains("client")
        })
    );
}

#[test]
fn cyclic_public_globs_terminate_without_hiding_a_reachable_module_candidate() {
    let package = PackageKey("resolution-cyclic-public-globs@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod a; pub mod b; pub mod target;");
    let a = collect("crate::a", "pub use crate::b::*; pub use crate::target::*;");
    let b = collect("crate::b", "pub use crate::a::*;");
    let target = collect("crate::target", "pub mod api;");
    let api = collect("crate::target::api", "pub fn answer() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &a, &b, &target, &api]);
    let owner = ModuleKey {
        package,
        path: "crate".into(),
    };

    let state = index.resolve_path(
        DefinitionNamespace::Value,
        &owner,
        &["crate".into(), "a".into(), "api".into(), "answer".into()],
    );
    assert!(
        matches!(state, ResolutionState::Resolved(_)),
        "the cyclic glob must terminate and continue to the target candidate: {state:?}"
    );
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
fn module_import_aliases_are_real_qualified_path_segments() {
    let package = PackageKey("resolution-module-alias@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod api; pub mod facade; mod caller;");
    let api = collect("crate::api", "pub fn answer() { () }");
    let facade = collect("crate::facade", "pub use crate::api as client;");
    let caller = collect("crate::caller", "fn local() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &api, &facade, &caller]);
    let owner = ModuleKey {
        package,
        path: "crate::caller".into(),
    };

    let state = index.resolve_path(
        DefinitionNamespace::Value,
        &owner,
        &[
            "crate".into(),
            "facade".into(),
            "client".into(),
            "answer".into(),
        ],
    );
    assert!(matches!(state, ResolutionState::Resolved(_)), "{state:?}");
}

#[test]
fn private_module_aliases_cannot_be_used_as_public_facade_path_edges() {
    let package = PackageKey("resolution-private-module-alias@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod api; pub mod facade; mod caller;");
    let api = collect("crate::api", "pub fn answer() { () }");
    let facade = collect("crate::facade", "use crate::api as client;");
    let caller = collect("crate::caller", "fn local() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &api, &facade, &caller]);
    let owner = ModuleKey {
        package,
        path: "crate::caller".into(),
    };

    assert!(matches!(
        index.resolve_path(
            DefinitionNamespace::Value,
            &owner,
            &[
                "crate".into(),
                "facade".into(),
                "client".into(),
                "answer".into(),
            ],
        ),
        ResolutionState::Inaccessible(_)
    ));
}

#[test]
fn public_globs_make_public_child_modules_traversable_without_source_order() {
    let package = PackageKey("resolution-glob-module@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod tree; pub mod facade; mod caller;");
    let tree = collect("crate::tree", "pub mod child;");
    let child = collect("crate::tree::child", "pub fn answer() { () }");
    let facade = collect("crate::facade", "pub use crate::tree::*;");
    let caller = collect("crate::caller", "fn local() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &tree, &child, &facade, &caller]);
    let owner = ModuleKey {
        package,
        path: "crate::caller".into(),
    };

    assert!(matches!(
        index.resolve_path(
            DefinitionNamespace::Value,
            &owner,
            &[
                "crate".into(),
                "facade".into(),
                "child".into(),
                "answer".into(),
            ],
        ),
        ResolutionState::Resolved(_)
    ));
}

#[test]
fn sealed_public_interfaces_include_transitive_module_alias_and_glob_surfaces() {
    let package = PackageKey("resolution-sealed-public-surface@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod api; pub mod facade;");
    let facade = collect("crate::facade", "pub use crate::api as client;");
    let api_before = collect("crate::api", "pub fn answer() { () } fn private() { () }");
    let api_after = collect(
        "crate::api",
        "pub fn answer() { () } pub fn newly_exported() { () } fn private() { () }",
    );

    let before = DefinitionIndex::from_interfaces([&root, &facade, &api_before]);
    let after = DefinitionIndex::from_interfaces([&root, &facade, &api_after]);

    assert_ne!(
        before.sealed_public_fingerprint(&facade),
        after.sealed_public_fingerprint(&facade),
        "a public module alias must carry the target's exported API"
    );
    assert_ne!(
        before.sealed_public_fingerprint(&root),
        after.sealed_public_fingerprint(&root),
        "a public module edge must carry its recursively reachable API"
    );

    let glob = collect("crate::facade", "pub use crate::api::*;");
    let glob_before = DefinitionIndex::from_interfaces([&root, &glob, &api_before]);
    let glob_after = DefinitionIndex::from_interfaces([&root, &glob, &api_after]);
    assert_ne!(
        glob_before.sealed_public_fingerprint(&glob),
        glob_after.sealed_public_fingerprint(&glob),
        "a public glob must carry the exact exported names it introduces"
    );
}

#[test]
fn reexported_type_interfaces_include_inherent_members_and_their_owner_dependencies() {
    let package = PackageKey("resolution-inherent-surface@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod api; mod methods; pub mod facade;");
    let facade = collect("crate::facade", "pub use crate::api::Cell as Public;");
    let api = collect("crate::api", "pub struct Cell {}");
    let methods = collect(
        "crate::methods",
        "use crate::api::Cell; impl Cell { pub fn answer() -> i64 { 1 } fn private() {} }",
    );
    let changed = collect(
        "crate::methods",
        "use crate::api::Cell; impl Cell { pub fn answer() -> u64 { 1 } fn private() {} }",
    );
    let body_changed = collect(
        "crate::methods",
        "use crate::api::Cell; impl Cell { pub fn answer() -> i64 { 2 } fn renamed_private() {} }",
    );
    let index = DefinitionIndex::from_interfaces([&root, &facade, &api, &methods]);
    let after = DefinitionIndex::from_interfaces([&root, &facade, &api, &changed]);
    let bodies = DefinitionIndex::from_interfaces([&root, &facade, &api, &body_changed]);
    assert!(
        index.validate_imports().is_empty(),
        "{:#?}",
        index.validate_imports()
    );
    assert_ne!(
        index.sealed_public_fingerprint(&facade),
        after.sealed_public_fingerprint(&facade)
    );
    assert_eq!(
        index.sealed_public_fingerprint(&facade),
        bodies.sealed_public_fingerprint(&facade)
    );
    assert_eq!(
        index.sealed_public_dependencies(&facade),
        vec![api.module.clone(), methods.module.clone()]
    );
}

#[test]
fn sealed_public_dependencies_follow_only_resolved_public_surface_contracts() {
    let package = PackageKey("resolution-sealed-public-dependencies@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect(
        "crate",
        "pub mod api; pub mod facade; pub mod private_facade;",
    );
    let api = collect("crate::api", "pub fn answer() { () } fn hidden() { () }");
    let facade = collect("crate::facade", "pub use crate::api as client;");
    let private_facade = collect(
        "crate::private_facade",
        "use crate::api::answer; pub fn local() { () }",
    );
    let index = DefinitionIndex::from_interfaces([&root, &api, &facade, &private_facade]);

    let api_module = ModuleKey {
        package: package.clone(),
        path: "crate::api".into(),
    };
    let facade_module = ModuleKey {
        package: package.clone(),
        path: "crate::facade".into(),
    };
    let private_facade_module = ModuleKey {
        package: package.clone(),
        path: "crate::private_facade".into(),
    };
    assert_eq!(
        index.sealed_public_dependencies(&facade),
        vec![api_module.clone()]
    );
    assert_eq!(
        index.sealed_public_dependencies(&private_facade),
        Vec::<ModuleKey>::new(),
        "a private import is not part of the exported facade contract"
    );
    assert_eq!(
        index.sealed_public_dependencies(&root),
        vec![api_module, facade_module, private_facade_module],
        "public module edges are target-interface dependencies"
    );
}

#[test]
fn sealed_public_interfaces_exclude_private_members_behind_public_modules() {
    let package = PackageKey("resolution-sealed-private-surface@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "pub mod api; pub mod facade;");
    let facade = collect("crate::facade", "pub use crate::api::*;");
    let api_before = collect("crate::api", "pub fn answer() { () } fn hidden() { 1 }");
    let api_after = collect("crate::api", "pub fn answer() { () } fn hidden() { 2 }");

    let before = DefinitionIndex::from_interfaces([&root, &facade, &api_before]);
    let after = DefinitionIndex::from_interfaces([&root, &facade, &api_after]);
    assert_eq!(
        before.sealed_public_fingerprint(&facade),
        after.sealed_public_fingerprint(&facade),
        "private target implementation changes must not churn a public facade ABI"
    );
    assert_eq!(
        before.sealed_public_fingerprint(&root),
        after.sealed_public_fingerprint(&root),
        "private target implementation changes must not churn the package surface"
    );
}

#[test]
fn glob_imports_expand_deterministically_and_contribute_import_occurrences() {
    let package = PackageKey("resolution-glob@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "use crate::math::*;");
    let math = collect("crate::math", "pub fn answer() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &math]);
    let owner = ModuleKey {
        package,
        path: "crate".into(),
    };
    let ResolutionState::Resolved(answer) =
        index.resolve_path(DefinitionNamespace::Value, &owner, &["answer".into()])
    else {
        panic!("globbed value did not resolve")
    };
    let occurrences = index.import_occurrences();
    assert!(occurrences.iter().any(|occurrence| {
        occurrence.namespace == DefinitionNamespace::Value
            && occurrence.role == OccurrenceRole::Import
            && occurrence.state == ResolutionState::Resolved(answer)
    }));
    let mut references = ReferenceIndex::default();
    references.record_imports(&index);
    assert!(references.references(answer).iter().any(|occurrence| {
        occurrence.role == OccurrenceRole::Import
            && occurrence.namespace == DefinitionNamespace::Value
    }));
}

#[test]
fn glob_imports_preserve_ambiguity_instead_of_picking_source_order() {
    let package = PackageKey("resolution-glob-collision@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "use crate::left::*; use crate::right::*;");
    let left = collect("crate::left", "pub fn answer() { () }");
    let right = collect("crate::right", "pub fn answer() { () }");
    let index = DefinitionIndex::from_interfaces([&root, &left, &right]);
    let owner = ModuleKey {
        package,
        path: "crate".into(),
    };
    assert!(matches!(
        index.resolve_path(DefinitionNamespace::Value, &owner, &["answer".into()]),
        ResolutionState::Ambiguous(_)
    ));
}

#[test]
fn private_glob_import_edges_are_rejected_without_waiting_for_a_body_use() {
    let package = PackageKey("resolution-private-glob@0.1.0".into());
    let collect = |module: &str, source: &str| {
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), module, &lexed, source, &scan).interface
    };
    let root = collect("crate", "mod outer; mod facade;");
    let outer = collect("crate::outer", "mod hidden;");
    let hidden = collect("crate::outer::hidden", "pub fn answer() { () }");
    let facade = collect("crate::facade", "use crate::outer::hidden::*;");
    let index = DefinitionIndex::from_interfaces([&root, &outer, &hidden, &facade]);
    assert!(
        index
            .validate_imports()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3326")
    );
}

#[test]
fn private_globs_do_not_make_absent_module_names_inaccessible() {
    let collect = |package: &str, module: &str, source: &str| {
        let package = PackageKey(package.into());
        let file = FileKey::new(&package, &format!("src/{module}.glorious"));
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package, module, &lexed, source, &scan).interface
    };
    for imports in [
        "use library::*; use library::api::*;",
        "use library::api::*; use library::*;",
    ] {
        let root = collect("consumer@0.1.0", "crate", imports);
        let library = collect("library@0.1.0", "crate", "pub mod api; pub mod internal; pub fn library() { () }");
        let api = collect("library@0.1.0", "crate::api", "use crate::*; use crate::library as hidden_value; pub fn answer() { () }");
        let internal = collect("library@0.1.0", "crate::internal", "pub fn secret() { () }");
        let index = DefinitionIndex::from_interfaces([&root, &library, &api, &internal]);
        assert!(index.validate_imports().is_empty(), "{:#?}", index.validate_imports());
        let owner = ModuleKey { package: root.package.clone(), path: "crate".into() };
        let resolve = |path: &[&str]| index.resolve_path(DefinitionNamespace::Value, &owner,
            &path.iter().map(|part| (*part).to_owned()).collect::<Vec<_>>());
        assert!(matches!(resolve(&["library", "api", "answer"]), ResolutionState::Resolved(_)));
        assert!(matches!(resolve(&["library", "internal", "secret"]), ResolutionState::Resolved(_)));
        assert!(matches!(resolve(&["library", "api", "internal", "secret"]), ResolutionState::Inaccessible(_)),
            "a private glob must not re-export its actual module bindings");
        assert_eq!(resolve(&["library", "api", "missing", "answer"]), ResolutionState::Unresolved);
        assert_eq!(resolve(&["library", "api", "hidden_value", "answer"]), ResolutionState::Unresolved);
        assert!(matches!(resolve(&["library", "api", "hidden_value"]),
            ResolutionState::Inaccessible(_) | ResolutionState::Unresolved),
            "the private value alias must not become an exported value");
    }
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
