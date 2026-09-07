//! Language §2.3: explicit imports outrank glob candidates without hiding errors.

use grandiose_stage0::{
    DeclarationScan, DefinitionIndex, DefinitionNamespace as Ns, FileKey, InterfaceSet, LexedFile,
    ModuleKey, PackageKey, ResolutionState,
};

fn index(imports: &str) -> (DefinitionIndex, ModuleKey) {
    let package = PackageKey("import-priority@0.1.0".into());
    let sources = [
        (
            "crate",
            "pub mod primary; pub mod fallback; pub mod consumer;",
        ),
        (
            "crate::primary",
            "pub fn value() {} pub struct Item {} pub type Scalar = i64; pub trait Rule {} pub effect Signal { send(); } pub infixl 8 join; pub fn join() {} pub mod nested; fn secret() {}",
        ),
        (
            "crate::fallback",
            "pub fn value() {} pub struct Item {} pub trait Rule {} pub effect Signal { send(); } pub infixl 9 join; pub fn join() {} pub fn secret() {} pub mod selected;",
        ),
        ("crate::primary::nested", "pub fn value() {}"),
        ("crate::fallback::selected", "pub fn value() {}"),
        ("crate::consumer", imports),
    ];
    let interfaces = sources.map(|(module, source)| {
        let lexed = LexedFile::lex(FileKey::new(&package, module), source);
        let scan = DeclarationScan::scan(&lexed, source);
        assert!(scan.diagnostics.is_empty(), "{scan:?}");
        let interface = InterfaceSet::collect(package.clone(), module, &lexed, source, &scan);
        assert!(
            interface.diagnostics.is_empty(),
            "{:?}",
            interface.diagnostics
        );
        interface.interface
    });
    (
        DefinitionIndex::from_interfaces(interfaces.iter()),
        ModuleKey {
            package,
            path: "crate::consumer".into(),
        },
    )
}

fn resolve(
    index: &DefinitionIndex,
    owner: &ModuleKey,
    namespace: Ns,
    path: &[&str],
) -> ResolutionState {
    index.resolve_path(
        namespace,
        owner,
        &path.iter().map(|s| (*s).into()).collect::<Vec<_>>(),
    )
}

#[test]
fn explicit_import_priority_reaches_execution_and_wire_round_trip() {
    use grandiose_stage0::{
        CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath,
        SourceInput, StageZeroCompiler, decode_and_verify_program,
    };
    for imports in [
        "use crate::primary::value; use crate::fallback::*;",
        "use crate::fallback::*; use crate::primary::value;",
    ] {
        let source = format!(
            "mod primary {{ pub fn value() -> i64 {{ 42 }} }}\n\
             mod fallback {{ pub fn value() -> i64 {{ 7 }} }}\n\
             {imports}\n pub fn main() -> i64 {{ value() }}"
        );
        let package = PackageKey("import-priority-run@0.1.0".into());
        let request = CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"import-priority-run")),
            mode: CompilationMode::Build,
            root_package: package.clone(),
            sources: vec![SourceInput::new(
                package,
                LogicalPath::parse("src/main.glorious").unwrap(),
                source.as_bytes(),
            )],
            target: "stage0-vm".into(),
            semantic_options: Default::default(),
            codegen_options: Default::default(),
            capability_manifest: vec![],
            runtime_manifest: None,
        };
        let outcome = StageZeroCompiler::new().compile(request).unwrap();
        assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
        let program = outcome.artifact.unwrap();
        assert_eq!(program.run_i64().unwrap(), 42);
        assert_eq!(
            decode_and_verify_program(&program.canonical_bytes())
                .unwrap()
                .run_i64()
                .unwrap(),
            42,
        );
    }
}

#[test]
fn explicit_imports_win_in_each_namespace_independent_of_import_order() {
    for imports in [
        "use crate::primary::{value, Item, Rule, Signal, join}; use crate::fallback::*;",
        "use crate::fallback::*; use crate::primary::{value, Item, Rule, Signal, join};",
    ] {
        let (index, owner) = index(imports);
        for (namespace, name) in [
            (Ns::Value, "value"),
            (Ns::Type, "Item"),
            (Ns::Trait, "Rule"),
            (Ns::Effect, "Signal"),
            (Ns::Operator, "join"),
        ] {
            let expected = resolve(&index, &owner, namespace, &["crate", "primary", name]);
            assert!(
                matches!(expected, ResolutionState::Resolved(_)),
                "{expected:?}"
            );
            assert_eq!(
                resolve(&index, &owner, namespace, &[name]),
                expected,
                "{namespace:?}"
            );
        }
    }
}

#[test]
fn explicit_module_alias_wins_over_a_glob_module() {
    let (index, owner) = index("use crate::fallback::*; use crate::primary::nested as selected;");
    assert_eq!(
        resolve(&index, &owner, Ns::Value, &["selected", "value"]),
        resolve(
            &index,
            &owner,
            Ns::Value,
            &["crate", "primary", "nested", "value"]
        ),
    );
}

#[test]
fn an_explicit_type_import_does_not_hide_a_value_in_another_namespace() {
    let (index, owner) = index("use crate::primary::Scalar as value; use crate::fallback::*;");
    let expected = resolve(&index, &owner, Ns::Value, &["crate", "fallback", "value"]);
    assert!(matches!(expected, ResolutionState::Resolved(_)));
    assert_eq!(resolve(&index, &owner, Ns::Value, &["value"]), expected);
    assert_eq!(
        resolve(&index, &owner, Ns::Type, &["value"]),
        resolve(&index, &owner, Ns::Type, &["crate", "primary", "Scalar"]),
    );
}

#[test]
fn conflicting_explicit_module_aliases_do_not_fall_back_to_a_glob() {
    let (index, owner) = index(
        "use crate::primary::nested as selected; use crate::fallback::selected; use crate::fallback::*;",
    );
    assert!(matches!(
        resolve(&index, &owner, Ns::Value, &["selected", "value"]),
        ResolutionState::Ambiguous(_)
    ));
}

#[test]
fn public_explicit_reexports_win_without_granting_private_import_authority() {
    let (index, owner) = index("pub use crate::primary::value; pub use crate::fallback::*;");
    let requester = ModuleKey {
        package: owner.package.clone(),
        path: "crate".into(),
    };
    assert_eq!(
        resolve(&index, &requester, Ns::Value, &["consumer", "value"]),
        resolve(&index, &requester, Ns::Value, &["primary", "value"]),
    );
}

#[test]
fn conflicting_explicit_imports_stay_ambiguous_despite_a_glob() {
    let (index, owner) =
        index("use crate::primary::value; use crate::fallback::value; use crate::primary::*;");
    assert!(
        matches!(resolve(&index, &owner, Ns::Value, &["value"]), ResolutionState::Ambiguous(keys) if keys.len() == 2)
    );
}

#[test]
fn inaccessible_explicit_import_does_not_fall_back_to_a_public_glob() {
    let (index, owner) = index("use crate::primary::secret; use crate::fallback::*;");
    assert!(matches!(
        resolve(&index, &owner, Ns::Value, &["secret"]),
        ResolutionState::Inaccessible(_)
    ));
}

#[test]
fn conflicting_globs_stay_ambiguous_without_an_explicit_selection() {
    let (index, owner) = index("use crate::primary::*; use crate::fallback::*;");
    assert!(
        matches!(resolve(&index, &owner, Ns::Value, &["value"]), ResolutionState::Ambiguous(keys) if keys.len() == 2)
    );
}
