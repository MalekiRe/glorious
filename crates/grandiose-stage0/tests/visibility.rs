use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, DeclarationScan, DiagnosticClass,
    Digest, FileKey, LogicalPath, PackageKey, SourceInput, StageZeroCompiler, Visibility,
    decode_and_verify_program,
};

fn compile(
    sources: &[(&str, &str, &str)],
) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    StageZeroCompiler::new().compile(request(sources))
}

fn request(sources: &[(&str, &str, &str)]) -> CompilationRequest {
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"visibility")),
        mode: CompilationMode::Build,
        root_package: PackageKey(sources[0].0.into()),
        sources: sources
            .iter()
            .map(|(package, path, source)| {
                SourceInput::new(
                    PackageKey((*package).into()),
                    LogicalPath::parse(*path).unwrap(),
                    source.as_bytes(),
                )
            })
            .collect(),
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: Default::default(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn run(source: &str, expected: i64) {
    let artifact = compile(&[("visibility@1", "src/main.glorious", source)])
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .artifact
        .unwrap();
    assert_eq!(artifact.run_i64().unwrap(), expected);
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        expected
    );
}

#[test]
fn scanner_preserves_visibility_scope_and_rejects_unknown_restrictions() {
    let package = PackageKey("visibility@1".into());
    let scan = |source: &str| {
        let lexed =
            grandiose_stage0::LexedFile::lex(FileKey::new(&package, "src/main.glorious"), source);
        DeclarationScan::scan(&lexed, source)
    };
    let parsed = scan(
        "fn a() {} pub(super) fn b() {} pub(crate) unsafe fn c() {} pub fn d() {} pub(crate) use crate::a;",
    );
    assert!(parsed.diagnostics.is_empty(), "{parsed:?}");
    assert_eq!(
        parsed
            .declarations
            .iter()
            .map(|declaration| declaration.visibility)
            .collect::<Vec<_>>(),
        [
            Visibility::Private,
            Visibility::Super,
            Visibility::Crate,
            Visibility::Public,
            Visibility::Crate
        ]
    );
    for restriction in ["", "self", "unknown", "crate,super", "crate::nested"] {
        let parsed = scan(&format!("pub({restriction}) fn denied() {{}}"));
        assert!(
            parsed
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G2005"),
            "{parsed:?}"
        );
        assert!(
            parsed
                .declarations
                .iter()
                .all(|declaration| !declaration.visibility.is_public())
        );
    }
}

#[test]
fn restricted_items_modules_imports_and_inherent_functions_use_module_scopes() {
    run("pub mod region {
        pub mod owner {
            pub(super) mod nested { pub fn answer() -> i64 { 2 } }
            pub(crate) fn base() -> i64 { 40 }
            pub struct Item {}
            impl Item { pub(super) fn local() -> i64 { 2 } pub(crate) fn wide() -> i64 { 40 } }
        }
        pub mod facade { pub(super) use super::owner::nested; pub(crate) use super::owner::base; }
        pub mod sibling { pub fn check() -> i64 { super::facade::nested::answer() + super::owner::Item::wide() } }
        pub fn local() -> i64 { owner::Item::local() }
    }
    pub fn main() -> i64 { region::sibling::check() + region::facade::base() + region::local() }", 84);
}

#[test]
fn private_record_fields_are_module_owned_even_in_one_source_file() {
    run(
        "pub mod owner {
        pub struct Record { value: i64 }
        pub fn make() -> Record { Record { value: 42 } }
        pub fn read(value: &Record) -> i64 { value.value }
        pub mod child { pub fn read() -> i64 { super::make().value } }
    }
    pub fn main() -> i64 { let value = owner::make(); owner::read(&value) + owner::child::read() }",
        84,
    );
    let prefix = "pub mod owner {
        pub struct Record { value: i64 }
        pub fn make() -> Record { Record { value: 42 } }
    } use owner::Record as Alias; ";
    for body in [
        "Alias { value: 42 }.value",
        "owner::make().value",
        "let mut item = owner::make(); item.value = 1; 42",
        "handle owner::make() { Alias { value } => value }",
    ] {
        let source = format!("{prefix} pub fn main() -> i64 {{ {body} }}");
        let error = compile(&[("visibility@1", "src/main.glorious", &source)]).unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.class == DiagnosticClass::Source
                    && diagnostic.message.contains("private field")),
            "{body}: {error:?}"
        );
    }
}

#[test]
fn restricted_fields_admit_their_scope_but_not_ancestors_or_other_packages() {
    run("pub mod region {
        pub mod owner {
            pub struct Record { pub(super) local: i64, pub(crate) wide: i64 }
            pub fn make() -> Record { Record { local: 2, wide: 40 } }
        }
        pub mod sibling { pub fn check() -> i64 { let item = super::owner::make(); item.local + item.wide } }
    }
    pub fn main() -> i64 { region::sibling::check() + region::owner::make().wide }", 82);
    for access in [
        "region::owner::local()",
        "region::owner::make().value",
        "region::owner::Item::local()",
        "region::owner::nested::answer()",
    ] {
        let source = format!(
            "pub mod region {{ pub mod owner {{
            pub(super) fn local() -> i64 {{ 42 }}
            pub struct Record {{ pub(super) value: i64 }}
            pub fn make() -> Record {{ Record {{ value: 42 }} }}
            pub struct Item {{}} impl Item {{ pub(super) fn local() -> i64 {{ 42 }} }}
            pub(super) mod nested {{ pub fn answer() -> i64 {{ 42 }} }}
        }} }} pub fn main() -> i64 {{ {access} }}"
        );
        let error = compile(&[("visibility@1", "src/main.glorious", &source)]).unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.class == DiagnosticClass::Source),
            "{access}: {error:?}"
        );
    }
    let library = "pub mod owner {
        pub(crate) fn local() -> i64 { 42 }
        pub struct Record { pub(crate) value: i64 }
        pub fn make() -> Record { Record { value: 42 } }
        pub struct Item {} impl Item { pub(crate) fn local() -> i64 { 42 } }
        pub(crate) mod nested { pub fn answer() -> i64 { 42 } }
    } pub(crate) use owner::local as alias;";
    for access in [
        "dep::owner::local()",
        "dep::owner::make().value",
        "dep::owner::Item::local()",
        "dep::owner::nested::answer()",
        "dep::alias()",
    ] {
        let source = format!("pub fn main() -> i64 {{ {access} }}");
        let error = compile(&[
            ("visibility@1", "src/main.glorious", &source),
            ("dep@1", "src/lib.glorious", library),
        ])
        .unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.class == DiagnosticClass::Source),
            "{access}: {error:?}"
        );
    }
}

#[test]
fn root_super_visibility_is_rejected_in_items_fields_and_members() {
    for declaration in [
        "pub(super) fn hidden() {}",
        "pub struct Record { pub(super) value: i64 }",
        "pub struct Item {} impl Item { pub(super) fn hidden() {} }",
    ] {
        let source = format!("{declaration} pub fn main() -> i64 {{ 42 }}");
        let error = compile(&[("visibility@1", "src/main.glorious", &source)]).unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == "G3004"),
            "{error:?}"
        );
    }
}

#[test]
fn restricted_reexports_cannot_widen_the_targets_authority() {
    for source in [
        "pub mod outer { pub mod inner { fn hidden() -> i64 { 42 } pub(super) use self::hidden as exposed; } } pub fn main() -> i64 { 42 }",
        "pub mod outer { pub(super) fn hidden() -> i64 { 42 } pub use self::hidden as exposed; } pub fn main() -> i64 { 42 }",
        "pub mod outer { pub mod inner { pub(super) fn hidden() -> i64 { 42 } pub(crate) use self::hidden as exposed; } } pub fn main() -> i64 { 42 }",
    ] {
        let error = compile(&[("visibility@1", "src/main.glorious", source)]).unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == "G3317"),
            "{error:?}"
        );
    }
    run(
        "pub(crate) fn base() -> i64 { 42 }
        pub mod outer { pub(crate) use crate::base as exposed; }
        pub fn main() -> i64 { outer::exposed() }",
        42,
    );
}

#[test]
fn field_authority_follows_modules_across_file_boundaries_and_public_aliases() {
    let root =
        "mod owner; pub struct Root { value: i64 } pub fn make() -> Root { Root { value: 42 } }
        pub fn main() -> i64 { owner::read() }";
    let owner = "pub fn read() -> i64 { crate::make().value }";
    let artifact = compile(&[
        ("visibility@1", "src/main.glorious", root),
        ("visibility@1", "src/owner/owner.glorious", owner),
    ])
    .unwrap()
    .artifact
    .unwrap();
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    let dependency = "pub mod owner {
        pub struct Record { value: i64 }
        pub fn make() -> Record { Record { value: 42 } }
    } pub use owner::Record as Alias; pub use owner::make;";
    for body in [
        "dep::make().value",
        "dep::Alias { value: 42 }.value",
        "handle dep::make() { dep::Alias { value } => value }",
    ] {
        let source = format!("pub fn main() -> i64 {{ {body} }}");
        let error = compile(&[
            ("visibility@1", "src/main.glorious", &source),
            ("dep@1", "src/lib.glorious", dependency),
        ])
        .unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.message.contains("private field")),
            "{body}: {error:?}"
        );
    }
}

#[test]
fn cached_revisions_do_not_retain_wider_item_or_field_authority() {
    for field in [false, true] {
        let source = |visibility: &str| {
            if field {
                format!(
                    "pub mod owner {{ pub struct Record {{ {visibility} value: i64 }} pub fn make() -> Record {{ Record {{ value: 42 }} }} }} pub fn main() -> i64 {{ owner::make().value }}"
                )
            } else {
                format!(
                    "pub mod owner {{ {visibility} fn answer() -> i64 {{ 42 }} }} pub fn main() -> i64 {{ owner::answer() }}"
                )
            }
        };
        let compiler = StageZeroCompiler::new();
        let public = source("pub(crate)");
        let parent = compiler
            .import_revision(
                request(&[("visibility@1", "src/main.glorious", &public)]),
                None,
            )
            .unwrap();
        assert_eq!(
            compiler
                .compile_revision(parent)
                .unwrap()
                .artifact
                .unwrap()
                .run_i64()
                .unwrap(),
            42
        );
        let private = source("");
        let child = compiler
            .import_revision(
                request(&[("visibility@1", "src/main.glorious", &private)]),
                Some(parent),
            )
            .unwrap();
        let error = compiler.compile_revision(child).unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.class == DiagnosticClass::Source),
            "{error:?}"
        );
        assert_eq!(
            compiler
                .compile_revision(parent)
                .unwrap()
                .artifact
                .unwrap()
                .run_i64()
                .unwrap(),
            42
        );
    }
}

#[test]
fn restricted_reexport_ambiguities_are_checked_without_a_body_use() {
    for visibility in ["pub(crate)", "pub(super)"] {
        let source = format!("pub mod outer {{
            pub mod left {{ pub fn answer() -> i64 {{ 40 }} }}
            pub mod right {{ pub fn answer() -> i64 {{ 2 }} }}
            pub mod facade {{ {visibility} use super::left::answer; {visibility} use super::right::answer; }}
        }} pub fn main() -> i64 {{ 42 }}");
        let error = compile(&[("visibility@1", "src/main.glorious", &source)]).unwrap_err();
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G3318"), "{error:?}");
    }
}
