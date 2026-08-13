use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, ModuleGraph,
    PackageKey, SourceInput,
};

fn world(files: &[(&str, &[u8])]) -> grandiose_stage0::NormalizedInputWorld {
    let package = PackageKey("modules@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity {
            compiler: Digest::of_bytes(b"stage0-module-test"),
            language_generation: 1,
            query_generation: 1,
            interface_generation: 1,
            cache_generation: 1,
            bytecode_generation: 1,
            verifier_generation: 1,
        },
        mode: CompilationMode::Check,
        root_package: package.clone(),
        sources: files
            .iter()
            .map(|(path, source)| {
                SourceInput::new(package.clone(), LogicalPath::parse(*path).unwrap(), *source)
            })
            .collect(),
        target: "g1-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
    .normalize()
    .unwrap()
}

#[test]
fn module_graph_follows_explicit_external_module_declarations() {
    let world = world(&[
        ("src/main.glorious", b"mod parser; pub fn main() { () }"),
        ("src/parser/parser.glorious", b"pub fn parse() { () }"),
    ]);
    let graph = ModuleGraph::build(&world, &PackageKey("modules@0.1.0".into()));
    assert!(graph.diagnostics.is_empty(), "{:#?}", graph.diagnostics);
    assert_eq!(graph.modules.len(), 2);
    assert_eq!(graph.modules[&graph.root].children[0].path, "crate::parser");
}

#[test]
fn module_graph_reports_missing_and_unclaimed_supplied_modules() {
    let world = world(&[
        ("src/main.glorious", b"mod parser;"),
        ("src/extra/extra.glorious", b"fn extra() { () }"),
    ]);
    let graph = ModuleGraph::build(&world, &PackageKey("modules@0.1.0".into()));
    let codes = graph
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<Vec<_>>();
    assert!(codes.contains(&"G3103"));
    assert!(codes.contains(&"G3104"));
}

#[test]
fn module_graph_indexes_nested_inline_modules_in_their_lexical_source() {
    let world = world(&[(
        "src/main.glorious",
        b"mod outer { mod inner { pub fn answer() { 42 } } } pub fn main() { outer::inner::answer() }",
    )]);
    let graph = ModuleGraph::build(&world, &PackageKey("modules@0.1.0".into()));
    assert!(graph.diagnostics.is_empty(), "{:#?}", graph.diagnostics);
    assert!(graph.modules.contains_key(&grandiose_stage0::ModuleKey {
        package: PackageKey("modules@0.1.0".into()),
        path: "crate::outer".into(),
    }));
    let inner = grandiose_stage0::ModuleKey {
        package: PackageKey("modules@0.1.0".into()),
        path: "crate::outer::inner".into(),
    };
    let inner_node = graph.modules.get(&inner).expect("nested inline module");
    assert_eq!(inner_node.file, graph.modules[&graph.root].file);
    assert_eq!(
        inner_node.interface.interface.definitions[0]
            .name
            .as_deref(),
        Some("answer")
    );
}
