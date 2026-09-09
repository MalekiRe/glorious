use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};
use std::collections::BTreeMap;

const TYPES: &str = r#"#![no_std]
    struct Item { value: i64 }
    impl Use<[0,1]> for Item {}
    trait Mark: Use<[0,1]> {}
    impl Mark for Item {}
    struct Packet<T> { head: T, tail: i64 }
    impl<T> Use<[0,1]> for Packet<T> where T: Use<[0,1]> {}
    impl<T> Drop for Packet<T> where T: Mark { drop(&mut self) -> {} }
    fn read(value: Item) -> i64 { let Item { value: result } = value; result }
"#;

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("conditional-drop@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"conditional-drop")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), optimization.into())]),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn accepts(body: &str) {
    let source = format!("{TYPES}{body}");
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new()
            .compile(request(&source, optimization))
            .unwrap_or_else(|error| panic!("{source}\n{error:#?}"))
            .artifact
            .unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(
            decode_and_verify_program(&artifact.canonical_bytes())
                .unwrap()
                .run_i64()
                .unwrap(),
            42
        );
    }
}

fn rejects(body: &str) {
    let source = format!("{TYPES}{body}");
    for optimization in ["0", "2"] {
        let result = StageZeroCompiler::new().compile(request(&source, optimization));
        let Err(failure) = result else {
            panic!("custom-Drop owner was opened by safe source:\n{source}");
        };
        assert!(
            failure
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == "G4188"),
            "{source}\n{failure:#?}"
        );
    }
}

#[test]
fn selected_drop_protects_implicit_and_nested_owned_projections() {
    rejects(
        "pub fn main() -> i64 { let packet = Packet { head: Item { value: 42 }, tail: 0 }; read(packet.head) }",
    );
    rejects(
        "struct Inner { item: Item } impl Mark for Inner {} pub fn main() -> i64 { let packet = Packet { head: Inner { item: Item { value: 42 } }, tail: 0 }; read(move packet.head.item) }",
    );
    rejects(
        "pub fn main() -> i64 { let packet = Packet { head: Item { value: 42 }, tail: 0 }; let Item { value: result } = packet.head; result }",
    );
    accepts(
        "pub fn main() -> i64 { let packet = Packet { head: Item { value: 42 }, tail: 0 }; packet.head.value }",
    );
    accepts("pub fn main() -> i64 { let packet = Packet { head: 42, tail: 0 }; move packet.head }");
}

#[test]
fn nested_constructor_patterns_cannot_open_selected_drop_shells() {
    rejects(
        "pub fn main() -> i64 { let packet = Packet { head: Item { value: 42 }, tail: 0 }; let (Packet { head: item, tail: _ },) = (packet,); read(item) }",
    );
    rejects(
        "pub fn main() -> i64 { let packet = Packet { head: Item { value: 42 }, tail: 0 }; let [Packet { head: item, tail: _ }]: [Packet<Item>;1] = [packet]; read(item) }",
    );
    rejects(
        "effect Stop { stop(value: Packet<Item>) -> !; } pub fn main() -> i64 { let packet = Packet { head: Item { value: 42 }, tail: 0 }; handle Stop::stop(packet) { Stop::stop(Packet { head: item, tail: _ }) => read(item) } }",
    );
    accepts(
        "pub fn main() -> i64 { let packet = Packet { head: Item { value: 42 }, tail: 0 }; let item = &packet.head; item.value }",
    );
}

#[test]
fn generic_templates_do_not_treat_unproved_drop_conditions_as_absent() {
    rejects(
        "fn peel<T>(packet: Packet<T>) -> T where T: Use<[0,1]> { move packet.head } pub fn main() -> i64 { read(peel(Packet { head: Item { value: 42 }, tail: 0 })) }",
    );
    rejects(
        "trait Family { type Item; } impl Family for i64 { type Item = Item; } fn peel<T>(packet: Packet<<T as Family>::Item>) -> <T as Family>::Item where T: Family, <T as Family>::Item: Use<[0,1]> { move packet.head } pub fn main() -> i64 { read(peel<i64>(Packet { head: Item { value: 42 }, tail: 0 })) }",
    );
    accepts(
        "trait Family { type Item; } impl Family for i64 { type Item = i64; } fn peel(packet: Packet<<i64 as Family>::Item>) -> i64 { move packet.head } pub fn main() -> i64 { peel(Packet { head: 42, tail: 0 }) }",
    );
    rejects(
        "trait Family { type Item; } impl Family for i64 { type Item = Item; } fn peel(packet: Packet<<i64 as Family>::Item>) -> Item { move packet.head } pub fn main() -> i64 { read(peel(Packet { head: Item { value: 42 }, tail: 0 })) }",
    );
    accepts(
        "trait Family { type Item; } impl Family for i64 { type Item = i64; } fn peel<T>(packet: Packet<<T as Family>::Item>) -> i64 where T: Family<Item = i64> { move packet.head } pub fn main() -> i64 { peel<i64>(Packet { head: 42, tail: 0 }) }",
    );
}

#[test]
fn selected_hooks_run_once_across_normal_label_terminal_and_cancelled_cleanup() {
    let declarations = r#"
        struct Tracked<'a,T> { item: T, count: &'a mut i64 }
        impl<'a,T> Use<[0,1]> for Tracked<'a,T> where T: Use<[0,1]> {}
        impl<'a,T> Drop for Tracked<'a,T> where T: Mark {
            drop(&mut self) -> { *self.count = handle *self.count { 0 => 42, _ => 0 }; }
        }
        fn forward<'a,T>(value: Tracked<'a,T>) -> Tracked<'a,T> where T: Use<[0,1]> { value }
    "#;
    for body in [
        "pub fn main() -> i64 { let mut count = 0; let result = { let owner = forward(Tracked { item: Item { value: 41 }, count: &mut count }); owner.item.value }; handle result { 41 => count, _ => 0 } }",
        "pub fn main() -> i64 { let mut count = 0; let result = label done { let owner = Tracked { item: Item { value: 41 }, count: &mut count }; transfer done owner.item.value }; handle result { 41 => count, _ => 0 } }",
        "effect Stop { stop() -> !; } pub fn main() -> i64 { let mut count = 0; let result = handle { let owner = Tracked { item: Item { value: 41 }, count: &mut count }; Stop::stop() } { Stop::stop() => 41 }; handle result { 41 => count, _ => 0 } }",
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { let mut count = 0; let result = handle { let owner = Tracked { item: Item { value: 41 }, count: &mut count }; Ask::ask(); 0 } { Ask::ask() with _ => 41 }; handle result { 41 => count, _ => 0 } }",
    ] {
        accepts(&format!("{declarations}{body}"));
    }
}

#[test]
fn unselected_hooks_allow_whole_element_transfers_and_nested_patterns() {
    accepts(
        "pub fn main() -> i64 { let packet = Packet { head: 42, tail: 0 }; let (Packet { head: result, tail: _ },) = (packet,); result }",
    );
    accepts(
        "pub fn main() -> i64 { let values: [Packet<i64>;1] = [Packet { head: 42, tail: 0 }]; let [Packet { head: result, tail: _ }] = values; result }",
    );
    accepts(
        "pub fn main() -> i64 { let values: [Packet<Item>;1] = [Packet { head: Item { value: 42 }, tail: 0 }]; let [packet] = values; packet.head.value }",
    );
    rejects(
        "struct Empty {} impl Use<[0,1]> for Empty {} impl Drop for Empty { drop(&mut self) -> {} } pub fn main() -> i64 { let [Empty {}]: [Empty;1] = [Empty {}]; 42 }",
    );
}

#[test]
fn frozen_placeflow_rechecks_custom_drop_without_source_diagnostics() {
    use grandiose_stage0::{
        BodySyntax, DeclarationScan, DefinitionIndex, ElaboratedInterface, FileKey, InterfaceSet,
        LexedFile, PlaceFlow, TypedBody,
    };
    for body in [
        "pub fn main(packet: Packet<Item>) -> Item { packet.head }",
        "pub fn main(packet: Packet<Item>) -> Item { move packet.head }",
        "pub fn main(packet: Packet<Item>) -> Item { let (Packet { head: item, tail: _ },) = (packet,); item }",
    ] {
        let source = format!("{TYPES}{body}");
        let package = PackageKey("conditional-drop-frozen@0.1.0".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/main.glorious"), &source);
        let scan = DeclarationScan::scan(&lexed, &source);
        let interface = InterfaceSet::collect(package, "crate", &lexed, &source, &scan).interface;
        let signatures = ElaboratedInterface::elaborate(&interface);
        assert!(
            signatures.diagnostics.is_empty(),
            "{:?}",
            signatures.diagnostics
        );
        let definition = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some("main"))
            .unwrap();
        let syntax = BodySyntax::parse(&lexed, &source, definition.body.unwrap());
        let mut core = TypedBody::elaborate(
            definition,
            &syntax,
            &DefinitionIndex::from_interface(&interface),
            &signatures,
        );
        // A downstream checker must not rely on an earlier source diagnostic
        // having survived reconstruction or a compiler transformation.
        core.diagnostics.clear();
        let flow = PlaceFlow::analyze_with_interface(&core, &signatures);
        assert!(
            flow.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G4188"),
            "{source}\n{flow:#?}"
        );
    }
}
