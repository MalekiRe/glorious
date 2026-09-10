use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};
use std::collections::BTreeMap;

fn request(source: &str, level: &str) -> CompilationRequest {
    let package = PackageKey("nominal-contracts@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"nominal-contracts")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), level.into())]),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

fn accepts(source: &str) {
    for level in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(source, level))
            .unwrap_or_else(|error| panic!("O{level}: {source}\n{:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn erased_view_storage_requires_an_element_type_from_context() {
    let source = r#"#![no_std]
        struct View<'a,T> { storage: &'a mut (), length: i64 }
        fn length<T>(view: View<T>) -> i64 { view.length }
        fn reborrow<T>(items: &mut View<T>) -> i64 {
            VIEW_BINDING
            length(view)
        }
        pub fn main() -> i64 {
            let mut storage = ();
            let mut items = View<'_,i64> { storage: &mut storage, length: 42 };
            reborrow(&mut items)
        }
    "#;
    for binding in [
        "let view: View<'_,T> = View { storage: &mut *items.storage, length: items.length };",
        "let view = View<'_,T> { storage: &mut *items.storage, length: items.length };",
    ] {
        accepts(&source.replace("VIEW_BINDING", binding));
    }
    // Neither erased reference provenance nor a same-spelled enclosing T is
    // evidence for the fresh constructor argument. A scalar result cannot
    // constrain it either. This is the original sorting_swap source mistake.
    let unconstrained = source.replace("VIEW_BINDING",
        "let view = View { storage: &mut *items.storage, length: items.length };");
    for level in ["0", "2"] {
        let failure = StageZeroCompiler::new().compile(request(&unconstrained, level))
            .expect_err("erased storage cannot infer a phantom element type");
        assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4116"),
            "O{level}: {:#?}", failure.diagnostics());
    }
}

#[test]
fn nominal_field_projections_use_only_their_declaration_contract() {
    accepts(r#"#![no_std]
        trait Source { type Item; }
        struct S {}
        impl Source for S { type Item = i64; }
        struct Cache<I> where I: Source { item: <I as Source>::Item }
        enum Slot<I> where I: Source { Full(<I as Source>::Item) }
        fn take<I>(value: Cache<I>) -> <I as Source>::Item where I: Source {
            let Cache { item: item } = value; item
        }
        pub fn main() -> i64 {
            let item = take<S>(Cache<S> { item: 42 });
            handle Slot<S>::Full(item) { Slot::Full(item) => item }
        }
    "#);
}

#[test]
fn nominal_constraints_are_checked_even_without_projection_fields() {
    for body in [
        "pub fn main() -> i64 { let _ = Restricted<i64> { value: 42 }; 42 }",
        "fn bad(value: Restricted<i64>) -> i64 { 42 } pub fn main() -> i64 { 42 }",
        "type Bad = Restricted<i64>; pub fn main() -> i64 { 42 }",
    ] {
        let source = format!("#![no_std]\ntrait Mark {{}} struct Restricted<T> where T: Mark {{ value: T }} {body}");
        let failure = StageZeroCompiler::new().compile(request(&source, "0")).expect_err(&source);
        assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4303"), "{source}\n{failure:#?}");
    }
}

#[test]
fn nominal_constraints_do_not_leak_to_other_declarations() {
    let source = r#"#![no_std]
        trait Source { type Item; }
        struct Valid<I> where I: Source { item: <I as Source>::Item }
        struct Invalid<I> { item: <I as Source>::Item }
        pub fn main() -> i64 { 42 }
    "#;
    let failure = StageZeroCompiler::new().compile(request(source, "0")).expect_err("nominal contracts are lexical");
    assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4190"), "{failure:#?}");
}

#[test]
fn nested_nominal_and_outlives_requirements_cannot_be_erased() {
    for source in [
        "#![no_std]\ntrait Mark {} struct Inner<T> where T: Mark { value: T } struct Outer<T> { value: Inner<T> } pub fn main() -> i64 { 42 }",
        "#![no_std]\nstruct Hold<'a,T> where T: 'a { value: T } fn bad<'a>(value: &'a i64) -> Hold<'static,&'a i64> { Hold { value: value } } pub fn main() -> i64 { 42 }",
    ] {
        let failure = StageZeroCompiler::new().compile(request(source, "0")).expect_err("nested type application must establish its full contract");
        assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4303"), "{failure:#?}");
    }
    accepts(r#"#![no_std]
        trait Mark {} impl Mark for i64 {}
        struct Inner<T> where T: Mark { value: T }
        struct Outer<T> where T: Mark { value: Inner<T> }
        pub fn main() -> i64 { let Outer { value: Inner { value: value } } = Outer { value: Inner { value: 42 } }; value }
    "#);
}

#[test]
fn imported_nominal_bounds_retain_their_exact_trait_identity() {
    for ty in ["i64", "u8"] {
        let library = "#![no_std]\npub trait Mark {} pub impl Mark for i64 {} pub struct Boxed<T> where T: Mark { pub value: T }";
        let source = format!("#![no_std]\nuse boundlib::Boxed; pub fn main() -> i64 {{ let input: {ty} = 42; let Boxed {{ value: value }} = Boxed {{ value: input }}; 42 }}");
        let mut req = request(&source, "0");
        req.sources.push(SourceInput::new(PackageKey("boundlib@0.1.0".into()), LogicalPath::parse("src/lib.glorious").unwrap(), library.as_bytes()));
        let outcome = StageZeroCompiler::new().compile(req);
        if ty == "i64" {
            let artifact = outcome.unwrap_or_else(|error| panic!("{error:#?}")).artifact.unwrap();
            assert_eq!(artifact.run_i64().unwrap(), 42);
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        } else {
            let failure = outcome.expect_err("an imported nominal constraint cannot disappear");
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4303"), "{failure:#?}");
        }
    }
}

#[test]
fn nominal_associated_equalities_and_universal_bounds_are_instantiated() {
    accepts(r#"#![no_std]
        trait Source { type Item; }
        trait Mark {}
        struct S {}
        impl Source for S { type Item = i64; }
        impl<'a> Mark for &'a S {}
        struct Cache<T> where T: Source<Item=i64>, for<'a> &'a T: Mark { value: <T as Source>::Item }
        fn take<T>(value: Cache<T>) -> i64 where T: Source<Item=i64>, for<'a> &'a T: Mark {
            let Cache { value: value } = value; value
        }
        pub fn main() -> i64 { take<S>(Cache<S> { value: 42 }) }
    "#);
}

#[test]
fn nominal_wrong_equality_or_nonuniversal_evidence_is_rejected() {
    for implementation in [
        "impl Source for S { type Item = u8; } impl<'a> Mark for &'a S {}",
        "impl Source for S { type Item = i64; } impl Mark for &'static S {}",
    ] {
        let source = format!(r#"#![no_std]
            trait Source {{ type Item; }} trait Mark {{}} struct S {{}}
            {implementation}
            struct Cache<T> where T: Source<Item=i64>, for<'a> &'a T: Mark {{ value: i64 }}
            pub fn main() -> i64 {{ let Cache {{ value: value }} = Cache<S> {{ value: 42 }}; value }}
        "#);
        let failure = StageZeroCompiler::new().compile(request(&source, "0")).expect_err("nominal requirements must be proved at construction");
        assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4303"), "{failure:#?}");
    }
}

#[test]
fn generic_nominal_implementation_projects_through_its_lexical_bounds() {
    accepts(r#"#![no_std]
        trait Source { type Item; fn take(value: Self) -> <Self as Source>::Item; }
        struct S { item: i64 }
        impl Source for S {
            type Item = i64;
            fn take(value: Self) -> <Self as Source>::Item { let S { item: item } = value; item }
        }
        struct Wrapper<I> { inner: I }
        impl<I> Source for Wrapper<I> where I: Source {
            type Item = <I as Source>::Item;
            fn take(value: Self) -> <Self as Source>::Item {
                let Wrapper { inner: inner } = value;
                Source::take(inner)
            }
        }
        pub fn main() -> i64 { Source::take(Wrapper { inner: S { item: 42 } }) }
    "#);
}

#[test]
fn generic_nominal_implementation_forwards_its_selected_effect_row() {
    accepts(r#"#![no_std]
        effect Read { [1,1] read() -> i64; }
        trait Source {
            type Item;
            type Effects: EffectRow;
            fn take(value: Self) -> <Self as Source>::Item / { | <Self as Source>::Effects };
        }
        struct S {}
        impl Source for S {
            type Item = i64;
            type Effects = {Read};
            fn take(value: Self) -> <Self as Source>::Item / {Read} {
                let S {} = value; Read::read()
            }
        }
        struct Wrapper<I> { inner: I }
        impl<I> Source for Wrapper<I> where I: Source {
            type Item = <I as Source>::Item;
            type Effects = { | <I as Source>::Effects };
            fn take(value: Self) -> <Self as Source>::Item / { | <Self as Source>::Effects } {
                let Wrapper { inner: inner } = value;
                Source::take(inner)
            }
        }
        pub fn main() -> i64 {
            let source = Wrapper { inner: S {} };
            handle Source::take(source) {
                Read::read() with k => k(42)
            }
        }
    "#);
}

#[test]
fn generic_nominal_selection_cannot_invent_an_implementation_predicate() {
    let source = r#"#![no_std]
        trait Source { type Item; }
        struct Wrapper<I> { inner: I }
        impl<I> Source for Wrapper<I> where I: Source { type Item = <I as Source>::Item; }
        impl<I> Wrapper<I> {
            fn bad(value: Self) -> <Self as Source>::Item {
                let Wrapper { inner: inner } = value; inner
            }
        }
        pub fn main() -> i64 { 42 }
    "#;
    let failure = StageZeroCompiler::new().compile(request(source, "0"))
        .expect_err("a structural subject is not proof of its conditional implementation");
    assert!(failure.diagnostics().iter().any(|diagnostic|
        matches!(diagnostic.code, "G4303" | "G4190" | "G4110")), "{failure:#?}");
}

#[test]
fn generic_wrapper_inherits_methods_from_its_lexical_supertrait() {
    accepts(r#"#![no_std]
        trait Parent { fn read(value: &Self) -> i64; }
        trait Child: Parent {}
        struct S { item: i64 }
        impl Parent for S { fn read(value: &Self) -> i64 { value.item } }
        impl Child for S {}
        struct Wrapper<I> { inner: I }
        impl<I> Parent for Wrapper<I> where I: Child {
            fn read(value: &Self) -> i64 { Parent::read(&value.inner) }
        }
        pub fn main() -> i64 {
            let wrapper = Wrapper { inner: S { item: 42 } };
            let result = Parent::read(&wrapper);
            let Wrapper { inner: S { item: item } } = wrapper;
            result
        }
    "#);
}

#[test]
fn generic_wrapper_tail_result_uses_the_same_selected_type_as_its_body() {
    accepts(r#"#![no_std]
        trait Source { type Item; fn read(value: &mut Self) -> <Self as Source>::Item; }
        struct S { item: i64 }
        impl Source for S {
            type Item = i64;
            fn read(value: &mut Self) -> <Self as Source>::Item { value.item }
        }
        struct Wrapper<I> { inner: I, remaining: i64 }
        impl<I> Source for Wrapper<I> where I: Source {
            type Item = <I as Source>::Item;
            fn read(value: &mut Self) -> <Self as Source>::Item {
                handle value.remaining {
                    0 => Source::read(&mut value.inner),
                    _ => { (*value).remaining = 0; tail Source::read(value) },
                }
            }
        }
        pub fn main() -> i64 {
            let mut wrapper = Wrapper { inner: S { item: 42 }, remaining: 1 };
            let result = Source::read(&mut wrapper);
            let Wrapper { inner: S { item: item }, remaining: remaining } = wrapper;
            result
        }
    "#);
}
