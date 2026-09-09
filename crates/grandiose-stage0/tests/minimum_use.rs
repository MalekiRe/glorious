use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};
use std::collections::BTreeMap;

const TOKEN: &str = "#![no_std]\nenum Flag { Yes, No } struct Token {} impl Use<[1,1]> for Token {} fn consume(value: Token) -> i64 { let Token {} = value; 42 } ";

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("minimum-use@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"minimum-use")),
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
    let source = format!("{TOKEN}{body}");
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
    let source = format!("{TOKEN}{body}");
    for optimization in ["0", "2"] {
        let failure = StageZeroCompiler::new()
            .compile(request(&source, optimization))
            .expect_err(&source);
        assert!(
            failure
                .diagnostics()
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, "G5024" | "G5001" | "G5003" | "G4223")),
            "{source}\n{failure:#?}"
        );
    }
}

#[test]
fn named_linear_owners_transfer_or_deconstruct_without_byte_residents() {
    accepts("pub fn main() -> i64 { let value = Token {}; consume(value) }");
    accepts(
        "fn forward<T>(value: T) -> T { value } pub fn main() -> i64 { let value = forward(Token {}); consume(value) }",
    );
    accepts(
        "struct Wrapper { value: i64 } impl Use<[1,1]> for Wrapper {} pub fn main() -> i64 { let owner = Wrapper { value: 42 }; let Wrapper { value: result } = owner; result }",
    );
    accepts(
        "pub fn main() -> i64 { let value = Token {}; { let value = Token {}; consume(value); }; consume(value) }",
    );
    accepts(
        "pub fn main() -> i64 { let [left,right]: [Token;2] = [Token {},Token {}]; consume(left); consume(right) }",
    );
    accepts(
        "enum Maybe { None, Some(Token) } fn finish(value: Maybe) -> i64 { handle value { Maybe::None => 42, Maybe::Some(value) => consume(value) } } pub fn main() -> i64 { finish(Maybe::None) }",
    );
}

#[test]
fn returned_generic_closures_transfer_their_owned_captures() {
    accepts(
        "fn capture<T>(value: T) -> () -> T { () -> T { value } } pub fn main() -> i64 { consume(capture(Token {})()) }",
    );
    accepts(
        "fn capture<T>(value: T) -> () -> () -> T { () -> () -> T { () -> T { value } } } pub fn main() -> i64 { consume(capture(Token {})()()) }",
    );
    accepts(
        "trait Family { type Item; } impl Family for i64 { type Item = Token; } fn capture<T>(value: <T as Family>::Item) -> () -> <T as Family>::Item where T: Family { () -> <T as Family>::Item { value } } pub fn main() -> i64 { consume(capture<i64>(Token {})()) }",
    );
    accepts(
        "trait Fn {} impl Fn for Token {} fn capture<T>(value: T) -> () -> T where T: Fn { () -> T { value } } pub fn main() -> i64 { consume(capture(Token {})()) }",
    );
    rejects(
        "fn capture<T>(value: T) -> () -> T { let take = () -> T { value }; let discarded = value; take } pub fn main() -> i64 { consume(capture(Token {})()) }",
    );
}

#[test]
fn each_scope_and_branch_retains_its_own_minimum_use_debt() {
    accepts(
        "fn choose(value: Token, flag: Flag) -> i64 { handle flag { Flag::Yes => consume(value), Flag::No => consume(value) } } pub fn main() -> i64 { choose(Token {},Flag::Yes) }",
    );
    accepts(
        "fn choose(value: Token, flag: Flag) -> i64 { handle flag { Flag::Yes => (), Flag::No => () }; consume(value) } pub fn main() -> i64 { choose(Token {},Flag::Yes) }",
    );
    rejects(
        "fn choose(value: Token, flag: Flag) -> i64 { handle flag { Flag::Yes => consume(value), Flag::No => 42 } } pub fn main() -> i64 { choose(Token {},Flag::Yes) }",
    );
    rejects(
        "pub fn main() -> i64 { let value = Token {}; { let value = Token {}; 0 }; consume(value) }",
    );
    rejects("pub fn main() -> i64 { let value = Token {}; 42 }");
    rejects("pub fn main() -> i64 { let values: [Token;2] = [Token {},Token {}]; 42 }");
}

#[test]
fn borrowed_closure_captures_do_not_duplicate_the_referents_minimum_use_debt() {
    accepts("fn observe(value: &Token) -> i64 { 42 }
        pub fn main() -> i64 { let value = Token {}; let read = () -> i64 { observe(&value) }; read(); consume(value) }");
    accepts("fn observe(value: &mut Token) -> i64 { 42 }
        pub fn main() -> i64 { let mut value = Token {}; let read = () -> i64 { observe(&mut value) }; read(); consume(value) }");
    rejects("fn observe(value: &Token) -> i64 { 42 }
        pub fn main() -> i64 { let value = Token {}; let read = () -> i64 { observe(&value) }; read() }");
    rejects("fn observe(value: &mut Token) -> i64 { 42 }
        pub fn main() -> i64 { let mut value = Token {}; let read = () -> i64 { observe(&mut value) }; read() }");
}

#[test]
fn reads_helpers_overwrites_and_wildcards_cannot_erase_linear_owners() {
    rejects("pub fn main() -> i64 { let value = Token {}; let borrowed = &value; 42 }");
    rejects("pub fn main() -> i64 { let mut value = Token {}; value = Token {}; consume(value) }");
    rejects("pub fn main() -> i64 { let value = Token {}; value; 42 }");
    rejects("fn erase<T>(value: T) -> i64 { 42 } pub fn main() -> i64 { erase(Token {}) }");
    rejects(
        "fn forward<T>(value: T) -> T { value } pub fn main() -> i64 { forward(Token {}); 42 }",
    );
    rejects("fn make() -> Token { Token {} } pub fn main() -> i64 { handle make() { _ => 42 } }");
    rejects(
        "pub fn main() -> i64 { let value = Token {}; let Token {} = value; let Token {} = value; 42 }",
    );
    rejects(
        "enum Maybe { None, Some(Token) } pub fn main() -> i64 { let value = Maybe::None; 42 }",
    );
}

#[test]
fn affine_and_proven_zero_use_generics_remain_discardable() {
    accepts(
        "struct Affine {} impl Use<[0,1]> for Affine {} pub fn main() -> i64 { let unused = Affine {}; let empty: [Token;0] = []; 42 }",
    );
    accepts(
        "fn discard<T>(value: T) -> i64 where T: Use<[0,1]> { 42 } pub fn main() -> i64 { discard(42) }",
    );
    accepts(
        "struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {} impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = 42; } } pub fn main() -> i64 { let mut count = 41; { let value = Probe { count: &mut count }; () }; count }",
    );
}

#[test]
fn partial_moves_and_constructor_shells_keep_independent_obligations() {
    accepts(
        "struct Pair { left: Token, right: Token } pub fn main() -> i64 { let pair = Pair { left: Token {}, right: Token {} }; consume(move pair.left); consume(move pair.right) }",
    );
    accepts(
        "pub fn main() -> i64 { let mut value = Token {}; consume(move value); value = Token {}; consume(value) }",
    );
    rejects(
        "struct Pair { left: Token, right: Token } pub fn main() -> i64 { let pair = Pair { left: Token {}, right: Token {} }; consume(move pair.left); 42 }",
    );
    rejects(
        "struct Wrapper { value: i64 } impl Use<[1,1]> for Wrapper {} fn finish(value: Wrapper) -> i64 { let Wrapper { value: result } = value; result } pub fn main() -> i64 { let owner = Wrapper { value: 42 }; let Wrapper { value: result } = owner; finish(owner) }",
    );
    rejects(
        "struct Pair { left: Token, right: Token } pub fn main() -> i64 { let pair = Pair { left: Token {}, right: Token {} }; handle pair { Pair { left: item, right: _ } => consume(item) } }",
    );
}

#[test]
fn cleanup_bearing_nonlocal_exits_do_not_fabricate_positive_uses() {
    accepts(
        "pub fn main() -> i64 { label done { let value = Token {}; consume(value); transfer done 42 } }",
    );
    accepts(
        "pub fn main() -> i64 { let value = Token {}; label done { transfer done 42 }; consume(value) }",
    );
    rejects("pub fn main() -> i64 { label done { let value = Token {}; transfer done 42 } }");
    rejects(
        "effect Stop { stop() -> !; } pub fn main() -> i64 { handle { let value = Token {}; Stop::stop() } { Stop::stop() => 42 } }",
    );
    accepts(
        "effect Stop { stop(value: Token) -> !; } pub fn main() -> i64 { let payload = Token {}; handle Stop::stop(payload) { Stop::stop(value) => consume(value) } }",
    );
    rejects(
        "effect Stop { stop(value: Token) -> !; } pub fn main() -> i64 { let payload = Token {}; handle Stop::stop(payload) { Stop::stop(_) => 42 } }",
    );
    rejects(
        "trait Fn {} impl Fn for Token {} fn ignore<T>(value: T) -> i64 where T: Fn { 42 } pub fn main() -> i64 { ignore(Token {}) }",
    );
    rejects(
        "trait Label {} impl Label for Token {} fn ignore<T>(value: T) -> i64 where T: Label { 42 } pub fn main() -> i64 { ignore(Token {}) }",
    );
}

#[test]
fn canceling_a_continuation_cannot_destroy_its_linear_residents() {
    rejects(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Token {}; Ask::ask(); consume(value) } { Ask::ask() with _ => 42 } }",
    );
    accepts(
        "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Token {}; Ask::ask(); consume(value) } { Ask::ask() => 0 } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { let value = Token {}; handle { Ask::ask(); consume(value) } { Ask::ask() with _ => 42 } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } fn ask() -> i64 / Ask { Ask::ask() } pub fn main() -> i64 { handle { let value = Token {}; ask(); consume(value) } { Ask::ask() with _ => 42 } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } fn pair(value: Token, answer: i64) -> i64 { consume(value) } pub fn main() -> i64 { handle { let value = Token {}; pair(value, Ask::ask()) } { Ask::ask() with _ => 42 } }",
    );
    rejects(
        "pub fn main() -> i64 { label done { let value = Token {}; let pair = (value, transfer done 42); 42 } }",
    );
    accepts(
        "effect Ask { [0,1] ask() -> i64; } fn pair(value: Token, answer: i64) -> i64 { consume(value) } pub fn main() -> i64 { pair(Token {}, handle Ask::ask() { Ask::ask() with _ => 0 }) }",
    );
    accepts(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { let value = Token {}; handle Ask::ask() { Ask::ask() with _ => consume(value) } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { let value = Token {}; let flag = Flag::No; handle { handle flag { Flag::Yes => Ask::ask(), Flag::No => 0 } } { Ask::ask() with _ => consume(value) } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } fn invoke<F>(body: F) -> i64 / Ask where F: Fn<(), Output = i64, Effects = {Ask}> { let value = Token {}; body(); consume(value) } pub fn main() -> i64 { handle invoke(() -> i64 / Ask { Ask::ask() }) { Ask::ask() with _ => 42 } }",
    );
    accepts(
        "fn invoke<F>(body: F) -> i64 where F: Fn<(), Output = i64> { let value = Token {}; body(); consume(value) } pub fn main() -> i64 { invoke(() -> i64 { 0 }) }",
    );
    accepts(
        "effect Ask { [0,1] ask(answer: i64) -> i64; } fn ask(answer: i64) -> i64 / Ask { Ask::ask(answer) } pub fn main() -> i64 { handle { let value = Token {}; label done { ask(transfer done 0) }; consume(value) } { Ask::ask(answer) with _ => 0 } }",
    );
    accepts(
        "effect Ask { [0,1] ask(answer: i64) -> i64; } pub fn main() -> i64 { handle { let value = Token {}; label done { Ask::ask(transfer done 0) }; consume(value) } { Ask::ask(answer) with _ => 0 } }",
    );
}

#[test]
fn only_manifest_bound_abort_has_a_no_cleanup_disposition() {
    let source = format!(
        "{TOKEN} pub fn halt_machine() -> !; pub fn main() -> i64 {{ let value = Token {{}}; halt_machine() }}"
    );
    for optimization in ["0", "2"] {
        let mut request = request(&source, optimization);
        request.runtime_manifest = Some(grandiose_stage0::RuntimeManifestInput {
            standard_library: request.root_package.clone(),
            host_imports: vec![],
            selectors: vec![grandiose_stage0::PrimitiveSelector {
                role: grandiose_stage0::PrimitiveRole::Abort,
                module_path: "crate".into(),
                name: "halt_machine".into(),
            }],
        });
        let artifact = StageZeroCompiler::new()
            .compile(request)
            .unwrap()
            .artifact
            .unwrap();
        assert!(matches!(
            artifact.run_i64(),
            Err(grandiose_stage0::VmArtifactError::Trap)
        ));
        assert!(matches!(
            decode_and_verify_program(&artifact.canonical_bytes())
                .unwrap()
                .run_i64(),
            Err(grandiose_stage0::VmArtifactError::Trap)
        ));
    }
    rejects(
        "fn __g1_abort() -> i64 { 42 } pub fn main() -> i64 { let value = Token {}; __g1_abort() }",
    );
}

#[test]
fn failed_library_insertion_returns_the_exact_linear_input() {
    let source = r#"use std::*;
        struct Token {} impl Use<[1,1]> for Token {}
        fn finish(value: Vec<Token>) -> i64 {
            handle Vec::finish_empty(value) {
                Result::Ok(_) => 42,
                Result::Err(value) => finish(value),
            }
        }
        pub fn main() -> i64 {
            let mut values: Vec<Token> = Vec::new();
            let result = Vec::insert(&mut values, 1, Token {});
            handle result {
                Result::Err(Rejected { value: Token {}, error: BoundsError { index: index, length: length } }) => {
                    finish(values) + as<i64>(index) + as<i64>(length) - 1
                },
                Result::Ok(_) => finish(values),
            }
        }
    "#;
    for optimization in ["0", "2"] {
        let mut request = request(source, optimization);
        let library = grandiose_stage0::service::STANDARD_LIBRARY_FRAGMENTS
            .iter()
            .filter(|(path, _)| {
                matches!(
                    *path,
                    "src/lib.glorious" | "src/foundation.glorious" | "src/memory.glorious"
                )
            })
            .map(|(_, source)| *source)
            .collect::<Vec<_>>()
            .join("\n");
        request.sources.push(SourceInput::new(
            PackageKey("std@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            library.as_bytes(),
        ));
        let artifact = StageZeroCompiler::new()
            .compile(request)
            .unwrap()
            .artifact
            .unwrap();
        // SAFETY: locally compiled library source owns its raw storage contract.
        assert_eq!(
            unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(),
            42
        );
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        assert_eq!(
            unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(),
            42
        );
    }
}
