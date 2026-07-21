use grandiose::compile_source_to_bytecode;
use grandiose_vm::verify;

#[test]
fn lexical_generic_parameters_shadow_same_named_global_aliases() {
    let source = r#"
        type A = Text;
        type E = Text;
        type F = Text;

        choose<A, E, F>(answer: A, evidence: E, fallback: F) -> A {
            evidence;
            fallback;
            answer
        }

        answer() -> i64 { choose(42, "evidence", ()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("generic-alias-shadowing.gr", source)
        .expect("lexical generic binders must win over global aliases");
    verify(artifact).unwrap();
}
