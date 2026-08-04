use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases,
    compile_source_to_phases_with_options,
};
use grandiose_vm::{Artifact, Instruction, Value, Vm, verify};

fn function_id(artifact: &Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

fn function_code<'a>(artifact: &'a Artifact, name: &str) -> &'a [Instruction] {
    let function = &artifact.functions[function_id(artifact, name) as usize];
    &artifact.code[function.code_start as usize..(function.code_start + function.code_len) as usize]
}

fn assert_direct_tail_call(artifact: &Artifact, caller: &str, callee: &str) {
    let callee = function_id(artifact, callee);
    let code = function_code(artifact, caller);
    assert!(
        matches!(
            code.last(),
            Some(Instruction::TailCall { function, .. }) if *function == callee
        ),
        "{caller} bytecode: {code:#?}"
    );
    assert!(!code.iter().any(|instruction| matches!(
        instruction,
        Instruction::Call { .. } | Instruction::Return { .. }
    )));
}

#[test]
fn direct_tail_positions_form_in_core_mir_and_bytecode_deterministically() {
    let source = r#"
        answer() -> i64 { 42 }
        relay() -> i64 { answer() }
        noop() -> { () }
        relay_unit() -> { noop() }
        nested() -> i64 { { answer() } }
        forever() -> ! { forever() }
        main() -> { () }
    "#;
    let options = CompileOptions {
        optimization_level: OptimizationLevel::O0,
    };
    let first =
        compile_source_to_phases_with_options("direct-tail.glorious", source, options).unwrap();
    let second =
        compile_source_to_phases_with_options("direct-tail.glorious", source, options).unwrap();
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    assert!(first.core.canonical_text().contains("tail-call fn#"));
    assert!(first.mir.canonical_text().contains("TailCall"));
    for (caller, callee) in [
        ("relay", "answer"),
        ("relay_unit", "noop"),
        ("nested", "answer"),
        ("forever", "forever"),
    ] {
        assert_direct_tail_call(&first.artifact, caller, callee);
    }
    let verified = verify(first.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified.clone())
            .run(function_id(&first.artifact, "relay"), vec![])
            .unwrap(),
        Value::I64(42)
    );
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&first.artifact, "relay_unit"), vec![])
            .unwrap(),
        Value::Unit
    );
}

#[test]
fn tail_calls_protect_must_move_arguments_and_clean_safe_affine_remainders() {
    let source = r#"
        struct Token { marker: i64 }
        struct Scratch { marker: i64 }
        impl Use<[1,1]> for Token {}
        impl Use<[0,1]> for Scratch {}
        token_identity(value: Token) -> Token { move value }
        relay(value: Token) -> Token { token_identity(move value) }
        leaf() -> i64 { 42 }
        cleanup_safe(unused: Scratch) -> i64 { leaf() }
        answer() -> i64 {
            let token = relay(Token { marker: 42 });
            let Token { marker } = token;
            marker
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("owned-tail.glorious", source).unwrap();
    assert_direct_tail_call(&phases.artifact, "relay", "token_identity");
    assert_direct_tail_call(&phases.artifact, "cleanup_safe", "leaf");
    let cleanup = function_code(&phases.artifact, "cleanup_safe");
    assert!(matches!(
        cleanup.first(),
        Some(Instruction::Drop { register: 1 })
    ));
    let relay = function_code(&phases.artifact, "relay");
    assert!(matches!(
        relay.first(),
        Some(Instruction::Move { src: 1, .. })
    ));
    let verified = verify(phases.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&phases.artifact, "answer"), vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn observable_drop_and_reference_cleanup_keep_ordinary_call_return_order() {
    let source = r#"
        struct Guard { marker: i64 }
        impl Use<[0,1]> for Guard {}
        impl Drop for Guard { drop(&mut self) -> { self.marker; () } }
        leaf() -> i64 { 42 }
        guarded(unused: Guard) -> i64 { leaf() }
        borrowed(value: &i64) -> i64 { leaf() }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases_with_options(
        "tail-fallback.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O0,
        },
    )
    .unwrap();
    for name in ["guarded", "borrowed"] {
        let code = function_code(&phases.artifact, name);
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::Call { .. })),
            "{name} bytecode: {code:#?}"
        );
        assert!(matches!(code.last(), Some(Instruction::Return { .. })));
        assert!(
            !code
                .iter()
                .any(|instruction| matches!(instruction, Instruction::TailCall { .. }))
        );
    }
    verify(phases.artifact).unwrap();
}

#[test]
fn outward_effectful_direct_tail_call_preserves_the_handler_delimiter() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        leaf() -> i64 / {Ask} { perform Ask::ask() }
        forward() -> i64 / {Ask} { leaf() }
        test() -> i64 {
            handle { forward() } { Ask::ask() with k => resume(k, 42) }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("effect-tail.glorious", source).unwrap();
    assert_direct_tail_call(&phases.artifact, "forward", "leaf");
    let forward = &phases.artifact.functions[function_id(&phases.artifact, "forward") as usize];
    let ask = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Ask")
        .expect("missing source protocol `Ask`") as u32;
    assert_eq!(forward.outward_protocols, [ask]);
    let verified = verify(phases.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&phases.artifact, "test"), vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn compiled_deep_forwarding_chain_executes_with_frame_replacement() {
    const DEPTH: usize = 1024;
    let mut source = String::new();
    for index in 0..DEPTH {
        source.push_str(&format!("step{index}() -> i64 {{ step{}() }}\n", index + 1));
    }
    source.push_str(&format!(
        "step{DEPTH}() -> i64 {{ 42 }}\nmain() -> {{ () }}\n"
    ));
    let phases = compile_source_to_phases("deep-tail-chain.glorious", &source).unwrap();
    for index in 0..DEPTH {
        assert_direct_tail_call(
            &phases.artifact,
            &format!("step{index}"),
            &format!("step{}", index + 1),
        );
    }
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&phases.artifact, "step0"), vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn externally_rooted_unique_reference_recursion_tail_transfers_at_every_level() {
    let source = r#"
        effect LoopCase { inspect(value: Bool) -> !; }
        walk(value: &mut i64, remaining: usize) -> i64 {
            handle perform LoopCase::inspect(remaining == 0) {
                LoopCase::inspect(Result::Ok(_)) => *value,
                LoopCase::inspect(Result::Err(_)) =>
                    walk(move value, remaining - 1)
            }
        }
        run() -> i64 {
            let value = 42;
            walk(&mut value, 100000)
        }
        main() -> () { run(); () }
    "#;

    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "unique-reference-tail.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let walk = function_id(&phases.artifact, "walk");
        let mut ordinary_recursive_edges = 0;
        let mut tail_recursive_edges = 0;
        for generated in phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$handler$"))
        {
            for instruction in &phases.artifact.code[generated.code_start as usize
                ..(generated.code_start + generated.code_len) as usize]
            {
                match instruction {
                    Instruction::Call { function, .. } if *function == walk => {
                        ordinary_recursive_edges += 1;
                    }
                    Instruction::TailCall { function, .. } if *function == walk => {
                        tail_recursive_edges += 1;
                    }
                    _ => {}
                }
            }
        }
        assert_eq!(
            ordinary_recursive_edges, 0,
            "unique-reference recursion retained Call at {optimization_level:?}"
        );
        assert!(
            tail_recursive_edges >= 1,
            "unique-reference recursion did not form TailCall at {optimization_level:?}"
        );
        let verified = verify(phases.artifact.clone()).unwrap();
        assert_eq!(
            Vm::new(verified)
                .run(function_id(&phases.artifact, "run"), vec![])
                .unwrap(),
            Value::I64(42),
            "deep unique-reference recursion grew frames at {optimization_level:?}"
        );
    }
}

#[test]
fn reference_tail_proof_rejects_live_loans_returns_and_leftover_reference_owners() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        leaf() -> i64 { 42 }
        consume(value: &mut i64) -> i64 { *value }
        ref_identity<'a>(value: &'a i64) -> &'a i64 { value }

        projected_loan(value: &mut Pair) -> i64 {
            let loan = &mut (*value).left;
            leaf()
        }
        suspended_parent(value: &mut i64) -> i64 {
            let child = &mut *value;
            leaf()
        }
        returns_reference<'a>(value: &'a i64) -> &'a i64 {
            ref_identity(value)
        }
        leftover_owner(first: &mut i64, second: &mut i64) -> i64 {
            consume(move first)
        }
        main() -> () { () }
    "#;
    let phases = compile_source_to_phases_with_options(
        "reference-tail-negative.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O0,
        },
    )
    .unwrap();

    for name in [
        "projected_loan",
        "suspended_parent",
        "returns_reference",
        "leftover_owner",
    ] {
        let code = function_code(&phases.artifact, name);
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::Call { .. })),
            "{name} must retain an ordinary Call; bytecode: {code:#?}"
        );
        assert!(
            !code
                .iter()
                .any(|instruction| matches!(instruction, Instruction::TailCall { .. })),
            "{name} unsafely formed a TailCall"
        );
    }
    verify(phases.artifact).unwrap();

    let errors = compile_source_to_phases(
        "ambiguous-reference-tail.glorious",
        r#"
            struct Two<'a> { first: &'a i64, second: &'a i64 }
            pass<'a>(value: Two<'a>) -> Two<'a> { move value }
            ambiguous<'a>(first: &'a i64, second: &'a i64) -> Two<'a> {
                pass(Two { first: first, second: second })
            }
            main() -> () { () }
        "#,
    )
    .expect_err("two independent reference origins must remain ambiguous");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("reference")
                || error.message.contains("loan")
                || error.message.contains("aggregate")
        }),
        "{errors:#?}"
    );
}
