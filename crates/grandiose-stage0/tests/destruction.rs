use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

const PROBE: &str = r#"
    use std::*;
    struct Probe<'a> { target: &'a mut i64 }
    impl<'a> Use<[0, 1]> for Probe<'a> {}
    impl<'a> Drop for Probe<'a> {
        drop(&mut self) -> { *self.target = *self.target + 1; }
    }
"#;

fn compile(body: &str) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    let source = format!("{PROBE}\n{body}");
    let package = PackageKey("destruction@0.1.0".into());
    let request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"source-destruction")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    };
    StageZeroCompiler::new().compile(request)
}

fn run(body: &str) -> i64 {
    let outcome = compile(body).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    program.run_i64().unwrap()
}

#[test]
fn replay_cannot_duplicate_a_live_affine_resident() {
    let outcome = compile(r#"
        struct Affine { value: i64 }
        impl Use<[0, 1]> for Affine {}
        effect Tick { [2, 2] tick() -> i64; }
        pub fn main() -> i64 {
            handle {
                let owned = Affine { value: 42 };
                Tick::tick();
                let consumed = move owned;
                consumed.value
            } {
                Tick::tick() with k => { k(1); k(2) }
            }
        }
    "#);
    assert!(matches!(outcome, Err(grandiose_stage0::ServiceError::Failed(_))), "replay accepted an affine capture");
}

#[test]
fn replay_cannot_duplicate_affine_residents_across_ordinary_calls() {
    for (computation, declarations) in [
        ("callee()", r#"
            fn callee() -> i64 / Tick {
                let owned = Affine { value: 42 };
                Tick::tick();
                let consumed = move owned;
                consumed.value
            }
        "#),
        (r#"{
            let owned = Affine { value: 42 };
            callee();
            let consumed = move owned;
            consumed.value
        }"#, "fn callee() -> i64 / Tick { Tick::tick() }"),
    ] {
        let outcome = compile(&format!(r#"
            struct Affine {{ value: i64 }}
            impl Use<[0, 1]> for Affine {{}}
            effect Tick {{ [2, 2] tick() -> i64; }}
            {declarations}
            pub fn main() -> i64 {{
                handle {computation} {{
                    Tick::tick() with k => {{ k(1); k(2) }}
                }}
            }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
            panic!("replay accepted an affine ordinary-call frame");
        };
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.message.contains("without Copy permission")),
            "replay failed for an unrelated reason: {diagnostics:?}");
    }
}

#[test]
fn replay_cannot_duplicate_an_affine_active_capture() {
    let outcome = compile(r#"
        struct Affine { value: i64 }
        impl Use<[0, 1]> for Affine {}
        effect Tick { [2, 2] tick() -> i64; }
        pub fn main() -> i64 {
            let owned = Affine { value: 42 };
            let pending = () -> i64 / Tick {
                Tick::tick();
                let consumed = move owned;
                consumed.value
            };
            handle pending() {
                Tick::tick() with k => { k(1); k(2) }
            }
        }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
        panic!("replay accepted an affine active capture");
    };
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.message.contains("without Copy permission")),
        "replay failed for an unrelated reason: {diagnostics:?}");
}

#[test]
fn array_elements_are_destroyed_by_runtime_loop() {
    assert_eq!(run(r#"
        fn finish(first: &mut i64, second: &mut i64) -> {
            let owners = [Probe { target: first }, Probe { target: second }];
            ()
        }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            finish(&mut first, &mut second);
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn nested_array_elements_are_destroyed_by_runtime_loops() {
    assert_eq!(run(r#"
        fn finish(first: &mut i64, second: &mut i64) -> {
            let owners = [[Probe { target: first }], [Probe { target: second }]];
            ()
        }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            finish(&mut first, &mut second);
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn empty_array_destruction_does_not_enter_element_cleanup() {
    assert_eq!(run(r#"
        struct Item { value: i64 }
        impl Use<[0, 1]> for Item {}
        impl Drop for Item { drop(&mut self) -> { () } }
        fn empty() -> Array<Item> { [] }
        pub fn main() -> i64 { let owners = empty(); 42 }
    "#), 42);
}

#[test]
fn uninvoked_closure_destroys_its_captured_array() {
    assert_eq!(run(r#"
        fn finish(target: &mut i64) -> {
            let owners = [Probe { target: target }];
            let pending = () -> i64 { let taken = move owners; 42 };
            ()
        }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#), 1);
}

#[test]
fn cancelled_array_cleanup_preserves_surviving_caller_storage() {
    assert_eq!(run(r#"
        effect Stop { [0, 1] stop() -> i64; }
        fn finish(target: &mut i64) -> i64 {
            let owners = [Probe { target: target }];
            handle Stop::stop() { Stop::stop() with _ => 0 }
        }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#), 1);
}

#[test]
fn owning_array_patterns_leave_only_residual_elements_for_cleanup() {
    assert_eq!(run(r#"
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let owners = [Probe { target: &mut first }, Probe { target: &mut second }];
                handle owners { [left, _] => (), _ => () };
                ()
            };
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn uninvoked_closure_destroys_its_moved_capture() {
    assert_eq!(run(r#"
        fn finish(target: &mut i64) -> {
            let owner = Probe { target: target };
            let pending = () -> i64 { let taken = move owner; 42 };
            ()
        }
        pub fn main() -> i64 {
            let mut count = 0;
            finish(&mut count);
            count
        }
    "#), 1);
}

#[test]
fn cancelled_capture_cleanup_preserves_checked_loans_into_surviving_callers() {
    for body in [
        "Stop::stop(); let taken = move owner; 42",
        "let taken = move owner; Stop::stop()",
        "{ let taken = move owner; () }; Stop::stop()",
    ] {
        let source = format!(r#"
            effect Stop {{ [0, 1] stop() -> i64; }}
            fn finish(target: &mut i64) -> i64 {{
                let owner = Probe {{ target: target }};
                let pending = () -> i64 / Stop {{ {body} }};
                handle pending() {{ Stop::stop() with _ => 0 }}
            }}
            pub fn main() -> i64 {{ let mut count = 0; finish(&mut count); count }}
        "#);
        assert_eq!(run(&source), 1, "{body}");
    }
}

#[test]
fn cancellation_cleanup_cannot_bypass_the_ordinary_call_depth_budget() {
    let outcome = compile(r#"
        effect Stop { [0, 1] stop() -> i64; }
        fn finish(target: &mut i64) -> i64 {
            let owner = Probe { target: target };
            let pending = () -> i64 / Stop { let taken = move owner; Stop::stop() };
            handle pending() { Stop::stop() with _ => 0 }
        }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#).unwrap();
    let artifact = outcome.artifact.unwrap();
    let program = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    assert_eq!(program.run_i64().unwrap(), 1);
    let limits = grandiose_stage0::VmExecutionLimits { max_call_depth: 3, ..Default::default() };
    assert!(matches!(program.run_i64_with_limits(limits),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 3 })));
}

#[test]
fn nonlocal_label_calls_destroy_owners_in_abandoned_ordinary_frames() {
    assert_eq!(run(r#"
        fn jump<L>(destination: L, target: &mut i64) -> ! where L: Label<i64> {
            let owner = Probe { target: target };
            destination(0)
        }
        fn finish(target: &mut i64) -> i64 {
            @done: i64 { jump(@done, target) }
        }
        pub fn main() -> i64 {
            let mut count = 0;
            finish(&mut count);
            count
        }
    "#), 1);
}

#[test]
fn nonlocal_label_calls_destroy_suspended_handler_clause_owners() {
    assert_eq!(run(r#"
        effect Ask { [1, 1] ask() -> i64; }
        fn protected<L>(destination: L) -> i64 / Ask where L: Label<i64> {
            let value = Ask::ask();
            destination(value)
        }
        fn handled<L>(destination: L, target: &mut i64) -> i64 where L: Label<i64> {
            handle protected(destination) {
                Ask::ask() with k => {
                    let owner = Probe { target: target };
                    k(0) + 1
                }
            }
        }
        fn finish(target: &mut i64) -> i64 {
            @done: i64 { handled(@done, target) }
        }
        pub fn main() -> i64 {
            let mut count = 0;
            finish(&mut count);
            count
        }
    "#), 1);
}

#[test]
fn nonlocal_label_calls_destroy_abandoned_suspended_computations() {
    let outcome = compile(r#"
        effect Ask { [0, 1] ask() -> i64; }
        fn protected(target: &mut i64) -> i64 / Ask {
            let owner = Probe { target: target };
            Ask::ask()
        }
        fn handled<L>(destination: L, target: &mut i64) -> i64 where L: Label<i64> {
            handle protected(target) {
                Ask::ask() with _ => destination(0)
            }
        }
        fn finish(target: &mut i64) -> i64 {
            @done: i64 { handled(@done, target) }
        }
        pub fn main() -> i64 {
            let mut count = 0;
            finish(&mut count);
            count
        }
    "#).unwrap();
    let artifact = outcome.artifact.unwrap();
    let program = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    assert_eq!(program.run_i64().unwrap(), 1);
    // The protected call fits in this budget, but its destructor requires
    // another frame. Abandonment may not bypass that ordinary call bound.
    let limits = grandiose_stage0::VmExecutionLimits { max_call_depth: 4, ..Default::default() };
    assert!(matches!(program.run_i64_with_limits(limits),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 4 })));
}

#[test]
fn lexical_leaves_destroy_abandoned_suspended_computations() {
    assert_eq!(run(r#"
        effect Ask { [0, 1] ask() -> i64; }
        fn protected(target: &mut i64) -> i64 / Ask {
            let owner = Probe { target: target };
            Ask::ask()
        }
        fn finish(target: &mut i64) -> i64 {
            label done {
                handle protected(target) {
                    Ask::ask() with _ => transfer done 0
                }
            }
        }
        pub fn main() -> i64 {
            let mut count = 0;
            finish(&mut count);
            count
        }
    "#), 1);
}

#[test]
fn suspended_computation_cleanup_preserves_its_transferred_operation_payload() {
    assert_eq!(run(r#"
        effect Ask<T> { [0, 1] ask(value: T) -> T; }
        fn protected<'a>(first: &'a mut i64, second: &'a mut i64) -> Probe<'a> / Ask<Probe<'a>> {
            let retained = Probe { target: first };
            Ask<Probe<'a>>::ask(Probe { target: second })
        }
        fn handled<'a, L>(destination: L, first: &'a mut i64, second: &'a mut i64) -> Probe<'a>
            where L: Label<Probe<'a>> {
            handle protected(first, second) {
                Ask<Probe<'a>>::ask(payload) with _ => destination(move payload)
            }
        }
        fn finish<'a>(first: &'a mut i64, second: &'a mut i64) -> Probe<'a> {
            @done: Probe<'a> { handled(@done, first, second) }
        }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            { let received = finish(&mut first, &mut second); () };
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn cancelling_nested_retained_computations_destroys_each_owned_branch() {
    assert_eq!(run(r#"
        effect Inner { [0, 1] ask() -> i64; }
        effect Outer { [0, 1] ask() -> i64; }
        fn protected(target: &mut i64) -> i64 / Inner {
            let owner = Probe { target: target };
            Inner::ask()
        }
        fn nested(first: &mut i64, second: &mut i64) -> i64 / Outer {
            handle protected(first) {
                Inner::ask() with _ => {
                    let owner = Probe { target: second };
                    Outer::ask()
                }
            }
        }
        fn finish(first: &mut i64, second: &mut i64) -> i64 {
            handle nested(first, second) { Outer::ask() with _ => 0 }
        }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            finish(&mut first, &mut second);
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn nonlocal_label_calls_destroy_transferred_parameters_in_abandoned_frames() {
    assert_eq!(run(r#"
        fn jump<'a, L>(destination: L, owner: Probe<'a>) -> ! where L: Label<i64> {
            destination(0)
        }
        fn relay<'a, L>(destination: L, owner: Probe<'a>) -> ! where L: Label<i64> {
            jump(destination, move owner)
        }
        fn finish(target: &mut i64) -> i64 {
            @done: i64 { relay(@done, Probe { target: target }) }
        }
        pub fn main() -> i64 {
            let mut count = 0;
            finish(&mut count);
            count
        }
    "#), 1);
}

#[test]
fn nonlocal_label_calls_preserve_transferred_owned_payloads() {
    assert_eq!(run(r#"
        fn jump<'a, L>(destination: L, owner: Probe<'a>) -> ! where L: Label<Probe<'a>> {
            destination(move owner)
        }
        fn finish<'a>(target: &'a mut i64) -> Probe<'a> {
            @done: Probe<'a> { jump(@done, Probe { target: target }) }
        }
        pub fn main() -> i64 {
            let mut count = 0;
            { let received = finish(&mut count); () };
            count
        }
    "#), 1);
}

#[test]
fn nonlocal_label_calls_return_residual_capture_ownership() {
    for body in [
        "exit(0); let taken = move owner; ()",
        "let taken = move owner; exit(0)",
        "{ let taken = move owner; () }; exit(0)",
    ] {
        assert_eq!(run(&format!(r#"
            fn jump<L>(destination: L, target: &mut i64) -> ! where L: Label<i64> {{
                let owner = Probe {{ target: target }};
                let pending = (exit: L) -> ! {{ {body} }};
                pending(destination)
            }}
            fn finish(target: &mut i64) -> i64 {{ @done: i64 {{ jump(@done, target) }} }}
            pub fn main() -> i64 {{ let mut count = 0; finish(&mut count); count }}
        "#)), 1, "{body}");
    }
}

#[test]
fn terminal_label_calls_in_closures_end_strict_evaluation_before_dead_suffixes() {
    for body in [
        "exit(0); let taken = move owner; 42",
        "let unreachable = exit(0); let taken = move owner; 42",
        "(exit(0), { let taken = move owner; 42 }); 42",
        "handle true { true => exit(0), false => 42 }; let taken = move owner; 42",
    ] {
        assert_eq!(run(&format!(r#"
            fn jump<L>(destination: L, target: &mut i64) -> i64 where L: Label<i64> {{
                let owner = Probe {{ target: target }};
                let pending = (exit: L) -> i64 {{ {body} }};
                pending(destination)
            }}
            fn finish(target: &mut i64) -> i64 {{ @done: i64 {{ jump(@done, target) }} }}
            pub fn main() -> i64 {{ let mut count = 0; finish(&mut count); count }}
        "#)), 1, "{body}");
    }
}

#[test]
fn terminal_call_operands_preserve_the_strict_prefix_and_skip_later_work() {
    assert_eq!(run(r#"
        fn touch(target: &mut i64) -> i64 { *target = *target + 10; 0 }
        fn sink(first: i64, second: i64, third: i64) -> i64 { 42 }
        fn jump<L>(destination: L, target: &mut i64) -> i64 where L: Label<i64> {
            let owner = Probe { target: target };
            let pending = (exit: L) -> i64 {
                sink(touch(&mut *owner.target), exit(0), touch(&mut *owner.target));
                let taken = move owner;
                42
            };
            pending(destination)
        }
        fn finish(target: &mut i64) -> i64 { @done: i64 { jump(@done, target) } }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#), 11);
}

#[test]
fn a_terminal_callee_expression_runs_before_its_call_arguments() {
    assert_eq!(run(r#"
        fn touch(target: &mut i64) -> i64 { *target = *target + 10; 0 }
        fn sink(value: i64) -> i64 { 42 }
        fn make<L>(exit: L) -> (i64) -> i64 where L: Label<i64> { exit(0); sink }
        fn jump<L>(destination: L, target: &mut i64) -> i64 where L: Label<i64> {
            let owner = Probe { target: target };
            let pending = (exit: L) -> i64 {
                make(exit)(touch(&mut *owner.target));
                let taken = move owner;
                42
            };
            pending(destination)
        }
        fn finish(target: &mut i64) -> i64 { @done: i64 { jump(@done, target) } }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#), 1);
}

#[test]
fn terminal_calls_only_end_the_selected_lazy_boolean_path() {
    // The destination belongs to the callback's own activation. A callback
    // retaining a label from its caller must be fused or rejected (§11); it
    // is not an eager compiler-known Boolean branch.
    for flag in [false, true] {
        for operator in ["and", "or"] {
            assert_eq!(run(&format!(r#"
                fn finish(target: &mut i64, flag: Bool) -> i64 {{
                    flag {operator} (() -> Bool {{
                        @done: Bool {{
                            let owner = Probe {{ target: target }};
                            @done(true);
                            *owner.target = *owner.target + 10;
                            false
                        }}
                    }});
                    42
                }}
                pub fn main() -> i64 {{ let mut count = 0; finish(&mut count, {flag}); count }}
            "#)), if flag == (operator == "and") { 1 } else { 0 }, "{flag} {operator}");
        }
    }
}

#[test]
fn terminal_first_completion_arm_does_not_erase_the_returning_arm() {
    for flag in [false, true] {
        assert_eq!(run(&format!(r#"
            fn jump<L>(destination: L, target: &mut i64, flag: Bool) -> i64 where L: Label<i64> {{
                let owner = Probe {{ target: target }};
                let pending = (exit: L) -> i64 {{
                    let result = handle flag {{ true => exit(0), false => 10 }};
                    *owner.target = *owner.target + result;
                    let taken = move owner;
                    42
                }};
                pending(destination)
            }}
            fn finish(target: &mut i64) -> i64 {{ @done: i64 {{ jump(@done, target, {flag}) }} }}
            pub fn main() -> i64 {{ let mut count = 0; finish(&mut count); count }}
        "#)), if flag { 1 } else { 11 }, "{flag}");
    }
}

#[test]
fn terminal_calls_in_ordinary_functions_end_the_source_block() {
    assert_eq!(run(r#"
        fn jump<L>(destination: L, target: &mut i64) -> i64 where L: Label<i64> {
            let owner = Probe { target: target };
            destination(0);
            42
        }
        fn finish(target: &mut i64) -> i64 { @done: i64 { jump(@done, target) } }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#), 1);
}

#[test]
fn completion_with_only_terminal_arms_has_no_value_join() {
    for flag in [false, true] {
        assert_eq!(run(&format!(r#"
            fn jump<L>(destination: L, target: &mut i64, flag: Bool) -> i64 where L: Label<i64> {{
                let owner = Probe {{ target: target }};
                let pending = (exit: L) -> i64 {{
                    let never_returned = handle flag {{ true => exit(1), false => exit(2) }};
                    let taken = move owner;
                    42
                }};
                pending(destination)
            }}
            fn finish(target: &mut i64) -> i64 {{ @done: i64 {{ jump(@done, target, {flag}) }} }}
            pub fn main() -> i64 {{ let mut count = 0; let result = finish(&mut count); result * 10 + count }}
        "#)), if flag { 11 } else { 21 }, "{flag}");
    }
}

#[test]
fn nonlocal_label_cleanup_cannot_bypass_the_ordinary_call_depth_budget() {
    let outcome = compile(r#"
        fn jump<L>(destination: L, target: &mut i64) -> ! where L: Label<i64> {
            let owner = Probe { target: target };
            destination(0)
        }
        fn finish(target: &mut i64) -> i64 { @done: i64 { jump(@done, target) } }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#).unwrap();
    let artifact = outcome.artifact.unwrap();
    let program = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    assert_eq!(program.run_i64().unwrap(), 1);
    let limits = grandiose_stage0::VmExecutionLimits { max_call_depth: 3, ..Default::default() };
    assert!(matches!(program.run_i64_with_limits(limits),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 3 })));
}

#[test]
fn closure_destruction_preserves_moved_and_retained_capture_states() {
    for action in [
        "pending(); ()",
        "let held = pending; held(); ()",
        "let pair = (pending, 42); ()",
        "let nested = () -> i64 { let held = move pending; held() }; ()",
        "let nested = () -> i64 { let held = move pending; held() }; nested(); ()",
    ] {
        assert_eq!(run(&format!(r#"
            fn finish(target: &mut i64) -> {{
                let owner = Probe {{ target: target }};
                let pending = () -> i64 {{ let taken = move owner; 42 }};
                {action}
            }}
            pub fn main() -> i64 {{ let mut count = 0; finish(&mut count); count }}
        "#)), 1, "{action}");
    }
    assert_eq!(run(r#"
        fn finish(target: &mut i64) -> {
            let owner = Probe { target: target };
            let observe = move (owner) { *owner.target };
            observe();
            observe();
            ()
        }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#), 1);
}

#[test]
fn replacing_a_copyable_closure_preserves_the_new_affine_capture_owner() {
    for action in ["pending(); ()", "let held = pending; held(); ()"] {
        assert_eq!(run(&format!(r#"
            fn finish(target: &mut i64) -> {{
                let owner = Probe {{ target: target }};
                let mut pending = () -> i64 {{ 42 }};
                pending = () -> i64 {{ let taken = move owner; 42 }};
                {action}
            }}
            pub fn main() -> i64 {{ let mut count = 0; finish(&mut count); count }}
        "#)), 1, "{action}");
    }
}

#[test]
fn indirect_entry_to_a_noncapturing_function_preserves_authoring_tail_recycling() {
    let artifact = compile(r#"
        fn count(value: i64) -> i64 {
            handle value == 0 { true => 42, false => count(value - 1) }
        }
        pub fn main() -> i64 { let callback = count; callback(1000) }
    "#).unwrap().artifact.unwrap();
    let program = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    let (result, profile) = program.run_i64_for_authoring(grandiose_stage0::VmExecutionLimits {
        max_call_depth: 64, ..Default::default()
    }).unwrap();
    assert_eq!(result, 42);
    assert_eq!(profile.recycled_tail_calls, 1000);
    assert!(profile.peak_call_depth < 64);
}

#[test]
fn returned_owned_closure_preserves_its_capture_until_the_destination_drops() {
    assert_eq!(run(r#"
        fn carry(callback: () -> i64) -> () -> i64 { move callback }
        fn finish(target: &mut i64) -> {
            let owner = Probe { target: target };
            let pending = move (owner) { *owner.target };
            let held = carry(move pending);
            held();
            ()
        }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#), 1);
    let rejected = compile(r#"
        fn carry(callback: () -> i64) -> () -> i64 { callback(); move callback }
        pub fn main() -> i64 { 42 }
    "#).unwrap_err();
    let grandiose_stage0::ServiceError::Failed(diagnostics) = rejected else { panic!("{rejected:?}"); };
    assert!(diagnostics.iter().any(|diagnostic|
        diagnostic.code == "G5013" && diagnostic.message.contains("combined demand")), "{diagnostics:#?}");
}

#[test]
fn borrowed_closure_captures_preserve_outer_storage_and_do_not_destroy_it() {
    assert_eq!(run(r#"
        pub fn main() -> i64 {
            let mut count = 0;
            { let set = () -> { count = 42; }; set(); set(); };
            count
        }
    "#), 42);
    assert_eq!(run(r#"
        fn finish(target: &mut i64) -> {
            let owner = Probe { target: target };
            { let observe = () -> i64 { *owner.target }; observe(); observe(); };
            ()
        }
        pub fn main() -> i64 { let mut count = 0; finish(&mut count); count }
    "#), 1);
}

#[test]
fn root_lowering_probes_preserve_lexical_owner_cleanup() {
    for result in ["42", "40 + 2", "produce()"] {
        assert_eq!(run(&format!(r#"
            fn produce() -> i64 {{ 42 }}
            fn finish(target: &mut i64) -> i64 {{
                let owner = Probe {{ target: target }};
                {result}
            }}
            pub fn main() -> i64 {{
                let mut count = 0;
                let result = finish(&mut count);
                handle count == 1 {{ true => result, false => 0 }}
            }}
        "#)), 42, "{result}");
    }
    for result in ["boolean(false) and { true }", "boolean(true) or { false }", "flag and { true }", "flag or { false }"] {
        assert_eq!(run(&format!(r#"
            fn boolean(value: Bool) -> Bool {{ value }}
            fn finish(target: &mut i64, flag: Bool) -> Bool {{
                let owner = Probe {{ target: target }};
                {result}
            }}
            pub fn main() -> i64 {{
                let mut count = 0;
                finish(&mut count, true);
                handle count == 1 {{ true => 42, false => 0 }}
            }}
        "#)), 42, "{result}");
    }
}

#[test]
fn lazy_boolean_value_joins_preserve_branch_and_enclosing_owner_cleanup() {
    for flag in [false, true] {
        assert_eq!(run(&format!(r#"
            fn finish(outer: &mut i64, inner: &mut i64, flag: Bool) -> Bool {{
                let enclosing = Probe {{ target: outer }};
                let selected = flag and {{
                    let branch = Probe {{ target: inner }};
                    true and {{ true }}
                }};
                selected or {{ false }}
            }}
            pub fn main() -> i64 {{
                let mut outer = 0;
                let mut inner = 0;
                finish(&mut outer, &mut inner, {flag});
                outer * 10 + inner
            }}
        "#)), 10 + i64::from(flag));
    }
}

#[test]
fn authoring_tail_calls_destroy_transferred_pattern_owners_exactly_once() {
    let outcome = compile(r#"
        enum Step<'a> { Next(Probe<'a>, i64), Done(i64) }
        fn step<'a>(probe: Probe<'a>, remaining: i64) -> Step<'a> {
            handle remaining == 0 {
                true => Step::Done(0),
                false => Step::Next(probe, remaining - 1),
            }
        }
        fn recur<'a>(probe: Probe<'a>, remaining: i64) -> i64 {
            handle step(probe, remaining) {
                Step::Next(next, left) => recur(next, left),
                Step::Done(value) => value,
            }
        }
        pub fn main() -> i64 {
            let mut count = 41;
            recur(Probe { target: &mut count }, 1000);
            count
        }
    "#).unwrap();
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    let program = decode_and_verify_program(&bytes).unwrap();
    let limits = grandiose_stage0::VmExecutionLimits { max_call_depth: 64, ..Default::default() };
    assert!(matches!(program.run_i64_with_limits(limits),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 64 })));
    let (value, profile) = program.run_i64_for_authoring(limits).unwrap();
    assert_eq!(value, 42);
    assert_eq!(profile.recycled_tail_calls, 1000);
    assert!(profile.peak_call_depth < 64);
}

#[test]
fn authoring_tail_calls_do_not_skip_an_active_zero_sized_destructor() {
    let outcome = compile(r#"
        struct Marker {}
        impl Drop for Marker { drop(&mut self) -> { () } }
        fn recur(remaining: i64) -> i64 {
            let marker = Marker {};
            handle remaining == 0 { true => 42, false => recur(remaining - 1) }
        }
        pub fn main() -> i64 { recur(1000) }
    "#).unwrap();
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    let program = decode_and_verify_program(&bytes).unwrap();
    let limits = grandiose_stage0::VmExecutionLimits { max_call_depth: 64, ..Default::default() };
    let result = program.run_i64_for_authoring(limits);
    assert!(matches!(result,
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 64 })), "{result:?}");
}

#[test]
fn terminal_completion_arms_destroy_the_enclosing_lexical_owners() {
    assert_eq!(run(r#"
        fn finish<'a>(target: &'a mut i64, choice: Bool) -> i64 {
            let owner = Probe { target: target };
            handle choice {
                true => 1,
                false => handle true { true => 2, false => 3 },
            }
        }
        pub fn main() -> i64 {
            let mut count = 40;
            finish(&mut count, true);
            finish(&mut count, false);
            count
        }
    "#), 42);
}

#[test]
fn generic_reference_reads_require_the_lexical_copy_contract() {
    assert_eq!(run(r#"
        fn duplicate<T>(value: &T) -> T where T: Use<[0, *]> { *value }
        pub fn main() -> i64 { let value = 42; duplicate(&value) }
    "#), 42);
    for bound in ["", "where T: Use<[0, 1]>"] {
        let outcome = compile(&format!(r#"
            fn duplicate<T>(value: &T) -> T {bound} {{ *value }}
            pub fn main() -> i64 {{ 0 }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
            panic!("generic borrowed value was copied without an unrestricted Use contract");
        };
        assert!(diagnostics.iter().any(|d| d.code == "G5004"), "{diagnostics:#?}");
    }
}

#[test]
fn lifted_generic_reference_reads_inherit_the_lexical_copy_contract() {
    assert_eq!(run(r#"
        fn duplicate<T>(value: &T) -> T where T: Use<[0, *]> {
            let copy = (input: &T) -> T { *input };
            copy(value)
        }
        pub fn main() -> i64 { let value = 42; duplicate(&value) }
    "#), 42);
}

#[test]
fn generic_erasure_destroys_the_concrete_owned_parameter() {
    assert_eq!(
        run(r#"
        fn discard<T>(value: T) -> () where T: Use<[0, 1]> { () }
        pub fn main() -> i64 {
            let mut count = 41;
            discard(Probe { target: &mut count });
            count
        }
    "#),
        42
    );
}

#[test]
fn repeated_reference_field_reborrows_do_not_take_the_reference_owner() {
    assert_eq!(
        run(r#"
        struct State { first: i64, second: i64 }
        struct Carrier<'a> { state: &'a mut State }
        fn update(carrier: Carrier) -> () {
            (*carrier.state).first = 20;
            (*carrier.state).second = 22;
            let mut first = (*carrier.state).first;
            let mut second = (*carrier.state).second;
            (*carrier.state).first = first + second;
        }
        pub fn main() -> i64 {
            let mut state = State { first: 0, second: 0 };
            update(Carrier { state: &mut state });
            state.first
        }
    "#),
        42
    );
}

#[test]
fn structural_destruction_reaches_nested_record_and_tuple_fields() {
    assert_eq!(
        run(r#"
        struct Outer<'a> { nested: (i64, Probe<'a>) }
        pub fn main() -> i64 {
            let mut count = 41;
            { let owner = Outer { nested: (9, Probe { target: &mut count }) }; () };
            count
        }
    "#),
        42
    );
}

#[test]
fn structural_destruction_only_visits_the_active_enum_payload() {
    assert_eq!(
        run(r#"
        enum Choice<'a> { Empty, Owned(Probe<'a>), Number(i64) }
        pub fn main() -> i64 {
            let mut count = 41;
            { let owner = Choice::Owned(Probe { target: &mut count }); () };
            { let empty = Choice::Empty; let number = Choice::Number(7); () };
            count
        }
    "#),
        42
    );
}

#[test]
fn owning_enum_patterns_destroy_each_extracted_and_discarded_field_once() {
    for pattern in ["Choice::Both(left, right)", "Choice::Both(left, _)", "Choice::Both(_, _)"] {
        assert_eq!(run(&format!(r#"
            enum Choice<'a> {{ Both(Probe<'a>, Probe<'a>), Empty }}
            pub fn main() -> i64 {{
                let mut first = 0;
                let mut second = 0;
                {{
                    let owner = Choice::Both(Probe {{ target: &mut first }}, Probe {{ target: &mut second }});
                    handle owner {{ {pattern} => (), Choice::Empty => () }};
                    ()
                }};
                first * 10 + second
            }}
        "#)), 11, "{pattern}");
    }
}

#[test]
fn an_owning_tuple_pattern_destroys_unbound_siblings() {
    assert_eq!(run(r#"
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let owner = (Probe { target: &mut first }, Probe { target: &mut second });
                handle owner { (left, _) => () };
                ()
            };
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn a_temporary_pattern_subject_destroys_its_residual_fields() {
    assert_eq!(run(r#"
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            handle (Probe { target: &mut first }, Probe { target: &mut second }) { (left, _) => () };
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn a_returned_pattern_binder_is_transferred_out_of_the_arm() {
    assert_eq!(run(r#"
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let result = handle (Probe { target: &mut first }, Probe { target: &mut second }) { (left, _) => left };
                ()
            };
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn a_projected_pattern_subject_moves_from_the_original_owner() {
    assert_eq!(run(r#"
        struct Inner<'a> { first: Probe<'a>, second: Probe<'a> }
        struct Outer<'a> { nested: Inner<'a> }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let owner = Outer { nested: Inner { first: Probe { target: &mut first }, second: Probe { target: &mut second } } };
                handle owner.nested { Inner { first: selected } => () };
                ()
            };
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn a_pattern_binder_can_shadow_its_source_owner() {
    assert_eq!(run(r#"
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let owner = (Probe { target: &mut first }, Probe { target: &mut second });
                handle owner { (owner, _) => { *owner.target = *owner.target + 1; } };
                ()
            };
            first * 10 + second
        }
    "#), 21);
}

#[test]
fn a_pattern_move_prevents_reusing_the_extracted_source_field() {
    let outcome = compile(r#"
        struct Owner<'a> { field: Probe<'a> }
        pub fn main() -> i64 {
            let mut count = 0;
            let owner = Owner { field: Probe { target: &mut count } };
            handle owner { Owner { field: selected } => () };
            let again = owner.field;
            0
        }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { panic!("expected a source ownership diagnostic"); };
    assert!(diagnostics.iter().any(|d| d.code == "G5003"), "{diagnostics:#?}");
}

#[test]
fn a_returned_pattern_owner_keeps_its_destructor_loan_live() {
    let outcome = compile(r#"
        pub fn main() -> i64 {
            let mut count = 0;
            let result = handle (Probe { target: &mut count }, 0) { (left, _) => left };
            count = 100;
            0
        }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { panic!("expected a source ownership diagnostic"); };
    assert!(diagnostics.iter().any(|d| d.code == "G5007"), "{diagnostics:#?}");
}

#[test]
fn a_temporary_pattern_binder_preserves_its_nested_reference_provenance() {
    assert_eq!(run(r#"
        pub fn main() -> i64 {
            let mut count = 40;
            handle (Probe { target: &mut count }, 0) { (left, _) => { *left.target = *left.target + 1; } };
            count
        }
    "#), 42);
}

#[test]
fn returned_pattern_owners_remain_live_across_strict_operands() {
    for expression in [
        "(handle (Probe { target: &mut count }, 0) { (left, _) => left }, { count = 100; 0 })",
        "(Outer { nested: handle (Probe { target: &mut count }, 0) { (left, _) => left } }, { count = 100; 0 })",
        "consume(handle (Probe { target: &mut count }, 0) { (left, _) => left }, { count = 100; 0 })",
        "({ let value = Probe { target: &mut count }; value }, { count = 100; 0 })",
    ] {
        let outcome = compile(&format!(r#"
            struct Outer<'a> {{ nested: Probe<'a> }}
            fn consume<'a>(value: Probe<'a>, other: i64) -> () {{ () }}
            pub fn main() -> i64 {{ let mut count = 0; {expression}; 0 }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {{
            panic!("expected an ownership diagnostic for {expression}");
        }};
        assert!(diagnostics.iter().any(|d| d.code == "G5007"), "{expression}: {diagnostics:#?}");
    }
}

#[test]
fn discarded_computed_owners_release_their_destructor_loans() {
    for expression in [
        "handle (Probe { target: &mut count }, 0) { (left, _) => left }",
        "{ let value = Probe { target: &mut count }; value }",
        "(handle (Probe { target: &mut count }, 0) { (left, _) => left }, 0)",
    ] {
        assert_eq!(run(&format!(r#"
            pub fn main() -> i64 {{ let mut count = 41; {expression}; count }}
        "#)), 42, "{expression}");
    }
}

#[test]
fn discarded_named_owners_are_destroyed_before_the_next_statement() {
    assert_eq!(run(r#"
        pub fn main() -> i64 {
            let mut count = 41;
            let owner = Probe { target: &mut count };
            owner;
            count
        }
    "#), 42);
}

#[test]
fn testing_a_borrowed_noncopy_enum_field_does_not_move_its_owner() {
    assert_eq!(run(r#"
        enum State<'a> { Full(Probe<'a>), Empty }
        struct Slot<'a> { state: State<'a> }
        fn inspect<'a, 'b>(slot: &'a Slot<'b>) -> i64 {
            handle slot.state { State::Full(_) => 41, State::Empty => 0 }
        }
        pub fn main() -> i64 {
            let mut count = 0;
            let observed = {
                let slot = Slot { state: State::Full(Probe { target: &mut count }) };
                inspect(&slot)
            };
            observed + count
        }
    "#), 42);
}

#[test]
fn an_inactive_enum_destructor_does_not_extend_the_selected_reference_loan() {
    assert_eq!(run(r#"
        struct Unrelated {}
        impl Use<[0, 1]> for Unrelated {}
        impl Drop for Unrelated { drop(&mut self) -> {} }
        enum Outcome<'a> { Lent(&'a i64), Owned(Unrelated) }
        fn lend<'a>(value: &'a mut i64) -> Outcome<'a> { Outcome::Lent(& *value) }
        pub fn main() -> i64 {
            let mut count = 0;
            handle lend(&mut count) {
                Outcome::Lent(_) => { count = 42; count },
                Outcome::Owned(_) => 0,
            }
        }
    "#), 42);
    for expression in [
        "handle Resident::Owned(Probe { target: &mut count }) { Resident::Owned(_) => { count = 42; count }, Resident::Empty => 0 }",
        "handle lend(&mut count) { Outcome::Lent(value) => { count = 42; *value }, Outcome::Owned(_) => 0 }",
    ] {
        let result = compile(&format!(r#"
            struct Unrelated {{}}
            impl Use<[0, 1]> for Unrelated {{}}
            impl Drop for Unrelated {{ drop(&mut self) -> {{}} }}
            enum Outcome<'a> {{ Lent(&'a i64), Owned(Unrelated) }}
            enum Resident<'a> {{ Owned(Probe<'a>), Empty }}
            fn lend<'a>(value: &'a mut i64) -> Outcome<'a> {{ Outcome::Lent(& *value) }}
            pub fn main() -> i64 {{ let mut count = 0; {expression} }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = result else {
            panic!("a live selected loan or destructor was discarded: {expression}");
        };
        assert!(diagnostics.iter().any(|d| matches!(d.code, "G5004" | "G5006" | "G5007")), "{diagnostics:#?}");
    }
}

#[test]
fn unique_reference_arguments_reborrow_contextually_but_explicit_moves_consume() {
    assert_eq!(run(r#"
        struct State { value: i64 }
        fn set(state: &mut State) -> () { (*state).value = 42; }
        fn inspect(state: &mut State) -> i64 { set(&mut *state); state.value }
        pub fn main() -> i64 { let mut state = State { value: 0 }; inspect(&mut state) }
    "#), 42);
    assert_eq!(run(r#"
        struct State { value: i64 }
        fn set(state: &mut State) -> () { (*state).value = 42; }
        fn inspect(state: &mut State) -> i64 { set(state); state.value }
        pub fn main() -> i64 { let mut state = State { value: 0 }; inspect(&mut state) }
    "#), 42);
    let result = compile(r#"
        struct State { value: i64 }
        fn set(state: &mut State) -> () { (*state).value = 42; }
        fn inspect(state: &mut State) -> i64 { set(move state); state.value }
        pub fn main() -> i64 { 0 }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = result else {
        panic!("a moved unique reference was used again");
    };
    assert!(diagnostics.iter().any(|d| d.code == "G5001"), "{diagnostics:#?}");
}

#[test]
fn an_operation_pattern_destroys_bound_and_discarded_payload_fields() {
    assert_eq!(run(r#"
        effect Accept<'a> { accept(value: (Probe<'a>, Probe<'a>)) -> !; }
        fn accept<'a>(value: (Probe<'a>, Probe<'a>)) -> () {
            handle Accept<'a>::accept(value) {
                Accept<'a>::accept((left, _)) => ()
            }
        }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            accept((Probe { target: &mut first }, Probe { target: &mut second }));
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn an_owning_pattern_cannot_extract_a_noncopy_field_through_a_borrow() {
    let outcome = compile(r#"
        struct Owner<'a> { field: Probe<'a> }
        pub fn main() -> i64 {
            let mut count = 0;
            let owner = Owner { field: Probe { target: &mut count } };
            let reference = &owner;
            handle *reference { Owner { field: selected } => () };
            0
        }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else { panic!("{outcome:#?}"); };
    assert!(diagnostics.iter().any(|d| d.code == "G5004"), "{diagnostics:#?}");
}

#[test]
fn leaving_a_pattern_arm_destroys_its_binder_and_residual_owner() {
    assert_eq!(run(r#"
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            let result = @done: i64 {
                let owner = (Probe { target: &mut first }, Probe { target: &mut second });
                handle owner { (left, _) => @done(0) };
                0
            };
            first * 10 + second + result
        }
    "#), 11);
}

#[test]
fn a_positive_record_refinement_does_not_duplicate_destruction() {
    assert_eq!(run(r#"
        struct Pair<'a> { first: Probe<'a>, second: Probe<'a> }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let owner = Pair { first: Probe { target: &mut first }, second: Probe { target: &mut second } };
                handle owner is Pair { first: selected } { Test::Yes(_) => (), Test::No(_) => () };
                ()
            };
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn an_observational_refinement_leaves_its_subject_owned() {
    assert_eq!(run(r#"
        struct Pair<'a> { first: Probe<'a>, second: Probe<'a> }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let owner = Pair { first: Probe { target: &mut first }, second: Probe { target: &mut second } };
                handle owner is Pair { first: selected } { Test::Yes(_) => (), Test::No(_) => () };
                let remaining = owner;
                ()
            };
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn a_refinement_binder_borrows_the_selected_noncopy_owner() {
    for subject in ["owner", "*reference"] {
        assert_eq!(run(&format!(r#"
            struct Owner {{ value: i64 }}
            impl Use<[0, 1]> for Owner {{}}
            struct Pair {{ field: Owner }}
            fn inspect(value: &Owner) -> i64 {{ value.value }}
            fn visit<Y, N, F>(test: Test<Y, N>, body: F) -> i64
                where N: Use<[0,1]>, F: Fn<(Y), Output = i64> {{
                handle test {{ Test::Yes(pack) => body(pack), Test::No(_) => 0 }}
            }}
            pub fn main() -> i64 {{
                let mut owner = Pair {{ field: Owner {{ value: 42 }} }};
                let reference = &owner;
                visit({subject} is Pair {{ field: selected }}) {{ inspect(selected) }}
            }}
        "#)), 42, "{subject}");
    }
}

#[test]
fn first_class_refinement_packs_keep_borrowed_owners_in_scope() {
    for source in [
        "pub fn main() -> i64 { let test = { let owner = Owner { value: 42 }; owner is selected }; handle test { Test::Yes(_) => 1, Test::No(_) => 0 } }",
        "fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { let test = { let owner = Owner { value: 42 }; identity(owner is selected) }; handle test { Test::Yes(_) => 1, Test::No(_) => 0 } }",
    ] {
        let outcome = compile(&format!("struct Owner {{ value: i64 }} {source}"));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
            panic!("a binding pack escaped its borrowed owner");
        };
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5013"), "{diagnostics:#?}");
    }
}

#[test]
fn first_class_refinement_packs_protect_borrowed_projections_across_calls() {
    for (action, code) in [
        ("let moved = owner", "G5004"),
        ("owner.field = Owner { value: 100 }", "G5007"),
    ] {
        let outcome = compile(&format!(r#"
            struct Owner {{ value: i64 }}
            impl Use<[0, 1]> for Owner {{}}
            struct Pair {{ field: Owner }}
            fn identity<T>(value: T) -> T {{ value }}
            pub fn main() -> i64 {{
                let mut owner = Pair {{ field: Owner {{ value: 42 }} }};
                let test = identity(owner is Pair {{ field: selected }});
                {action};
                handle test {{ Test::Yes(_) => 1, Test::No(_) => 0 }}
            }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
            panic!("a live binding pack lost its borrowed projection for {action}");
        };
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == code), "{diagnostics:#?}");
    }
    assert_eq!(run(r#"
        struct Owner { value: i64 }
        impl Use<[0, 1]> for Owner {}
        struct Pair { field: Owner }
        fn identity<T>(value: T) -> T { value }
        pub fn main() -> i64 {
            let owner = Pair { field: Owner { value: 42 } };
            let test = identity(owner is Pair { field: selected });
            let matched = handle test { Test::Yes(_) => 1, Test::No(_) => 0 };
            let moved = owner;
            moved.field.value + matched
        }
    "#), 43);
}

#[test]
fn a_refinement_borrow_cannot_escape_its_owning_scope() {
    for body in [
        "pub fn bad() -> &Owner { let value = Owner { value: 42 }; visit(value is selected, &value) { selected } } pub fn main() -> i64 { 0 }",
        "pub fn main() -> i64 { let reference = { let value = Owner { value: 42 }; visit(value is selected, &value) { selected } }; reference.value }",
    ] {
        let outcome = compile(&format!(r#"
            struct Owner {{ value: i64 }}
            impl Use<[0, 1]> for Owner {{}}
            fn visit<Y, N, R, F>(test: Test<Y, N>, fallback: R, body: F) -> R
            where N: Use<[0,1]>, F: Fn<(Y), Output = R>, R: Use<[0, 1]> {{
                handle test {{ Test::Yes(pack) => body(pack), Test::No(_) => fallback }}
            }}
            {body}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
            panic!("expected a refinement escape diagnostic");
        };
        assert!(diagnostics.iter().any(|d| d.code == "G5013"), "{diagnostics:#?}");
    }
}

#[test]
fn observing_a_unique_reference_preserves_its_owner_after_the_pack_is_consumed() {
    assert_eq!(run(r#"
        fn visit<Y, N, F>(test: Test<Y, N>, body: F) -> i64
            where N: Use<[0,1]>, F: Fn<(Y), Output = i64> {
            handle test { Test::Yes(pack) => body(pack), Test::No(_) => 0 }
        }
        pub fn main() -> i64 {
            let mut value = 21;
            let reference = &mut value;
            let observed = visit(reference is selected) { *(*selected) };
            *reference = 21;
            observed + *reference
        }
    "#), 42);
    assert_eq!(run(r#"
        struct Owner { value: i64 }
        fn visit<Y, N, F>(test: Test<Y, N>, body: F) -> i64
            where N: Use<[0,1]>, F: Fn<(Y), Output = i64> {
            handle test { Test::Yes(pack) => body(pack), Test::No(_) => 0 }
        }
        pub fn main() -> i64 {
            let mut owner = Owner { value: 21 };
            let reference = &mut owner;
            let observed = visit(*reference is Owner { value: selected }) { selected };
            (*reference).value = 21;
            observed + reference.value
        }
    "#), 42);
}

#[test]
fn a_live_observational_pack_suspends_its_unique_reference_subject() {
    let outcome = compile(r#"
        fn visit<Y, N, F>(test: Test<Y, N>, body: F) -> i64
            where N: Use<[0,1]>, F: Fn<(Y), Output = i64> {
            handle test { Test::Yes(pack) => body(pack), Test::No(_) => 0 }
        }
        pub fn main() -> i64 {
            let mut value = 42;
            let reference = &mut value;
            let test = reference is selected;
            *reference = 100;
            visit(test) { *(*selected) }
        }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
        panic!("a unique reference remained writable while its observational pack was live");
    };
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5004"), "{diagnostics:#?}");
    assert_eq!(run(r#"
        fn visit<Y, N, F>(test: Test<Y, N>, body: F) -> i64
            where N: Use<[0,1]>, F: Fn<(Y), Output = i64> {
            handle test { Test::Yes(pack) => body(pack), Test::No(_) => 0 }
        }
        pub fn main() -> i64 {
            let mut value = 42;
            let reference = &mut value;
            let test = reference is selected;
            let observed = *reference;
            visit(test) { *(*selected) } + observed
        }
    "#), 84);
}

#[test]
fn hidden_refinement_arguments_do_not_grant_unique_access() {
    for action in ["let child = &mut *(*selected); ()", "*(*selected) = 100"] {
        let outcome = compile(&format!(r#"
            enum Holder<'a> {{ Held(&'a mut i64), Empty }}
            fn visit<Y, N, F>(test: Test<Y, N>, body: F) -> i64
                where N: Use<[0,1]>, F: Fn<(Y), Output = i64> {{
                handle test {{ Test::Yes(pack) => body(pack), Test::No(_) => 0 }}
            }}
            pub fn main() -> i64 {{
                let mut value = 42;
                let holder = Holder::Held(&mut value);
                visit(holder is Holder::Held(selected)) {{ {action}; 0 }}
            }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
            panic!("a hidden observational argument granted unique access");
        };
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4141"), "{diagnostics:#?}");
    }
}

#[test]
fn an_observational_refinement_cannot_recover_unique_access() {
    for action in ["let child = &mut *(*selected); ()", "*(*selected) = 100"] {
        let outcome = compile(&format!(r#"
            enum Holder<'a> {{ Held(&'a mut i64), Empty }}
            fn visit<Y, N, F>(test: Test<Y, N>, body: F) -> i64
                where N: Use<[0,1]>, F: Fn<(Y), Output = i64> {{
                handle test {{ Test::Yes(pack) => body(pack), Test::No(_) => 0 }}
            }}
            pub fn main() -> i64 {{
                let mut value = 42;
                let holder = Holder::Held(&mut value);
                let reference = &holder;
                visit(*reference is Holder::Held(selected)) {{ {action}; 0 }};
                0
            }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
            panic!("expected a shared-refinement ownership diagnostic");
        };
        assert!(diagnostics.iter().any(|d| d.code == "G4141"), "{diagnostics:#?}");
    }
}

#[test]
fn copying_a_closure_capture_cannot_bypass_a_unique_field_loan() {
    let outcome = compile(r#"
        struct Pair { left: i64, right: i64 }
        pub fn main() -> i64 {
            let mut owner = Pair { left: 1, right: 2 };
            let loan = &mut owner.left;
            let delayed = (ignored: i64) -> i64 { owner.left + owner.right };
            *loan = 40;
            delayed(0)
        }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
        panic!("an owned closure copy bypassed a live unique field loan");
    };
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5008"), "{diagnostics:#?}");
    assert_eq!(run(r#"
        struct Pair { left: i64, right: i64 }
        pub fn main() -> i64 {
            let mut owner = Pair { left: 1, right: 2 };
            let loan = &mut owner.left;
            *loan = 40;
            let delayed = (ignored: i64) -> i64 { owner.left + owner.right };
            delayed(0)
        }
    "#), 42);
}

#[test]
fn a_live_refinement_view_protects_its_source_place() {
    for (action, code) in [
        ("let moved = owner", "G5004"),
        ("owner.field = Owner { value: 100 }", "G5006"),
    ] {
        let outcome = compile(&format!(r#"
            struct Owner {{ value: i64 }}
            impl Use<[0, 1]> for Owner {{}}
            struct Pair {{ field: Owner }}
            fn inspect(value: &Owner) -> i64 {{ value.value }}
            fn visit<Y, N, F>(test: Test<Y, N>, body: F) -> i64
                where N: Use<[0,1]>, F: Fn<(Y), Output = i64> {{
                handle test {{ Test::Yes(pack) => body(pack), Test::No(_) => 0 }}
            }}
            pub fn main() -> i64 {{
                let mut owner = Pair {{ field: Owner {{ value: 42 }} }};
                visit(owner is Pair {{ field: selected }}) {{ {action}; inspect(selected) }}
            }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
            panic!("expected a live-refinement borrow diagnostic");
        };
        assert!(diagnostics.iter().any(|d| d.code == code), "{diagnostics:#?}");
    }
}

#[test]
fn a_resumption_completes_before_the_enclosing_expression_suffix() {
    assert_eq!(run(r#"
        effect Ask { [1, 1] ask() -> i64; }
        fn relay() -> i64 / Ask { Ask::ask() }
        pub fn main() -> i64 {
            let answer = handle relay() { Ask::ask() with k => k(1) * 2 };
            answer + 100
        }
    "#), 102);
}

#[test]
fn indirect_handler_payloads_preserve_the_declared_input_region() {
    assert_eq!(run(r#"
        effect Ask<T> { [1, 1] ask(value: T) -> T; }
        type Callback = for<'a, 'b> (&'a i64, &'b i64) -> &'b i64 / {Ask<&'b i64>};
        fn relay<'a, 'b>(ignored: &'a i64, value: &'b i64) -> &'b i64 / {Ask<&'b i64>} {
            Ask<&'b i64>::ask(value)
        }
        fn read(value: &i64) -> i64 { *value }
        fn apply(callback: Callback) -> i64 {
            let stable = 42;
            let result = {
                let temporary = 0;
                handle callback(&temporary, &stable) {
                    Ask<&i64>::ask(payload) with k => k(payload)
                }
            };
            read(result)
        }
        pub fn main() -> i64 { apply(relay) }
    "#), 42);
}

#[test]
fn delimited_handler_completion_preserves_the_ordinary_call_path() {
    assert_eq!(run(r#"
        effect Ask { [1, 1] ask() -> i64; }
        fn relay() -> i64 / Ask { 7 }
        fn apply() -> i64 {
            let answer = handle relay() { Ask::ask() with k => k(1) * 2 };
            answer + 100
        }
        pub fn main() -> i64 { apply() + 1000 }
    "#), 1107);
}

#[test]
fn delimited_resumptions_finish_inside_a_non_entry_call_frame() {
    assert_eq!(run(r#"
        effect Ask { [1, 1] ask() -> i64; }
        fn relay() -> i64 / Ask { Ask::ask() + 10 }
        fn apply() -> i64 {
            let answer = handle relay() { Ask::ask() with k => k(1) * 2 };
            answer + 100
        }
        pub fn main() -> i64 { apply() + 1000 }
    "#), 1122);
}

#[test]
fn each_deep_one_shot_resumption_completes_before_the_lexical_suffix() {
    assert_eq!(run(r#"
        effect Ask { [1, 1] ask() -> i64; }
        fn relay() -> i64 / Ask { let first = Ask::ask(); first + Ask::ask() }
        pub fn main() -> i64 {
            let answer = handle relay() { Ask::ask() with k => k(1) * 2 };
            answer + 100
        }
    "#), 108);
}

#[test]
fn delimited_resumption_results_need_not_match_the_operation_parameter() {
    assert_eq!(run(r#"
        effect Ask { [1, 1] ask() -> i64; }
        fn relay() -> Bool / Ask { Ask::ask() == 1 }
        fn bit(value: Bool) -> i64 { handle value { true => 42, false => 0 } }
        fn apply() -> i64 {
            let answer = handle relay() { Ask::ask() with k => k(1) };
            bit(answer)
        }
        pub fn main() -> i64 { apply() }
    "#), 42);
}

#[test]
fn resumption_completion_preserves_writes_to_the_enclosing_source_storage() {
    assert_eq!(run(r#"
        effect Ask { [1, 1] ask() -> i64; }
        fn relay(target: &mut i64) -> i64 / Ask {
            let value = Ask::ask();
            *target = *target + 10;
            value
        }
        pub fn main() -> i64 {
            let mut count = 0;
            let answer = handle relay(&mut count) { Ask::ask() with k => k(1) * 2 };
            count * 100 + answer
        }
    "#), 1002);
}

#[test]
fn indirect_handler_payloads_cannot_outlive_their_actual_argument() {
    let outcome = compile(r#"
        effect Ask<T> { [1, 1] ask(value: T) -> T; }
        type Callback = for<'a, 'b> (&'a i64, &'b i64) -> &'b i64 / {Ask<&'b i64>};
        fn read(value: &i64) -> i64 { *value }
        fn apply(callback: Callback) -> i64 {
            let stable = 42;
            let result = {
                let temporary = 0;
                handle callback(&stable, &temporary) {
                    Ask<&i64>::ask(payload) with k => k(payload)
                }
            };
            read(result)
        }
        pub fn main() -> i64 { 0 }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
        panic!("indirect handler payload escaped its short-lived argument");
    };
    assert!(diagnostics.iter().any(|d| matches!(d.code, "G5013" | "G5017")), "{diagnostics:#?}");
}

#[test]
fn projected_reads_check_the_selected_referent_field() {
    assert_eq!(run(r#"
        struct Pair { first: i64, second: i64 }
        fn inspect(value: &mut Pair) -> i64 {
            let first = &mut value.first;
            handle value.second { 22 => { (*value).second = 22; *first = 20; *first + 22 }, _ => 0 }
        }
        pub fn main() -> i64 { let mut value = Pair { first: 0, second: 22 }; inspect(&mut value) }
    "#), 42);
    for read in ["let copied = value.first; copied + *first", "handle value.first { copied => copied + *first }", "(*value).first = 42; *first"] {
        let outcome = compile(&format!(r#"
            struct Pair {{ first: i64, second: i64 }}
            fn inspect(value: &mut Pair) -> i64 {{
                let first = &mut value.first;
                {read}
            }}
            pub fn main() -> i64 {{ 0 }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
            panic!("overlapping field observation used a suspended parent");
        };
        assert!(diagnostics.iter().any(|d| d.code == "G5004"), "{diagnostics:#?}");
    }
}

#[test]
fn a_scalar_observation_consumes_its_computed_reference() {
    assert_eq!(run(r#"
        fn lend(value: &mut i64) -> &i64 { & *value }
        fn overwrite(value: &mut i64) -> i64 { *value = 42; *value }
        pub fn main() -> i64 {
            let mut value = 0;
            handle *lend(&mut value) { 0 => overwrite(&mut value), _ => 0 }
        }
    "#), 42);
}

#[test]
fn a_consumed_reference_result_releases_only_dead_payload_loans() {
    assert_eq!(run(r#"
        enum Lent<'a> { Value(&'a i64) }
        fn lend(value: &mut i64) -> Lent { Lent::Value(& *value) }
        pub fn main() -> i64 {
            let mut value = 21;
            handle lend(&mut value) { Lent::Value(first) => {
                let copied = *first;
                handle lend(&mut value) { Lent::Value(second) => copied + *second }
            } }
        }
    "#), 42);
    let outcome = compile(r#"
        enum Lent<'a> { Value(&'a i64) }
        fn lend(value: &mut i64) -> Lent { Lent::Value(& *value) }
        pub fn main() -> i64 {
            let mut value = 21;
            handle lend(&mut value) { Lent::Value(first) => {
                handle lend(&mut value) { Lent::Value(second) => *first + *second }
            } }
        }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
        panic!("consuming a result released a still-live reference payload");
    };
    assert!(diagnostics.iter().any(|d| d.code == "G5006"), "{diagnostics:#?}");
}

#[test]
fn a_reference_tuple_cannot_duplicate_one_unique_reborrow() {
    let outcome = compile(r#"
        struct Pair { first: i64, second: i64 }
        fn bad<'a>(value: &'a mut Pair) -> (&'a mut i64, &'a mut i64) {
            (&mut value.first, &mut value.first)
        }
        pub fn main() -> i64 { 0 }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
        panic!("a producer duplicated one unique field into two live references");
    };
    assert!(diagnostics.iter().any(|d| d.code == "G5006"), "{diagnostics:#?}");
}

#[test]
fn disjoint_unique_reborrows_can_be_returned_together() {
    assert_eq!(run(r#"
        struct Pair { first: i64, second: i64 }
        fn split<'a>(value: &'a mut Pair) -> (&'a mut i64, &'a mut i64) {
            (&mut value.first, &mut value.second)
        }
        pub fn main() -> i64 {
            let mut value = Pair { first: 2, second: 22 };
            handle split(&mut value) { (left, right) => { *left = 20; *left + *right } }
        }
    "#), 42);
}

#[test]
fn returned_partitions_do_not_reactivate_their_common_parent() {
    let outcome = compile(r#"
        struct Pair { first: i64, second: i64 }
        fn split<'a>(value: &'a mut Pair) -> (&'a mut i64, &'a mut i64) {
            (&mut value.first, &mut value.second)
        }
        fn overwrite(value: &mut Pair) -> () { (*value).first = 100; }
        fn bad(value: &mut Pair) -> i64 {
            handle split(value) { (left, right) => { overwrite(value); *left + *right } }
        }
        pub fn main() -> i64 { 0 }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
        panic!("a returned partition reactivated its common parent");
    };
    assert!(diagnostics.iter().any(|d| matches!(d.code, "G5004" | "G5006")), "{diagnostics:#?}");
}

#[test]
fn a_reference_tuple_cannot_copy_borrowed_unique_handles() {
    for reference in ["&'a &'a mut i64", "&'a mut &'a mut i64"] {
        let outcome = compile(&format!(r#"
            fn bad<'a>(value: {reference}) -> (&'a mut i64, &'a mut i64) {{ (*value, *value) }}
            pub fn main() -> i64 {{ 0 }}
        "#));
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {{
            panic!("a producer copied unique handles through {reference}");
        }};
        assert!(diagnostics.iter().any(|d| matches!(d.code, "G4141" | "G5004" | "G5006")), "{diagnostics:#?}");
    }
}

#[test]
fn a_partition_reborrow_preserves_disjoint_sibling_access() {
    assert_eq!(run(r#"
        struct Pair { first: i64, second: i64 }
        fn split<'a>(value: &'a mut Pair) -> (&'a mut i64, &'a mut i64) {
            (&mut value.first, &mut value.second)
        }
        pub fn main() -> i64 {
            let mut value = Pair { first: 2, second: 0 };
            handle split(&mut value) { (left, right) => {
                let child = &mut *left;
                *right = 22;
                *child = 20;
                *child + *right
            } }
        }
    "#), 42);
}

#[test]
fn a_partition_cannot_be_reborrowed_twice_while_both_children_are_live() {
    let outcome = compile(r#"
        struct Pair { first: i64, second: i64 }
        fn split<'a>(value: &'a mut Pair) -> (&'a mut i64, &'a mut i64) {
            (&mut value.first, &mut value.second)
        }
        pub fn main() -> i64 {
            let mut value = Pair { first: 2, second: 22 };
            handle split(&mut value) { (left, right) => {
                let child = &mut *left;
                let duplicate = &mut *left;
                *child + *duplicate + *right
            } }
        }
    "#);
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome else {
        panic!("one partition was reborrowed uniquely twice");
    };
    assert!(diagnostics.iter().any(|d| d.code == "G5006"), "{diagnostics:#?}");
}

#[test]
fn an_owning_record_pattern_preserves_nested_residual_owners() {
    assert_eq!(run(r#"
        struct Inner<'a> { first: Probe<'a>, second: Probe<'a> }
        struct Outer<'a> { nested: Inner<'a> }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let owner = Outer { nested: Inner { first: Probe { target: &mut first }, second: Probe { target: &mut second } } };
                handle owner { Outer { nested: Inner { first: selected } } => () };
                ()
            };
            first * 10 + second
        }
    "#), 11);
}

#[test]
fn replacement_destroys_the_old_owner_before_the_new_owner() {
    assert_eq!(
        run(r#"
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let mut owner = Probe { target: &mut first };
                owner = Probe { target: &mut second };
                ()
            };
            first * 10 + second
        }
    "#),
        11
    );
}

#[test]
fn replacement_releases_the_old_residents_loan_immediately() {
    assert_eq!(
        run(r#"
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let mut owner = Probe { target: &mut first };
                owner = Probe { target: &mut second };
                first = first + 30;
                ()
            };
            first + second + 10
        }
    "#),
        42
    );
}

#[test]
fn assigning_an_owner_to_itself_retains_its_reference_provenance() {
    assert_eq!(
        run(r#"
        pub fn main() -> i64 {
            let mut count = 41;
            { let mut owner = Probe { target: &mut count }; owner = owner; () };
            count
        }
    "#),
        42
    );
}

#[test]
fn partial_moves_destroy_only_the_remaining_fields() {
    assert_eq!(
        run(r#"
        struct Pair<'a> { first: Probe<'a>, second: Probe<'a> }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let pair = Pair { first: Probe { target: &mut first }, second: Probe { target: &mut second } };
                let moved = move pair.first;
                ()
            };
            first * 10 + second
        }
    "#),
        11
    );
}

#[test]
fn nonlocal_exit_destroys_nested_owners_once() {
    assert_eq!(
        run(r#"
        struct Outer<'a> { nested: Probe<'a> }
        pub fn main() -> i64 {
            let mut count = 40;
            let result = @done: i64 {
                let owner = Outer { nested: Probe { target: &mut count } };
                @done(1);
                0
            };
            count + result
        }
    "#),
        42
    );
}

#[test]
fn forwarding_an_owned_parameter_does_not_also_destroy_the_sender() {
    assert_eq!(
        run(r#"
        fn relay<T>(value: T) -> T where T: Use<[0, 1]> { value }
        pub fn main() -> i64 {
            let mut count = 41;
            { let owner = relay(Probe { target: &mut count }); (); };
            count
        }
    "#),
        42
    );
}

#[test]
fn constructing_an_aggregate_transfers_the_owned_parameter() {
    assert_eq!(
        run(r#"
        struct Outer<'a> { nested: Probe<'a> }
        fn wrap<'a>(value: Probe<'a>) -> Outer<'a> { Outer { nested: value } }
        pub fn main() -> i64 {
            let mut count = 41;
            { let owner = wrap(Probe { target: &mut count }); (); };
            count
        }
    "#),
        42
    );
}

#[test]
fn an_ignored_owned_call_result_is_destroyed() {
    assert_eq!(
        run(r#"
        fn make<'a>(target: &'a mut i64) -> Probe<'a> { Probe { target: target } }
        pub fn main() -> i64 {
            let mut count = 41;
            make(&mut count);
            count
        }
    "#),
        42
    );
}

#[test]
fn inspecting_a_borrow_does_not_destroy_the_borrowed_owner() {
    assert_eq!(
        run(r#"
        fn inspect<'a, 'b>(value: &'a Probe<'b>) -> i64 { *value.target }
        pub fn main() -> i64 {
            let mut count = 40;
            let observed = {
                let owner = Probe { target: &mut count };
                let before = inspect(&owner);
                inspect(&owner) - before + 1
            };
            count + observed
        }
    "#),
        42
    );
}

#[test]
fn implicit_field_moves_destroy_only_the_remaining_owner() {
    assert_eq!(
        run(r#"
        struct Pair<'a> { first: Probe<'a>, second: Probe<'a> }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let pair = Pair { first: Probe { target: &mut first }, second: Probe { target: &mut second } };
                let moved = pair.first;
                ()
            };
            first * 10 + second
        }
    "#),
        11
    );
}

#[test]
fn returning_a_field_destroys_the_remaining_parameter_fields() {
    assert_eq!(
        run(r#"
        struct Pair<'a> { first: Probe<'a>, second: Probe<'a> }
        fn first<'a>(pair: Pair<'a>) -> Probe<'a> { pair.first }
        pub fn main() -> i64 {
            let mut left = 0;
            let mut right = 0;
            {
                let owner = first(Pair { first: Probe { target: &mut left }, second: Probe { target: &mut right } });
                ()
            };
            left * 10 + right
        }
    "#),
        11
    );
}

#[test]
fn shadowing_keeps_both_owned_bindings_armed_until_scope_exit() {
    assert_eq!(
        run(r#"
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let owner = Probe { target: &mut first };
                let owner = Probe { target: &mut second };
                ()
            };
            first * 10 + second
        }
    "#),
        11
    );
}

#[test]
fn the_custom_hook_runs_before_structural_field_destruction() {
    assert_eq!(
        run(r#"
        struct Outer<'a> { nested: Probe<'a> }
        impl<'a> Drop for Outer<'a> {
            drop(&mut self) -> { *self.nested.target = *self.nested.target * 10; }
        }
        pub fn main() -> i64 {
            let mut count = 4;
            { let owner = Outer { nested: Probe { target: &mut count } }; () };
            count
        }
    "#),
        41
    );
}

#[test]
fn generic_drop_hooks_and_owned_fields_are_specialized_together() {
    assert_eq!(
        run(r#"
        struct Outer<T> { nested: T }
        impl<T> Drop for Outer<T> where T: Use<[0, 1]> {
            drop(&mut self) -> {}
        }
        pub fn main() -> i64 {
            let mut count = 41;
            { let owner = Outer { nested: Probe { target: &mut count } }; () };
            count
        }
    "#),
        42
    );
}

#[test]
fn replacing_a_borrowed_slot_destroys_its_previous_owner() {
    assert_eq!(
        run(r#"
        fn replace<'a, 'b>(slot: &'a mut Probe<'b>, value: Probe<'b>) -> () { *slot = value; }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let mut owner = Probe { target: &mut first };
                replace(&mut owner, Probe { target: &mut second });
                ()
            };
            first * 10 + second
        }
    "#),
        11
    );
}

#[test]
fn restoring_a_moved_referent_does_not_destroy_the_transferred_value() {
    assert_eq!(
        run(r#"
        fn restore<'a, 'b>(slot: &'a mut Probe<'b>) -> () {
            let resident = move *slot;
            *slot = resident;
        }
        pub fn main() -> i64 {
            let mut count = 41;
            { let mut owner = Probe { target: &mut count }; restore(&mut owner); () };
            count
        }
    "#),
        42
    );
}

#[test]
fn field_replacement_destroys_only_the_old_field_and_preserves_siblings() {
    assert_eq!(
        run(r#"
        struct Pair<'a> { first: Probe<'a>, second: Probe<'a> }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            let mut third = 0;
            {
                let mut pair = Pair { first: Probe { target: &mut first }, second: Probe { target: &mut second } };
                pair.first = Probe { target: &mut third };
                ()
            };
            first * 100 + second * 10 + third
        }
    "#),
        111
    );
}

#[test]
fn a_moved_field_can_be_restored_without_destroying_its_former_owner() {
    assert_eq!(
        run(r#"
        struct Outer<'a> { nested: Probe<'a> }
        pub fn main() -> i64 {
            let mut first = 0;
            let mut second = 0;
            {
                let mut owner = Outer { nested: Probe { target: &mut first } };
                let moved = owner.nested;
                owner.nested = Probe { target: &mut second };
                ()
            };
            first * 10 + second
        }
    "#),
        11
    );
}
