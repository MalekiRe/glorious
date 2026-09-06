use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

const PROBE: &str = r#"
    struct Probe<'a> { target: &'a mut i64 }
    impl<'a> Use<[0, 1]> for Probe<'a> {}
    impl<'a> Drop for Probe<'a> {
        drop(&mut self) -> { *self.target = *self.target + 1; }
    }
"#;

fn run(body: &str) -> i64 {
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
    let outcome = StageZeroCompiler::new().compile(request).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    program.run_i64().unwrap()
}

#[test]
fn generic_erasure_destroys_the_concrete_owned_parameter() {
    assert_eq!(
        run(r#"
        fn discard<T>(value: T) -> () where T: Use<[0, 1]> { () }
        pub fn main() -> i64 {
            let count = 41;
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
            let first = (*carrier.state).first;
            let second = (*carrier.state).second;
            (*carrier.state).first = first + second;
        }
        pub fn main() -> i64 {
            let state = State { first: 0, second: 0 };
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
            let count = 41;
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
            let count = 41;
            { let owner = Choice::Owned(Probe { target: &mut count }); () };
            { let empty = Choice::Empty; let number = Choice::Number(7); () };
            count
        }
    "#),
        42
    );
}

#[test]
fn replacement_destroys_the_old_owner_before_the_new_owner() {
    assert_eq!(
        run(r#"
        pub fn main() -> i64 {
            let first = 0;
            let second = 0;
            {
                let owner = Probe { target: &mut first };
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
            let first = 0;
            let second = 0;
            {
                let owner = Probe { target: &mut first };
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
            let count = 41;
            { let owner = Probe { target: &mut count }; owner = owner; () };
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
            let first = 0;
            let second = 0;
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
            let count = 40;
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
            let count = 41;
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
            let count = 41;
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
            let count = 41;
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
            let count = 40;
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
            let first = 0;
            let second = 0;
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
            let left = 0;
            let right = 0;
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
            let first = 0;
            let second = 0;
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
            let count = 4;
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
            let count = 41;
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
            let first = 0;
            let second = 0;
            {
                let owner = Probe { target: &mut first };
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
            let count = 41;
            { let owner = Probe { target: &mut count }; restore(&mut owner); () };
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
            let first = 0;
            let second = 0;
            let third = 0;
            {
                let pair = Pair { first: Probe { target: &mut first }, second: Probe { target: &mut second } };
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
            let first = 0;
            let second = 0;
            {
                let owner = Outer { nested: Probe { target: &mut first } };
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
