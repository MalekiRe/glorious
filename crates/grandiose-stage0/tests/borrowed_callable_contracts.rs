use std::collections::BTreeMap;
use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};

fn request(source: &str, level: &str) -> CompilationRequest {
    let package = PackageKey("borrowed-callable-contracts@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"borrowed-callable-contracts")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), level.into())]),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

fn run(source: &str, expected: i64) {
    for level in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(source, level))
            .unwrap_or_else(|error| panic!("O{level}: {source}: {:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), expected, "O{level} fresh");
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), expected, "O{level} decoded");
    }
}

#[test]
fn owned_capture_storage_borrows_preserve_nested_contents_and_updates() {
    for source in [
        "pub fn main() -> i64 { let value = (20,22); let task = move (value) { &value }; let result = (&task)(); result.0 + result.1 }",
        "pub fn main() -> i64 { let backing = 42; let value = (&backing,0); let task = move (value) { &value }; let result = (&task)(); *result.0 }",
        "pub fn main() -> i64 { let value = (0,42); let task = move (value) { &value.1 }; let result = (&task)(); *result }",
        "pub fn main() -> i64 { let mut value = 41; let mut task = move (value) { &mut value }; let result = (&mut task)(); *result = *result + 1; *result }",
        "pub fn main() -> i64 { let first = 1; let final_value = 42; let mut value = (&first,0); let mut task = move (value) { &mut value }; let result = (&mut task)(); result.0 = &final_value; *result.0 }",
        "pub fn main() -> i64 { let a = 1; let b = 42; let first = (&a,0); let second = (&b,0); let task = move (first,second) { let unused = first.1; &second }; let result = (&task)(); *result.0 }",
    ] { run(source, 42); }
}

#[test]
fn borrowed_capture_storage_keeps_owner_and_written_reference_lifetimes() {
    for (source, codes) in [
        ("fn bad() -> &i64 { let value = 42; let task = move (value) { &value }; (&task)() } pub fn main() -> i64 { *bad() }", &["G5013", "G5017"][..]),
        ("pub fn main() -> i64 { let value = 42; let task = move (value) { &value }; let result = (&task)(); let moved = move task; *result }", &["G5004"][..]),
        ("pub fn main() -> i64 { let mut value = 42; let mut task = move (value) { &mut value }; let first = (&mut task)(); let second = (&mut task)(); *first + *second }", &["G5004", "G5006", "G5007"][..]),
        ("pub fn main() -> i64 { let backing = 1; let mut value = (&backing,0); let mut task = move (value) { &mut value }; let result = (&mut task)(); { let local = 42; result.0 = &local; }; *result.0 }", &["G5013", "G5017"][..]),
    ] {
        for level in ["0", "2"] {
            let outcome = StageZeroCompiler::new().compile(request(source, level));
            assert!(outcome.is_err(), "invalid lifetime or alias was accepted: {source}");
            let diagnostics = outcome.unwrap_err().diagnostics();
            assert!(diagnostics.iter().any(|diagnostic| codes.contains(&diagnostic.code)), "{source}: {diagnostics:#?}");
            let represented = ["(&task)()", "(&mut task)()"].into_iter().flat_map(|call|
                source.match_indices(call).map(|(start, _)| start..start + call.len())).collect::<Vec<_>>();
            assert!(!diagnostics.iter().any(|diagnostic| diagnostic.code == "G5023"
                && diagnostic.primary.as_ref().is_some_and(|span| represented.iter().any(|call|
                    call.contains(&(span.start as usize))))),
                "represented capture storage must reach the actual lifetime or alias obligation: {source}: {diagnostics:#?}");
        }
    }
}

#[test]
fn returned_capture_references_compose_through_receivers_and_products() {
    for source in [
        "pub fn main() -> i64 { let value = 42; let reference = &value; let task = move (reference) { reference }; let result = (&task)(); *result }",
        "fn keep<T>(value:T) -> T { value } fn make<'a>(value:&'a i64) -> () -> &'a i64 { move (value) { value } } pub fn main() -> i64 { let value = 42; let (task,) = keep((make(&value),)); let result = task(); *result }",
        "fn make<'a>(left:&'a i64, right:&'a i64) -> () -> (&'a i64,&'a i64) { move (left,right) { (left,right) } } pub fn main() -> i64 { let left = 20; let right = 22; let (a,b) = make(&left,&right)(); *a + *b }",
        "fn make<'a>(value:&'a (i64,i64)) -> () -> &'a i64 { move (value) { &value.1 } } pub fn main() -> i64 { let value = (0,42); *make(&value)() }",
        "fn make<'a>(value:&'a mut i64) -> () -> &'a mut i64 { move (value) { value } } pub fn main() -> i64 { let mut value = 41; let result = make(&mut value)(); *result = *result + 1; *result }",
        "enum Choice { Left, Right } fn make<'a>(choice:Choice, left:&'a i64, right:&'a i64) -> () -> &'a i64 { move (choice,left,right) { handle choice { Choice::Left => left, Choice::Right => right } } } pub fn main() -> i64 { let left = 20; let right = 22; *make(Choice::Left,&left,&right)() + *make(Choice::Right,&left,&right)() }",
    ] { run(source, 42); }
}

#[test]
fn returned_capture_references_retain_escape_and_mutation_obligations() {
    for (source, code) in [
        ("fn make<'a>(value:&'a i64) -> () -> &'a i64 { move (value) { value } } fn bad() -> &i64 { let value = 42; make(&value)() } pub fn main() -> i64 { *bad() }", "G5013"),
        ("fn make<'a>(value:&'a i64) -> () -> &'a i64 { move (value) { value } } pub fn main() -> i64 { let mut value = 42; let result = make(&value)(); value = 0; *result }", "G5007"),
    ] {
        for level in ["0", "2"] {
            let diagnostics = StageZeroCompiler::new().compile(request(source, level))
                .expect_err("returned capture must keep its backing loan").diagnostics();
            assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == code), "{source}: {diagnostics:#?}");
            let represented = source.find("make(&value)()").unwrap();
            assert!(!diagnostics.iter().any(|diagnostic| diagnostic.code == "G5023"
                && diagnostic.primary.as_ref().is_some_and(|span|
                    span.start as usize >= represented && (span.start as usize) < represented + "make(&value)()".len())),
                "the represented return must reach the actual resource obligation: {diagnostics:#?}");
        }
    }
}

#[test]
fn returned_reference_provenance_does_not_grant_erased_receiver_authority() {
    let source = "fn make<'a>(value:&'a i64) -> () -> &'a i64 { move (value) { value } } pub fn main() -> i64 { let value = 42; let task = make(&value); *(&task)() }";
    for level in ["0", "2"] {
        let diagnostics = StageZeroCompiler::new().compile(request(source, level))
            .expect_err("the erased owned callable contract supplies no borrowed receiver permission").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4180"), "{diagnostics:#?}");
    }
}

fn reject_library_cancellation(source: &str, dependencies: &[&str]) {
    let library = grandiose_stage0::service::STANDARD_LIBRARY_FRAGMENTS.iter()
        .filter(|(path, _)| *path == "src/lib.glorious" || dependencies.contains(path))
        .map(|(_, source)| *source).collect::<Vec<_>>().join("\n");
    for level in ["0", "2"] {
        let mut request = request(source, level);
        request.sources.push(SourceInput::new(PackageKey("std@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(), library.as_bytes()));
        // These are explicit source-contract gap regressions, not passing
        // library-root claims. An arbitrary callback row may abandon a frame
        // retaining an unconstrained linear owner. Preserve that guard while
        // demonstrating that quantified callback selection is no longer the
        // blocker. The small positive fixtures above execute both artifacts.
        let diagnostics = StageZeroCompiler::new().compile(request)
            .expect_err("generic library callbacks still need cancellation-safe owner contracts").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5024"), "O{level}: {diagnostics:#?}");
        assert!(!diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G4198" | "G4147" | "G4169")), "O{level}: {diagnostics:#?}");
    }
}

#[test]
fn generic_callable_value_arguments_still_join_their_receiver_permissions() {
    run(r#"
        fn pair<T>(first: T, second: T) -> (T, T) { (first, second) }
        fn answer() -> i64 { 21 }
        pub fn main() -> i64 {
            let mut count = 20;
            let first: () -> i64 = answer;
            let second: () -> i64 = () -> i64 { count = count + 1; count };
            let (first, second) = pair(first, second);
            first() + second()
        }
    "#, 42);
}

#[test]
fn later_callable_argument_preserves_an_earlier_nominal_generic_identity() {
    run(r#"
        struct Slot<T> { value: T }
        fn select<T>(slot: &mut Slot<T>, value: T) -> T { value }
        fn answer() -> i64 { 21 }
        pub fn main() -> i64 {
            let mut slot: Slot<() -> i64> = Slot { value: answer };
            let selected = select(&mut slot, answer);
            let Slot { value } = slot;
            selected() + value()
        }
    "#, 42);
}

#[test]
fn captured_quantified_callback_receivers_resolve_native_storage_before_borrowing() {
    run(r#"
        type Callback = for<'a> (&'a i64) -> &'a i64;
        fn identity<'a>(value: &'a i64) -> &'a i64 { value }
        fn apply(callback: Callback, value: &i64) -> i64 {
            let task = () -> i64 { *callback(value) };
            task()
        }
        pub fn main() -> i64 { let value = 42; apply(identity, &value) }
    "#, 42);
    run(r#"
        type Callback = for<'a> (&'a i64) -> &'a i64;
        fn identity<'a>(value: &'a i64) -> &'a i64 { value }
        fn make<'a>(callback: Callback, value: &'a i64) -> () -> i64 {
            move (callback, value) { *callback(value) }
        }
        pub fn main() -> i64 { let value = 42; make(identity, &value)() }
    "#, 42);
    run(r#"
        fn answer() -> i64 { 42 }
        fn apply<F>(callback: &F) -> i64
        where for<'a> &'a F: Fn<(), Output=i64, Effects={}> {
            let task = () -> i64 { callback() };
            task()
        }
        pub fn main() -> i64 { let stored = answer; apply(&stored) }
    "#, 42);
}

#[test]
fn returned_callback_cannot_borrow_its_factory_local_capture_slots() {
    let source = r#"
        type Callback = for<'a> (&'a i64) -> &'a i64;
        fn identity<'a>(value: &'a i64) -> &'a i64 { value }
        fn make<'a>(callback: Callback, shared: &'a i64, seed: i64) -> () -> i64 {
            let mut seed = seed;
            () -> i64 { seed = *callback(shared) + 1; seed }
        }
        pub fn main() -> i64 {
            let value = 41;
            let task = make(identity, &value, 0);
            task()
        }
    "#;
    for level in ["0", "2"] {
        let error = match StageZeroCompiler::new().compile(request(source, level)) {
            Err(error) => error,
            Ok(_) => panic!("a returned callback cannot retain borrows of its factory's local slots"),
        };
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5014"),
            "O{level}: {:#?}", error.diagnostics());
    }
}

#[test]
fn capture_formation_retains_source_slots_and_nested_value_dependencies() {
    for source in [
        "fn make<'a>(value: &'a i64) -> () -> i64 { () -> i64 { *value } }
         pub fn main() -> i64 { let value = 42; make(&value)() }",
        "fn make() -> () -> i64 {
            let mut seed = 40; () -> i64 { seed = seed + 1; seed }
         } pub fn main() -> i64 { make()() }",
        "fn make<'a>(value: &'a i64) -> () -> i64 {
            let inner = () -> i64 { *value }; move (inner) { inner() }
         } pub fn main() -> i64 { let value = 42; make(&value)() }",
        "fn make<'a>(value: &'a i64) -> () -> i64 {
            let inner = () -> i64 { *value }; let wrapped = (inner,);
            move (wrapped) { wrapped.0() }
         } pub fn main() -> i64 { let value = 42; make(&value)() }",
        "fn make() -> () -> i64 {
            let value = 42; let reference = &value; move (reference) { *reference }
         } pub fn main() -> i64 { make()() }",
    ] {
        for level in ["0", "2"] {
            let error = match StageZeroCompiler::new().compile(request(source, level)) {
                Err(error) => error,
                Ok(_) => panic!("a capture must retain every dependency on an ending frame: {source}"),
            };
            assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5014"),
                "O{level}: {source}\n{:#?}", error.diagnostics());
        }
    }
}

#[test]
fn owned_capture_handles_do_not_borrow_their_source_slots() {
    run("fn make<'a>(value: &'a i64) -> () -> i64 { move (value) { *value } }
        pub fn main() -> i64 { let value = 42; make(&value)() }", 42);
    run("fn make<'a>(value: &'a i64) -> () -> i64 {
            let inner = move (value) { *value }; move (inner) { inner() }
        } pub fn main() -> i64 { let value = 42; make(&value)() }", 42);
    run("fn make() -> () -> i64 {
            let mut seed = 41; move (seed) { seed = seed + 1; seed }
        } pub fn main() -> i64 { make()() }", 42);
}

#[test]
fn shared_named_callable_is_invoked_through_its_original_borrowed_receiver() {
    run(r#"
        fn answer() -> i64 { 21 }
        fn twice<F>(body: &F) -> i64
        where for<'a> &'a F: Fn<(),Output=i64,Effects={}> {
            body() + body()
        }
        pub fn main() -> i64 { let stored = answer; twice(&stored) }
    "#, 42);
}

#[test]
fn an_owned_capture_can_be_observed_by_a_shared_callback_receiver() {
    run(r#"
        struct Owner { value: i64 }
        impl Use<[0,1]> for Owner {}
        fn twice<F>(body: &F) -> i64
        where for<'a> &'a F: Fn<(),Output=i64,Effects={}> { body() + body() }
        pub fn main() -> i64 {
            let owner = Owner { value: 21 };
            let callback = move (owner) { owner.value };
            twice(&callback)
        }
    "#, 42);
}

#[test]
fn returned_callable_values_preserve_nested_executable_refinements() {
    run(r#"
        fn make(value: i64) -> (i64) -> i64 { (extra: i64) -> i64 { value + extra } }
        pub fn main() -> i64 { make(40)(2) }
    "#, 42);
    run(r#"
        fn make() -> () -> () -> i64 { () -> () -> i64 { () -> i64 { 42 } } }
        pub fn main() -> i64 { make()()() }
    "#, 42);
}

#[test]
fn unique_stored_callable_preserves_capture_state_between_invocations() {
    run(r#"
        struct Stored<F> { callback: F }
        fn twice<'env,Env,F>(body: &mut F) -> i64
        where Env: Environment<'env>,
            for<'a> &'a mut F: Fn<(),Output=i64,Effects={}>,
            for<'a> &'a mut F: RunsIn<&'a mut Env,(),After=Env> {
            body() + body()
        }
        pub fn main() -> i64 {
            let mut counter = 19;
            let callback = () -> i64 { counter = counter + 1; counter };
            let mut stored = Stored { callback: callback };
            let first = twice(&mut stored.callback);
            let next = (&mut stored.callback)();
            first + next
        }
    "#, 63);
}

#[test]
fn stored_callback_impl_bounds_preserve_quantified_environment_evidence() {
    run(r#"
        trait Invoke { fn invoke(value: &mut Self) -> i64; }
        struct Stored<'env,Env,F> { callback: F }
        fn store<'env,Env,F>(callback: F) -> Stored<'env,Env,F>
        where Env: Environment<'env>,
            for<'a> &'a mut F: Fn<(),Output=i64,Effects={}>,
            for<'a> &'a mut F: RunsIn<&'a mut Env,(),After=Env> { Stored { callback: callback } }
        impl<'env,Env,F> Invoke for Stored<'env,Env,F>
        where Env: Environment<'env>,
            for<'a> &'a mut F: Fn<(),Output=i64,Effects={}>,
            for<'a> &'a mut F: RunsIn<&'a mut Env,(),After=Env> {
            fn invoke(value: &mut Self) -> i64 { let callback = &mut value.callback; callback() }
        }
        pub fn main() -> i64 {
            let mut counter = 19;
            let callback = () -> i64 { counter = counter + 1; counter };
            let mut stored = store(callback);
            Invoke::invoke(&mut stored) + Invoke::invoke(&mut stored) + Invoke::invoke(&mut stored)
        }
    "#, 63);
}

#[test]
fn label_transfer_in_a_strict_argument_does_not_invoke_the_borrowed_receiver() {
    run(r#"
        pub fn main() -> i64 {
            let mut count = 40;
            let mut callback = (extra: i64) -> i64 { count = count + extra; count };
            let value = @done: i64 { (&mut callback)(@done(2)) };
            (&mut callback)(value)
        }
    "#, 42);
}

#[test]
fn stored_callback_impl_derives_non_head_output_and_effect_arguments() {
    run(r#"
        trait Invoke {
            type Output; type Effects: EffectRow;
            fn invoke(value: &mut Self) -> <Self as Invoke>::Output / { | <Self as Invoke>::Effects };
        }
        struct Stored<F> { callback: F }
        impl<F,U,e: EffectRow> Invoke for Stored<F>
        where for<'a> &'a mut F: Fn<(),Output=U,Effects=e> {
            type Output = U; type Effects = { | e };
            fn invoke(value: &mut Self) -> U / { | e } { let callback = &mut value.callback; callback() }
        }
        fn answer() -> i64 { 21 }
        pub fn main() -> i64 {
            let mut stored = Stored { callback: answer };
            Invoke::invoke(&mut stored) + Invoke::invoke(&mut stored)
        }
    "#, 42);
}

#[test]
fn non_head_callable_arguments_cannot_capture_a_quantified_region() {
    for (declarations, equality) in [(r#"
        fn callback<'a>(value: &'a i64) -> &'a i64 { value }
    "#, "Output=U,Effects={}"), (r#"
        effect Observe<'a> { [1,1] observe(value: &'a i64) -> i64; }
        fn callback<'a>(value: &'a i64) -> i64 / Observe<'a> { Observe::observe(value) }
    "#, "Output=U,Effects=e")] {
        let source = format!(r#"
            trait Select {{}}
            struct Stored<F> {{ callback: F }}
            impl<F,U,e: EffectRow> Select for Stored<F>
            where for<'a> &'a F: Fn<(&'a i64,),{equality}> {{}}
            fn require<T>(value: &T) where T: Select {{}}
            {declarations}
            pub fn main() -> i64 {{ let stored = Stored {{ callback: callback }}; require(&stored); 42 }}
        "#);
        for level in ["0", "2"] {
            let diagnostics = StageZeroCompiler::new().compile(request(&source, level))
                .expect_err("an impl binder outside for cannot capture its region").diagnostics();
            assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G4140" | "G4141" | "G4143" | "G5017")), "{diagnostics:#?}");
            assert!(!diagnostics.iter().any(|diagnostic| diagnostic.code == "G4198"), "{diagnostics:#?}");
        }
    }
}

#[test]
fn environment_scope_retains_the_stored_capture_lifetimes() {
    let prelude = r#"
        fn require_static<Env,F>(callback: &F) -> i64
        where Env: Environment<'static>,
            for<'a> &'a F: Fn<(),Output=i64,Effects={}>,
            for<'a> &'a F: RunsIn<&'a Env,(),After=Env> { callback() }
    "#;
    run(&format!(r#"{prelude}
        fn answer() -> i64 {{ 42 }}
        pub fn main() -> i64 {{ let callback = answer; require_static(&callback) }}
    "#), 42);
    run(&format!(r#"{prelude}
        pub fn main() -> i64 {{ let value = 42; let callback = move (value) {{ value }}; require_static(&callback) }}
    "#), 42);
    let direct = format!(r#"{prelude}
            pub fn main() -> i64 {{ let value = 42; let borrowed = &value; let callback = move (borrowed) {{ *borrowed }}; require_static(&callback) }}
        "#);
    let contextual = r#"
        struct Stored<'env,Env,F> { callback: F }
        fn store<'env,Env,F>(callback: F) -> Stored<'env,Env,F>
        where Env: Environment<'env>,
            for<'a> &'a F: Fn<(),Output=i64,Effects={}>,
            for<'a> &'a F: RunsIn<&'a Env,(),After=Env> { Stored { callback: callback } }
        fn demand_static<Env,F>(stored: &Stored<'static,Env,F>) -> i64 { 42 }
        pub fn main() -> i64 {
            let value = 42; let borrowed = &value;
            let callback = move (borrowed) { *borrowed };
            let stored = store(callback);
            demand_static(&stored)
        }
    "#;
    for source in [direct.as_str(), contextual] {
      for level in ["0", "2"] {
        let diagnostics = StageZeroCompiler::new().compile(request(&source, level))
            .expect_err("a borrowed local capture is not a static environment").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4188"), "{diagnostics:#?}");
      }
    }
}

#[test]
fn borrowed_callable_predicates_reject_wrong_access_and_post_state() {
    for source in [r#"
        fn shared<F>(body: &F) -> i64 where for<'a> &'a F: Fn<(),Output=i64,Effects={}> { body() }
        pub fn main() -> i64 {
            let mut counter = 41;
            let callback = () -> i64 { counter = counter + 1; counter };
            shared(&callback)
        }
    "#, r#"
        fn wrong<'env,Env,F>(body: &mut F) -> i64
        where Env: Environment<'env>, for<'a> &'a mut F: Fn<(),Output=i64,Effects={}>,
            for<'a> &'a mut F: RunsIn<&'a mut Env,(),After=i64> { body() }
        pub fn main() -> i64 { let mut callback = () -> i64 { 42 }; wrong(&mut callback) }
    "#] {
        for level in ["0", "2"] {
            let diagnostics = StageZeroCompiler::new().compile(request(source, level)).expect_err("borrowed evidence must be exact").diagnostics();
            assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G4188" | "G4167")), "{diagnostics:#?}");
            assert!(!diagnostics.iter().any(|diagnostic| diagnostic.code == "G4198"), "{diagnostics:#?}");
        }
    }
}

#[test]
fn stored_function_values_keep_ordinary_and_quantified_residual_predicates() {
    for universal in [false, true] {
        let (implementation, predicate) = if universal {
            ("impl<'a> Marker for &'a i64 {}", "for<'a> &'a T: Marker")
        } else { ("impl Marker for i64 {}", "T: Marker") };
        run(&format!(r#"
            trait Marker {{}}
            {implementation}
            fn checked<T>(value: T) -> T where {predicate} {{ value }}
            pub fn main() -> i64 {{ let checked_value: (i64) -> i64 = checked; checked_value(42) }}
        "#), 42);
        for level in ["0", "2"] {
            let source = format!(r#"
                trait Marker {{}}
                fn checked<T>(value: T) -> T where {predicate} {{ value }}
                pub fn main() -> i64 {{ let checked_value: (i64) -> i64 = checked; checked_value(42) }}
            "#);
            let diagnostics = StageZeroCompiler::new().compile(request(&source, level))
                .expect_err("stored functions cannot erase residual obligations").diagnostics();
            assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G4140" | "G4143")), "{diagnostics:#?}");
            assert!(!diagnostics.iter().any(|diagnostic| diagnostic.code == "G4198"), "{diagnostics:#?}");
        }
    }
    run(r#"
        fn answer() -> i64 { 21 }
        fn checked<F>(body: F) -> i64
        where F: Use<[0,1]>, for<'a> &'a F: Fn<(),Output=i64,Effects={}> { (&body)() + (&body)() }
        pub fn main() -> i64 { let stored = checked; stored(answer) }
    "#, 42);
}

#[test]
fn written_callable_abis_cannot_erase_residual_invocation_predicates() {
    for (predicate, implementation) in [("T: Marker", "impl Marker for i64 {}"),
        ("for<'a> &'a T: Marker", "impl<'a> Marker for &'a i64 {}")]
    {
        for boundary in [r#"
            fn apply(callback: (i64) -> i64) -> i64 { callback(42) }
            pub fn main() -> i64 { apply(checked) }
        "#, r#"
            fn make() -> (i64) -> i64 { checked }
            pub fn main() -> i64 { make()(42) }
        "#, r#"
            struct Holder { callback: (i64) -> i64 }
            pub fn main() -> i64 { let holder = Holder { callback: checked }; holder.callback(42) }
        "#, r#"
            pub fn main() -> i64 { let [callback]: [(i64) -> i64;1] = [checked]; callback(42) }
        "#, r#"
            struct Holder<T> { callback: T }
            fn apply(value: Holder<(i64) -> i64>) -> i64 { value.callback(42) }
            pub fn main() -> i64 { apply(Holder { callback: checked }) }
        "#, r#"
            effect Invoke { [1,1] invoke(callback: (i64) -> i64) -> i64; }
            pub fn main() -> i64 { handle Invoke::invoke(checked) { Invoke::invoke(callback) => callback(42) } }
        "#] {
            let source = format!("trait Marker {{}} fn checked<T>(value: T) -> T where {predicate} {{ value }} {boundary}");
            for level in ["0", "2"] {
                let diagnostics = StageZeroCompiler::new().compile(request(&source, level))
                    .expect_err("an ABI must retain or prove the callable's invocation predicates").diagnostics();
                assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4143"), "{diagnostics:#?}");
                assert!(!diagnostics.iter().any(|diagnostic| diagnostic.code == "G4198"), "{diagnostics:#?}");
            }
            run(&format!("{source} {implementation}"), 42);
        }
    }
}

#[test]
fn replacement_cannot_retain_the_previous_callables_borrowed_authority() {
    let source = r#"
        struct Owner {}
        impl Use<[0,1]> for Owner {}
        pub fn main() -> i64 {
            let owner = Owner {};
            let mut callback = () -> i64 { 21 };
            callback = () -> i64 { let taken = move owner; 42 };
            (&callback)()
        }
    "#;
    for level in ["0", "2"] {
        let diagnostics = StageZeroCompiler::new().compile(request(source, level))
            .expect_err("replacing an observer with a consumer cannot keep shared access").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G4180" | "G4188")), "{diagnostics:#?}");
    }
}

#[test]
fn borrowed_callback_effects_cannot_bypass_linear_cancellation_checks() {
    let prelude = r#"
        struct Token {} impl Use<[1,1]> for Token {}
        fn consume(value: Token) -> i64 { let Token {} = value; 42 }
    "#;
    for body in [r#"
        effect Ask { [0,1] ask() -> i64; }
        fn ask() -> i64 / Ask { Ask::ask() }
        pub fn main() -> i64 {
            handle { let value = Token {}; let callback = ask; (&callback)(); consume(value) }
            { Ask::ask() with _ => 42 }
        }
    "#, r#"
        fn invoke<F,e: EffectRow>(body: &mut F) -> i64 / { | e }
        where for<'a> &'a mut F: Fn<(),Output=i64,Effects=e> {
            let value = Token {}; body(); consume(value)
        }
        pub fn main() -> i64 { 42 }
    "#] {
        for level in ["0", "2"] {
            let diagnostics = StageZeroCompiler::new().compile(request(&format!("{prelude}{body}"), level))
                .expect_err("borrowed callback cancellation must retain linear obligations").diagnostics();
            assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5024"), "{diagnostics:#?}");
        }
    }
    run(&format!(r#"{prelude}
        fn invoke<F>(body: &F) -> i64 where for<'a> &'a F: Fn<(),Output=i64,Effects={{}}> {{
            let value = Token {{}}; body(); consume(value)
        }}
        fn answer() -> i64 {{ 0 }}
        pub fn main() -> i64 {{ let callback = answer; invoke(&callback) }}
    "#), 42);
}

#[test]
fn fresh_and_decoded_vm_reconstruct_borrowed_capture_authority() {
    use grandiose_stage0::{VmInstruction, VmType, decode_program, encode_program, verify_vm_program};
    for (shared, source) in [(true, r#"
        pub fn main() -> i64 {
            let mut count = 41;
            let callback = () -> i64 { count = count + 1; count };
            callback()
        }
    "#), (false, r#"
        struct Owner {} impl Use<[0,1]> for Owner {}
        pub fn main() -> i64 {
            let owner = Owner {};
            let callback = () -> i64 { let taken = move owner; 42 };
            callback()
        }
    "#)] {
        for level in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(request(source, level)).unwrap().artifact.unwrap();
            assert_eq!(artifact.run_i64().unwrap(), 42);
            let mut candidate = decode_program(&artifact.canonical_bytes()).unwrap();
            let mut changed = 0;
            let mut replacements = Vec::new();
            for function in candidate.functions.values_mut() {
                for instruction in &function.instructions {
                    if let VmInstruction::MakeCallable { dst, captures, .. } = instruction
                        && !captures.is_empty()
                        && let VmType::Callable { shared_receiver, unique_receiver, .. } = &function.registers[*dst as usize] {
                        assert!(!if shared { *shared_receiver } else { *unique_receiver });
                        let from = function.registers[*dst as usize].clone();
                        let mut to = from.clone();
                        let VmType::Callable { shared_receiver, unique_receiver, .. } = &mut to else { unreachable!() };
                        *shared_receiver = shared; *unique_receiver = true;
                        replacements.push((from, to));
                        changed += 1;
                    }
                }
            }
            for function in candidate.functions.values_mut() {
                for ty in &mut function.registers {
                    if let Some((_, replacement)) = replacements.iter().find(|(original, _)| original == ty) {
                        *ty = replacement.clone();
                    }
                }
            }
            assert!(changed > 0, "O{level} must retain a concrete capture producer");
            candidate.fingerprint = candidate.computed_fingerprint();
            for result in [verify_vm_program(candidate.clone()), decode_and_verify_program(&encode_program(&candidate))] {
                assert!(matches!(result, Err(grandiose_stage0::VmArtifactError::InvalidCallableEnvironment {
                    message: "borrowed callable authority is not established by its executable capture accesses"
                })), "O{level}, shared={shared}: {result:?}");
            }
        }
    }
}

#[test]
fn fresh_and_decoded_vm_preserve_receiver_variance_at_indirect_boundaries() {
    use grandiose_stage0::{DefKey, VmInstruction, VmType, decode_program, encode_program, verify_vm_program};
    fn weaken_callback(ty: &mut VmType) {
        match ty {
            VmType::Callable { shared_receiver, unique_receiver, parameters, .. } => {
                if parameters.is_empty() { *shared_receiver = false; *unique_receiver = false; }
                for parameter in parameters { weaken_callback(parameter); }
            }
            VmType::Reference { referent, .. } => weaken_callback(referent),
            _ => {}
        }
    }
    for (higher_order, source) in [(true, r#"
        fn answer() -> i64 { 42 }
        fn read<F>(callback: F) -> i64
        where F: Use<[0,1]>, for<'a> &'a F: Fn<(),Output=i64,Effects={}> { (&callback)() }
        fn apply<W,F>(wrapper: W, callback: F) -> i64
        where W: Fn<(F,),Output=i64,Effects={}> { wrapper(callback) }
        pub fn main() -> i64 { apply(read, answer) }
    "#), (false, r#"
        fn answer() -> i64 { 42 }
        fn observe<F>(callback: &mut F) -> i64 { 42 }
        pub fn main() -> i64 { let mut callback = answer; observe(&mut callback) }
    "#)] {
        for level in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(request(source, level))
                .unwrap_or_else(|error| panic!("O{level}: {:#?}", error.diagnostics())).artifact.unwrap();
            assert_eq!(artifact.run_i64().unwrap(), 42);
            let mut candidate = decode_program(&artifact.canonical_bytes()).unwrap();
            let mut changed = 0;
            let mut cleanup_copies = BTreeMap::new();
            for function in candidate.functions.values_mut() {
                let selected = if higher_order {
                    function.parameters == 2 && matches!(function.registers.first(), Some(VmType::Callable { parameters, .. })
                        if matches!(parameters.as_slice(), [VmType::Callable { .. }]))
                } else {
                    function.parameters == 1 && matches!(function.registers.first(), Some(VmType::Reference { unique: true, referent })
                        if matches!(referent.as_ref(), VmType::Callable { .. }))
                };
                if selected {
                    for ty in &mut function.registers { weaken_callback(ty); }
                    // Keep ordinary cleanup ABIs consistent with the forged
                    // owner type, so rejection must concern receiver variance
                    // rather than an unrelated stale destruction signature.
                    for instruction in &mut function.instructions {
                        if let VmInstruction::DeclareFrameCleanup { actions } = instruction {
                            for action in actions {
                                let replacement = DefKey(Digest::of_parts([
                                    b"receiver-variance-cleanup".as_slice(), action.destructor.0.as_bytes().as_slice(),
                                ]));
                                cleanup_copies.insert(action.destructor, replacement);
                                action.destructor = replacement;
                            }
                        }
                    }
                    changed += 1;
                }
            }
            assert_eq!(changed, 1, "one checked boundary must be forged");
            for (original, replacement) in cleanup_copies {
                let mut cleanup = candidate.functions[&original].clone();
                cleanup.definition = replacement;
                for ty in &mut cleanup.registers { weaken_callback(ty); }
                assert!(candidate.functions.insert(replacement, cleanup).is_none());
            }
            candidate.fingerprint = candidate.computed_fingerprint();
            for result in [verify_vm_program(candidate.clone()), decode_and_verify_program(&encode_program(&candidate))] {
                assert!(matches!(result, Err(grandiose_stage0::VmArtifactError::TypeMismatch { .. })),
                    "O{level}, higher_order={higher_order}: {result:?}");
            }
        }
    }
}

#[test]
fn effect_payloads_cannot_gain_borrowed_receiver_authority_across_frames() {
    use grandiose_stage0::{DefKey, VmInstruction, VmType, decode_program, encode_program, verify_vm_program};
    let source = r#"
        struct Owner {} impl Use<[0,1]> for Owner {}
        effect Invoke { [1,1] invoke(callback: () -> i64) -> i64; }
        fn send(callback: () -> i64) -> i64 / Invoke { Invoke::invoke(callback) }
        pub fn main() -> i64 {
            let owner = Owner {};
            let callback = () -> i64 { let taken = move owner; 42 };
            handle send(callback) { Invoke::invoke(callback) => callback() }
        }
    "#;
    for level in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(source, level))
            .unwrap_or_else(|error| panic!("O{level}: {:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        let mut candidate = decode_program(&artifact.canonical_bytes()).unwrap();
        let mut changed = 0;
        let mut cleanup_copies = BTreeMap::new();
        for function in candidate.functions.values_mut() {
            let mut changed_owners = std::collections::BTreeSet::new();
            for instruction in &function.instructions {
                let destinations = match instruction {
                    VmInstruction::InstallHandler { payload_destinations, .. }
                    | VmInstruction::InstallHandlerOwned { payload_destinations, .. } => payload_destinations,
                    _ => continue,
                };
                for destination in destinations {
                    if let VmType::Callable { shared_receiver, unique_receiver, .. } = &mut function.registers[*destination as usize] {
                        assert!(!*shared_receiver && !*unique_receiver);
                        *shared_receiver = true;
                        *unique_receiver = true;
                        changed_owners.insert(*destination);
                        changed += 1;
                    }
                }
            }
            // Preserve cleanup's exact owner ABI, so this candidate reaches
            // the cross-frame payload check rather than a stale local type.
            for instruction in &mut function.instructions {
                if let VmInstruction::DeclareFrameCleanup { actions } = instruction {
                    for action in actions {
                        if changed_owners.contains(&action.owner) {
                            let replacement = DefKey(Digest::of_parts([
                                b"effect-receiver-cleanup".as_slice(), action.destructor.0.as_bytes().as_slice(),
                            ]));
                            cleanup_copies.insert(action.destructor, (replacement, function.registers[action.owner as usize].clone()));
                            action.destructor = replacement;
                        }
                    }
                }
            }
        }
        assert_eq!(changed, 1, "one cross-frame handler payload must be forged");
        for (original, (replacement, owner)) in cleanup_copies {
            let mut cleanup = candidate.functions[&original].clone();
            cleanup.definition = replacement;
            let old = cleanup.registers[0].clone();
            for ty in &mut cleanup.registers { if *ty == old { *ty = owner.clone(); } }
            assert!(candidate.functions.insert(replacement, cleanup).is_none());
        }
        candidate.fingerprint = candidate.computed_fingerprint();
        for result in [verify_vm_program(candidate.clone()), decode_and_verify_program(&encode_program(&candidate))] {
            assert!(matches!(result, Err(grandiose_stage0::VmArtifactError::MalformedEncoding {
                message: "program effect operation ABI declarations disagree"
            })), "O{level}: {result:?}");
        }
    }
}

#[test]
fn standard_array_callback_contract_reaches_the_cancellation_guard() {
    reject_library_cancellation(r#"
        use std::*;
        pub fn main() -> i64 {
            let mut count = 18;
            let mut produce = (index: usize) -> i64 { count = count + 1; count };
            let [a,b,c]: [i64;3] = array_from_fn(&mut produce);
            let next = (&mut produce)(3);
            a + b + c + next
        }
    "#, &["src/foundation.glorious", "src/memory.glorious", "src/array.glorious"]);
}

#[test]
fn standard_iterator_callback_contract_reaches_the_cancellation_guard() {
    let source = r#"
        use std::*;
        fn double(value: i64) -> i64 { value * 2 }
        pub fn main() -> i64 {
            let mut values: Vec<i64> = Vec::new(); Vec::push(&mut values, 21);
            let mut mapped = map_iter(Vec::into_iter(values), double);
            handle Iterator::next(&mut mapped) { Result::Ok(value) => value, Result::Err(_) => 0 }
        }
    "#;
    reject_library_cancellation(&source, &["src/foundation.glorious", "src/memory.glorious", "src/iterator.glorious", "src/iterator_callbacks.glorious"]);
}
