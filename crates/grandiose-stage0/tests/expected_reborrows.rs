use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath,
    PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program,
};
use std::collections::BTreeMap;

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("reborrow-cases@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"expected-reborrow-cases")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), optimization.into())]),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

fn accepts(source: &str) {
    accepts_with_dependency(source, None);
}

fn accepts_with_dependency(source: &str, dependency: Option<&str>) {
    for optimization in ["0", "2"] {
        let mut input = request(source, optimization);
        if let Some(dependency) = dependency {
            input.sources.push(SourceInput::new(PackageKey("views@0.1.0".into()),
                LogicalPath::parse("src/lib.glorious").unwrap(), dependency.as_bytes()));
        }
        let result = StageZeroCompiler::new().compile(input).unwrap();
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let artifact = result.artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

fn rejects(source: &str, codes: &[&str]) {
    for optimization in ["0", "2"] {
        let error = StageZeroCompiler::new().compile(request(source, optimization)).expect_err("invalid reference conversion must fail");
        assert!(error.diagnostics().iter().any(|diagnostic| codes.contains(&diagnostic.code)), "{error:?}");
    }
}

#[test]
fn scalar_updates_through_a_borrowed_carrier_preserve_reference_provenance() {
    accepts("struct View<'a,T> { value: &'a T, length: usize } fn reset<'a,T>(view: View<'a,T>) -> &'a T { let mut view = view; (*&mut view).length = 0; view.value } pub fn main() -> i64 { let number = 42; *reset(View { value: &number, length: 1 }) }");
}

#[test]
fn captured_reference_reborrows_use_their_own_checked_callable_access() {
    for action in [
        "let update = move (pointer) { bump(pointer); }; update();",
        "let update = () -> () { bump(pointer); }; update();",
        "let outer = move (pointer) { let inner = move (pointer) { bump(pointer); }; inner(); }; outer();",
    ] {
        accepts(&captured_reference_program(action));
    }
    rejects("fn write(value: &mut i64) { *value = 42; } pub fn main() -> i64 { let value = 41; let pointer = &value; let update = move (pointer) { write(pointer); }; update(); value }", &["G4107", "G5017", "G5006"]);
    rejects("fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let mut value = 41; let pointer = &mut value; let delayed = move (pointer) { read(pointer) }; value = 42; delayed() }", &["G5007", "G5006", "G5008"]);
}

fn captured_reference_program(action: &str) -> String {
    format!("fn bump(value: &mut i64) {{ *value = *value + 1; }} pub fn main() -> i64 {{ let mut value = 41; let pointer = &mut value; {action} value }}")
}

#[test]
fn checked_borrow_temporaries_evaluate_once_before_projection() {
    accepts("fn fresh(count: &mut i64) -> (i64, i64) { *count = *count + 1; (40, 2) } pub fn main() -> i64 { let mut count = 0; let value = &fresh(&mut count); value.0 + value.1 + count - 1 }");
}

#[test]
fn checked_captured_reference_reborrows_execute_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let source = captured_reference_program("let update = move (pointer) { bump(pointer); }; update();");
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(&source, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("source O{optimization}: {error:#?}"));
        // SAFETY: compile and execute only the locally checked safe program.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }.unwrap().0, 42);
    }
}

#[test]
fn expected_shared_reborrow_releases_before_later_unique_mutation() {
    accepts("fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let mut value = 10; let unique = &mut value; let a = read(unique); let b = read(unique); *unique = a + b + 22; *unique }");
}

#[test]
fn expected_shared_reborrow_preserves_returned_loan_and_computed_origin() {
    accepts("fn relay<'a>(value: &'a mut i64) -> &'a mut i64 { value } fn shared<'a>(value: &'a i64) -> &'a i64 { value } pub fn main() -> i64 { let mut value = 41; let unique = &mut value; let child = shared(relay(unique)); let result = *child; value = result + 1; value }");
    rejects("fn shared<'a>(value: &'a i64) -> &'a i64 { value } pub fn main() -> i64 { let mut value = 41; let unique = &mut value; let child = shared(unique); *unique = 42; *child }", &["G5004"]);
}

#[test]
fn expected_shared_reborrow_works_for_generic_calls_and_typed_bindings() {
    accepts("fn shared<'a, T>(value: &'a T) -> &'a T { value } pub fn main() -> i64 { let mut value = 41; let unique = &mut value; let child: &i64 = unique; let a = *child; let b = *shared(unique); *unique = a + b - 40; *unique }");
}

#[test]
fn expected_shared_reborrow_never_upgrades_shared_authority_or_extends_storage() {
    rejects("fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { read(42) }", &["G4107", "G5017"]);
    rejects("fn write(value: &mut i64) -> i64 { *value = 42; *value } pub fn main() -> i64 { let value = 1; write(&value) }", &["G4107", "G5017"]);
    rejects("fn escape() -> &'static i64 { let mut value = 42; let unique = &mut value; unique } pub fn main() -> i64 { *escape() }", &["G5017", "G5006", "G5011"]);
}

#[test]
fn expected_shared_reborrow_tracks_resumed_and_abandoned_effect_calls() {
    accepts("effect Ask { [1,1] get() -> i64; } fn read(value: &i64) -> i64 / {Ask} { *value + Ask::get() } pub fn main() -> i64 { let mut value = 20; let unique = &mut value; let answer = handle read(unique) { Ask::get() with k => k(1) }; *unique = answer * 2; *unique }");
    // Explicitly discard the optional continuation: an ordinary clause without
    // `with` resumes with its value and would evaluate the suspended `+ *value`.
    accepts("effect Ask { [0,1] get() -> i64; } fn read(value: &i64) -> i64 / {Ask} { Ask::get() + *value } pub fn main() -> i64 { let mut value = 20; let unique = &mut value; let answer = handle read(unique) { Ask::get() with _ => 41 }; *unique = answer + 1; *unique }");
}

#[test]
fn expected_unique_reborrow_can_be_used_again_after_call() {
    accepts("fn bump(value: &mut i64) { *value = *value + 1; } pub fn main() -> i64 { let mut value = 40; let unique = &mut value; bump(unique); bump(unique); *unique }");
    rejects("fn relay<'a>(value: &'a mut i64) -> &'a mut i64 { value } pub fn main() -> i64 { let mut value = 41; let unique = &mut value; let child = relay(unique); *unique = 42; *child }", &["G5004"]);
}

#[test]
fn borrowed_record_returns_its_stored_reference_region() {
    accepts("struct Window<'a> { storage: &'a i64, position: i64 } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } pub fn main() -> i64 { let backing = 42; let mut window = Window { storage: &backing, position: 0 }; let result = get(&window); window.position = 1; *result }");
}

#[test]
fn stored_reference_outlives_its_short_record_borrow() {
    accepts("struct Window<'a> { storage: &'a i64 } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } pub fn main() -> i64 { let backing = 42; let result = { let window = Window { storage: &backing }; get(&window) }; *result }");
    accepts("struct Window<'a> { storage: &'a i64 } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } fn wrap<'a>(storage: &'a i64) -> Window<'a> { Window { storage: storage } } pub fn main() -> i64 { let backing = 42; *get(&wrap(&backing)) }");
    accepts("struct Window<'a> { storage: &'a i64 } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } fn pass<'a>(incoming: &'a i64) -> &'a i64 { let holder = Window { storage: incoming }; let borrowed = &holder; let local = 0; let holder = Window { storage: &local }; get(borrowed) } pub fn main() -> i64 { let value = 42; *pass(&value) }");
}

#[test]
fn unique_carrier_assignment_replaces_its_stored_reference_provenance() {
    accepts("struct Window<'a> { storage: &'a i64 } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } pub fn main() -> i64 { let mut first = 40; let second = 1; let mut window = Window { storage: &first }; let unique = &mut window; (*unique).storage = &second; first = 41; *get(unique) + first }");
    rejects("struct Window<'a> { storage: &'a i64 } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } pub fn main() -> i64 { let first = 40; let mut second = 1; let mut window = Window { storage: &first }; let unique = &mut window; (*unique).storage = &second; let result = get(unique); second = 42; *result }", &["G5007"]);
}

#[test]
fn generic_stored_references_keep_computed_receiver_provenance() {
    accepts("struct Window<'a,T> { storage: &'a T } struct Wrapped<T> { inner: T } fn get<'a,T>(value: &Wrapped<Window<'a,T>>) -> &'a T { value.inner.storage } fn relay<'a,T>(value: &'a mut T) -> &'a mut T { value } pub fn main() -> i64 { let backing = 42; let mut carrier = Wrapped { inner: Window { storage: &backing } }; let result = get(relay(&mut carrier)); *result }");
    accepts("struct Window<'a> { storage: &'a i64 } struct Wrapped<'a,'b> { padding: &'b i64, inner: Window<'a> } fn wrap<'a,'b>(value: &'a i64, padding: &'b i64) -> Wrapped<'a,'b> { Wrapped { padding: padding, inner: Window { storage: value } } } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } fn pass<'a>(value: &'a i64) -> &'a i64 { let local = 0; get(&wrap(value, &local).inner) } pub fn main() -> i64 { let value = 42; *pass(&value) }");
}

#[test]
fn stored_reference_keeps_backing_storage_borrowed() {
    rejects("struct Window<'a> { storage: &'a i64 } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } pub fn main() -> i64 { let mut backing = 41; let window = Window { storage: &backing }; let result = get(&window); backing = 42; *result }", &["G5007"]);
    rejects("struct Window<'a> { storage: &'a i64 } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } fn escape<'a>() -> &'a i64 { let backing = 42; let window = Window { storage: &backing }; get(&window) } pub fn main() -> i64 { *escape() }", &["G5017", "G5013", "G5006", "G5011"]);
    rejects("fn bump(value: &mut i64) { *value = *value + 1; } pub fn main() -> i64 { let mut value = 40; let unique = &mut value; bump(move unique); bump(unique); value }", &["G5001", "G5003"]);
    rejects("struct Window<'a> { storage: &'a i64 } fn choose<'a>(left: &Window<'a>, right: &Window<'a>, pick: i64) -> &'a i64 { handle pick { 0 => left.storage, _ => right.storage } } pub fn main() -> i64 { let first = 41; let mut second = 42; let left = Window { storage: &first }; let right = Window { storage: &second }; let result = choose(&left, &right, 1); second = 43; *result }", &["G5007"]);
    accepts("struct Window<'a> { storage: &'a i64 } fn get<'a>(value: &Window<'a>) -> &'a i64 { value.storage } pub fn main() -> i64 { let first = 40; let second = 2; let mut window = Window { storage: &first }; let old = get(&window); window.storage = &second; *old + *get(&window) }");
}

#[test]
fn nested_unique_reborrow_uses_the_carrier_access_region() {
    accepts("struct Window<'a> { storage: &'a mut i64 } fn get<'a,'b>(value: &'b mut Window<'a>) -> &'b mut i64 { &mut *value.storage } pub fn main() -> i64 { let mut backing = 40; let mut window = Window { storage: &mut backing }; let a = get(&mut window); *a = *a + 1; let b = get(&mut window); *b = *b + 1; backing }");
    rejects("struct Window<'a> { storage: &'a mut i64 } fn get<'a,'b>(value: &'b mut Window<'a>) -> &'a mut i64 { &mut *value.storage } pub fn main() -> i64 { 42 }", &["G5017"]);
    rejects("struct Window<'a> { storage: &'a mut i64 } fn get<'a>(value: &Window<'a>) -> &'a mut i64 { value.storage } pub fn main() -> i64 { 42 }", &["G4141", "G5004"]);
    accepts("fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let mut value = 42; read(&mut value) }");
    rejects("struct Window<'a> { storage: &'a mut i64 } fn get<'a,'b>(value: &'b mut Window<'a>) -> &'b mut i64 { &mut *value.storage } pub fn main() -> i64 { let mut backing = 41; let mut window = Window { storage: &mut backing }; let child = get(&mut window); *window.storage = 42; *child }", &["G5004"]);
}

#[test]
fn direct_referent_replacement_updates_backing_storage_not_its_carrier() {
    accepts("struct Slot<'a> { value: &'a i64 } struct Carrier<'a,'b> { target: &'b mut Slot<'a> } pub fn main() -> i64 { let first = 40; let second = 42; let mut slot = Slot { value: &first }; let mut carrier = Carrier { target: &mut slot }; let target = &mut *carrier.target; *target = Slot { value: &second }; *carrier.target.value }");
}

#[test]
fn returned_referent_replacement_updates_backing_storage_not_its_carrier() {
    accepts("struct Slot<'a> { value: &'a i64 } struct Carrier<'a,'b> { target: &'b mut Slot<'a> } fn get<'a,'b,'c>(carrier: &'c mut Carrier<'a,'b>) -> &'c mut Slot<'a> { &mut *carrier.target } pub fn main() -> i64 { let first = 40; let second = 42; let mut slot = Slot { value: &first }; let mut carrier = Carrier { target: &mut slot }; let target = get(&mut carrier); *target = Slot { value: &second }; *get(&mut carrier).value }");
}

#[test]
fn returned_referent_replacement_retains_the_new_backing_loan() {
    rejects("struct Slot<'a> { value: &'a i64 } struct Carrier<'a,'b> { target: &'b mut Slot<'a> } fn get<'a,'b,'c>(carrier: &'c mut Carrier<'a,'b>) -> &'c mut Slot<'a> { &mut *carrier.target } pub fn main() -> i64 { let first = 40; let mut second = 42; let mut slot = Slot { value: &first }; let mut carrier = Carrier { target: &mut slot }; let target = get(&mut carrier); *target = Slot { value: &second }; second = 43; *get(&mut carrier).value }", &["G5007"]);
}

#[test]
fn returned_referent_keeps_its_carrier_suspended() {
    rejects("struct Window<'a> { storage: &'a mut i64 } fn get<'a,'b>(value: &'b mut Window<'a>) -> &'b mut i64 { &mut *value.storage } pub fn main() -> i64 { let mut backing = 41; let mut replacement = 42; let mut window = Window { storage: &mut backing }; let child = get(&mut window); window = Window { storage: &mut replacement }; *child }", &["G5004", "G5007"]);
}

#[test]
fn returned_referent_targets_survive_aggregate_and_capture_transfers() {
    accepts("struct Window<'a> { storage: &'a mut i64 } fn get<'a,'b>(value: &'b mut Window<'a>) -> &'b mut i64 { &mut *value.storage } pub fn main() -> i64 { let mut backing = 40; let mut window = Window { storage: &mut backing }; let handles = (get(&mut window),); *handles.0 = 42; backing }");
    accepts("struct Window<'a> { storage: &'a mut i64 } fn get<'a,'b>(value: &'b mut Window<'a>) -> &'b mut i64 { &mut *value.storage } pub fn main() -> i64 { let mut backing = 40; let mut window = Window { storage: &mut backing }; let target = get(&mut window); let update = move (target) { *target = 42; }; update(); backing }");
}

#[test]
fn alternative_referent_targets_keep_weak_replacement_provenance() {
    accepts("struct Slot<'a> { value: &'a i64 } fn choose<'a,'b>(left: &'b mut Slot<'a>, right: &'b mut Slot<'a>, pick: i64) -> &'b mut Slot<'a> { handle pick { 0 => left, _ => right } } pub fn main() -> i64 { let first = 40; let second = 1; let replacement = 42; let mut left = Slot { value: &first }; let mut right = Slot { value: &second }; let mut pick = 1; pick = 0; let target = choose(&mut left, &mut right, pick); *target = Slot { value: &replacement }; *left.value + *right.value - 1 }");
    rejects("struct Slot<'a> { value: &'a i64 } fn choose<'a,'b>(left: &'b mut Slot<'a>, right: &'b mut Slot<'a>, pick: i64) -> &'b mut Slot<'a> { handle pick { 0 => left, _ => right } } pub fn main() -> i64 { let first = 40; let second = 1; let mut replacement = 42; let mut left = Slot { value: &first }; let mut right = Slot { value: &second }; let mut pick = 1; pick = 0; let target = choose(&mut left, &mut right, pick); *target = Slot { value: &replacement }; replacement = 43; *left.value + *right.value - 1 }", &["G5007"]);
}

#[test]
fn helper_replacement_cannot_leave_a_stale_reference_target() {
    accepts("struct Slot<'a> { value: &'a i64 } fn set<'a>(slot: &mut Slot<'a>, value: &'a i64) { slot.value = value; } pub fn main() -> i64 { let first = 40; let second = 2; let mut slot = Slot { value: &first }; let old = slot.value; set(&mut slot, &second); *old + *slot.value }");
    rejects("struct Slot<'a> { value: &'a i64 } fn set<'a>(slot: &mut Slot<'a>, value: &'a i64) { slot.value = value; } pub fn main() -> i64 { let first = 40; let mut second = 42; let mut slot = Slot { value: &first }; set(&mut slot, &second); second = 43; *slot.value }", &["G5007"]);
}

#[test]
fn helper_reference_stores_respect_directional_outlives_contracts() {
    accepts("struct Slot<'a> { value: &'a i64 } fn set<'a,'b>(slot: &mut Slot<'b>, value: &'a i64) where 'a: 'b { slot.value = value; } pub fn main() -> i64 { let first = 40; let second = 42; let mut slot = Slot { value: &first }; set(&mut slot, &second); *slot.value }");
}

#[test]
fn helper_reference_stores_retain_longer_input_loans() {
    rejects("struct Slot<'a> { value: &'a i64 } fn set<'a,'b>(slot: &mut Slot<'b>, value: &'a i64) where 'a: 'b { slot.value = value; } pub fn main() -> i64 { let first = 40; let mut second = 42; let mut slot = Slot { value: &first }; set(&mut slot, &second); second = 43; *slot.value }", &["G5007"]);
}

#[test]
fn generic_borrowed_variant_payloads_keep_their_external_storage() {
    accepts("enum Outcome<T,E> { Ok(T), Err(E) } fn copied<'a,T,E>(value: Outcome<&'a T,E>) -> Outcome<T,E> where T: Use<[0,*]> { handle value { Outcome::Ok(item) => Outcome::Ok(*item), Outcome::Err(error) => Outcome::Err(error) } } pub fn main() -> i64 { let backing = 42; let value: Outcome<&i64,()> = Outcome::Ok(&backing); handle copied(value) { Outcome::Ok(item) => item, Outcome::Err(_) => 0 } }");
}

#[test]
fn imported_generic_reference_carriers_preserve_input_regions() {
    accepts_with_dependency("use views::{Window, get, relay}; pub fn main() -> i64 { let backing = 42; let mut carrier = Window { storage: &backing }; let result = get(relay(&mut carrier)); *result }",
        Some("pub struct Window<'a,T> { pub storage: &'a T } pub fn get<'a,T>(value: &Window<'a,T>) -> &'a T { value.storage } pub fn relay<'a,T>(value: &'a mut T) -> &'a mut T { value }"));
}

#[test]
fn static_and_caller_views_join_at_the_checked_result_region() {
    let source = "use std::*; fn select<'a>(bytes: Slice<'a,u8>, empty: Bool) -> Slice<'a,u8> { handle empty { true => b\"\", false => bytes } } pub fn main() -> i64 { as<i64>(Slice::len(&select(b\"x\", true))) + as<i64>(*Slice::get_unchecked(select(b\"*\", false), 0)) }";
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(source, optimization)).unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: this fixture calls the trusted bundled Slice primitives on
        // valid static storage, with an in-bounds element index.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
}

#[test]
fn evaluated_static_views_keep_their_declared_reference_contract() {
    let source = "use std::*; pub let literal = { let view: Slice<'static,u8> = b\"*\"; view }; pub fn main() -> i64 { as<i64>(*Slice::get_unchecked(literal, 0)) }";
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(source, optimization)).unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: the checked source indexes its trusted, one-byte static view.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
}

const STATIC_VIEW_REPLACEMENT: &str = r#"use std::*;
        enum Maybe<T> { Some(T), None(()) }
        struct State { previous: Maybe<Slice<'static,u8>> }
        fn set(state: &mut State) { let view: Slice<'static,u8> = b"*"; state.previous = Maybe::Some(view); }
        fn select(state: State) -> Slice<'static,u8> {
            handle state.previous { Maybe::Some(value) => value, Maybe::None(_) => b"!" }
        }
        pub fn main() -> i64 { let mut state = State { previous: Maybe::None(()) }; set(&mut state); as<i64>(*Slice::get_unchecked(select(state), 0)) }
    "#;

#[test]
fn helper_created_static_views_replace_an_empty_payload() {
    // Replacement payloads include references created by the helper, not
    // merely loans forwarded from its incoming values.
    let source = STATIC_VIEW_REPLACEMENT;
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(source, optimization)).unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: the helper stores a one-byte static view and the source
        // indexes only its first byte through the trusted Slice primitive.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
}

fn generic_reference_replacement_source(action: &str) -> String {
    let prefix = r#"use std::*;
        enum Maybe<T> { Some(T), None(()) }
        struct State<'a> { previous: Maybe<Slice<'a,u8>> }
        fn set<'a>(state: &mut State<'a>) { let view: Slice<'static,u8> = b"*"; state.previous = Maybe::Some(view); }
        fn select<'a>(state: State<'a>) -> Slice<'a,u8> {
            handle state.previous { Maybe::Some(value) => value, Maybe::None(_) => b"!" }
        }
    "#;
    format!("{prefix} pub fn main() -> i64 {{ let mut state: State<'_> = State {{ previous: Maybe::None(()) }}; {action} as<i64>(*Slice::get_unchecked(select(state), 0)) }}")
}

fn check_generic_reference_replacement(action: &str) {
    let source = generic_reference_replacement_source(action);
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(&source, optimization))
            .unwrap_or_else(|error| panic!("{action}: {error:?}")).artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: each helper writes a one-byte static view; its first
        // byte is read through the trusted, in-bounds Slice primitive.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
}

#[test]
fn helper_created_references_compose_with_generic_regions() {
    check_generic_reference_replacement("set(&mut state);");
}

#[test]
fn helper_created_references_compose_with_captured_targets() {
    // Active acceptance regression: the captured-input resource handoff and
    // region identities must agree with the invocation's storage relation.
    check_generic_reference_replacement("let target = &mut state; let update = move (target) { set(target); }; update();");
}

#[test]
fn inferred_body_region_bounds_survive_freezing_and_specialization() {
    accepts("struct Token<'a> { value: i64 } fn pair<'a,'b>() -> (Token<'a>,Token<'b>) where 'a: 'b { (Token { value: 40 }, Token { value: 2 }) } pub fn main() -> i64 { let pair = pair(); pair.0.value + pair.1.value }");
    accepts("struct Token<'a> { value: i64 } fn static_token<'a>() -> Token<'a> where 'a: 'static { Token { value: 42 } } pub fn main() -> i64 { static_token().value }");
    accepts("fn add<'a>(left: &'a i64, right: &'a i64) -> i64 { *left + *right } pub fn main() -> i64 { let left = 40; let right = 2; add(&left, &right) }");
    rejects("fn require_static(value: &'static i64) -> i64 { *value } pub fn main() -> i64 { let local = 42; require_static(&local) }", &["G5017"]);
}

#[test]
fn inferred_shared_call_regions_can_shorten_an_incoming_loan_to_local_storage() {
    accepts("fn add<'a>(left: &'a i64, right: &'a i64) -> i64 { *left + *right } fn inner<'a>(incoming: &'a i64) -> i64 { let local = 2; add(incoming, &local) } pub fn main() -> i64 { let value = 40; inner(&value) }");
}

#[test]
fn nominal_callback_and_mutable_field_variance_cannot_extend_local_borrows() {
    rejects("struct Consumer<'a> { call: (&'a i64) -> i64 } fn static_read(value: &'static i64) -> i64 { *value } fn invoke<'a>(consumer: Consumer<'a>, value: &'a i64) -> i64 { (consumer.call)(value) } pub fn main() -> i64 { let local = 42; let consumer: Consumer<'static> = Consumer { call: static_read }; invoke(consumer, &local) }", &["G5017"]);
    rejects("struct Slot<'a,'b> { value: &'a mut &'b i64 } fn require_same<'a,'b>(left: Slot<'a,'b>, right: Slot<'a,'b>) { } fn invalid<'a,'b,'c>(left: &'a mut &'b i64, right: &'a mut &'c i64) { require_same(Slot { value: left }, Slot { value: right }); } pub fn main() -> i64 { 42 }", &["G5017"]);
}

#[test]
fn captured_inferred_region_stores_retain_real_incoming_loans() {
    let program = |after: &str| format!(r#"
        enum Maybe<T> {{ Some(T), None(()) }}
        struct Slot<'a> {{ value: Maybe<&'a i64> }}
        fn set<'a,'b>(slot: &mut Slot<'b>, value: &'a i64) where 'a: 'b {{ slot.value = Maybe::Some(value); }}
        fn get<'a>(slot: Slot<'a>) -> i64 {{ handle slot.value {{ Maybe::Some(value) => *value, Maybe::None(_) => 0 }} }}
        pub fn main() -> i64 {{
            let mut backing = 42;
            let mut slot: Slot<'_> = Slot {{ value: Maybe::None(()) }};
            let target = &mut slot;
            let incoming = &backing;
            let update = move (target, incoming) {{ set(target, incoming); }};
            update();
            {after}
            get(slot)
        }}
    "#);
    accepts(&program(""));
    rejects(&program("backing = 43;"), &["G5007", "G5008"]);
}

#[test]
fn helper_created_static_reference_payloads_execute_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(STATIC_VIEW_REPLACEMENT, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("source O{optimization}: {error:#?}"));
        // SAFETY: compile and execute only this locally checked source and
        // its trusted static-memory/Slice operations.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }.unwrap().0, 42);
    }
}

#[test]
fn captured_inferred_region_replacements_execute_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let source = generic_reference_replacement_source("let target = &mut state; let update = move (target) { set(target); }; update();");
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(&source, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("source O{optimization}: {error:#?}"));
        // SAFETY: the same checked captured-target regression stores a
        // one-byte static Slice and reads its in-bounds first element.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }.unwrap().0, 42);
    }
}
