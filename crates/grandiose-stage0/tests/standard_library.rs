use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler,
};

trait RunBundledStandardLibrary {
    fn run_std_i64(&self) -> Result<i64, grandiose_stage0::VmArtifactError>;
    fn run_std_usize(&self) -> Result<u64, grandiose_stage0::VmArtifactError>;
    fn run_std_u8(&self) -> Result<u8, grandiose_stage0::VmArtifactError>;
    fn run_std_u32(&self) -> Result<u32, grandiose_stage0::VmArtifactError>;
}
impl RunBundledStandardLibrary for grandiose_stage0::VerifiedVmProgram {
    fn run_std_i64(&self) -> Result<i64, grandiose_stage0::VmArtifactError> {
        // SAFETY: these fixtures execute freshly compiled source and the
        // trusted bundled stdlib, never a supplied unsafe artifact. Negative
        // source fixtures fail compilation and do not reach this runner.
        unsafe { self.run_i64_with_unsafe(grandiose_stage0::VmExecutionLimits::default()) }
    }
    fn run_std_usize(&self) -> Result<u64, grandiose_stage0::VmArtifactError> {
        // SAFETY: same locally compiled source contract as run_std_i64.
        let text = unsafe { self.run_display_with_unsafe(Default::default(), None) }?;
        Ok(text.parse().expect("usize fixture must return a decimal integer"))
    }
    fn run_std_u8(&self) -> Result<u8, grandiose_stage0::VmArtifactError> {
        Ok(self.run_std_usize()?.try_into().expect("u8 fixture must fit u8"))
    }
    fn run_std_u32(&self) -> Result<u32, grandiose_stage0::VmArtifactError> {
        Ok(self.run_std_usize()?.try_into().expect("u32 fixture must fit u32"))
    }
}

fn request(application: &str) -> CompilationRequest {
    let app = PackageKey("app@0.1.0".into());
    let standard = PackageKey("std@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"standard-library-test")),
        mode: CompilationMode::Build,
        root_package: app.clone(),
        sources: vec![
            SourceInput::new(
                app,
                LogicalPath::parse("src/main.glorious").unwrap(),
                application.as_bytes(),
            ),
            SourceInput::new(
                standard,
                LogicalPath::parse("src/lib.glorious").unwrap(),
                include_bytes!("../../../stdlib/src/lib.glorious").as_slice(),
            ),
        ],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

#[test]
fn native_static_addresses_keep_exact_literal_bytes_after_the_leaf_returns() {
    let mut input = request("use std::*; pub fn main() -> i64 { native_static_address_fixture() }");
    let compiler = StageZeroCompiler::new();
    let revision = compiler.import_revision(input.clone(), None).unwrap();
    // Augmented std intentionally does not receive automatic trusted bindings.
    // This test explicitly carries forward the unmodified distribution's exact
    // manifest; the added fixture itself receives no extra authority.
    input.runtime_manifest = compiler.open_session(revision).unwrap()
        .snapshot().world().runtime_manifest.clone();
    let source = format!(r#"{}
        fn native_literal_reference() -> &'static u8 {{
            unsafe {{ __g1_memory_borrow_shared(__g1_memory_static_utf8_address("*")) }}
        }}
        pub fn native_static_address_fixture() -> i64 {{
            let reference = native_literal_reference();
            unsafe {{
                let raw = __g1_memory_static_bytes_address(b"\x00\xff");
                let last = __g1_memory_read(__g1_memory_offset_const(raw, 1));
                handle last == 255 {{ true => as<i64>(*reference), false => 0 }}
            }}
        }}
    "#, include_str!("../../../stdlib/src/lib.glorious"));
    input.sources[1] = SourceInput::new(PackageKey("std@0.1.0".into()), LogicalPath::parse("src/lib.glorious").unwrap(), source.as_bytes());
    let program = compiler.compile(input).unwrap().artifact.unwrap();
    // SAFETY: the source fixture reads in-range immutable literal bytes only;
    // native-address roots retain them for the entire execution domain.
    assert_eq!(unsafe { program.run_i64_with_unsafe(grandiose_stage0::VmExecutionLimits::default()) }.unwrap(), 42);
}

#[test]
fn source_clones_create_independent_nested_collection_owners() {
    let source = r#"
        use std::*;
        fn extend_first(values: &mut Vec<String>) -> () {
            handle Vec::get_mut(values, 0) {
                Result::Err(_) => (),
                Result::Ok(value) => String::push_str(value, "b"),
            }
        }
        pub fn main() -> i64 {
            let original = Vec<String>::new();
            Vec::push(&mut original, Str::to_string("a"));
            let copied = Clone::clone(&original);
            extend_first(&mut original);
            Vec::push(&mut copied, Str::to_string("c"));
            let expected_copy = Str::to_string("a");
            let expected_original = Str::to_string("ab");
            handle Eq::eq(Vec::get_unchecked(&copied, 0), &expected_copy) {
                false => 0,
                true => handle Eq::eq(Vec::get_unchecked(&original, 0), &expected_original) {
                    false => 0,
                    true => handle Vec::len(&original) == 1 {
                        false => 0,
                        true => handle Vec::len(&copied) == 2 { false => 0, true => 42 },
                    },
                },
            }
        }
    "#;
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(artifact.run_std_i64().unwrap(), 42);
}

#[test]
fn byte_cursor_fixed_width_reads_preserve_unaligned_windows_and_failed_positions() {
    let bytes: Vec<u8> = (0..16).map(|index| 0xf0 + index).collect();
    let literal: String = bytes.iter().map(|byte| format!("\\x{byte:02x}")).collect();
    let mut checks = String::new();
    for offset in 0..8 {
        for width in 0..=8 {
            let expected = if width == 8 {
                u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
            } else {
                0
            };
            for input in ["literal", "Vec::as_slice(&owned)"] {
                checks.push_str(&format!(
                    "score = score + check({input}, {offset}, {width}, {expected});\n"
                ));
            }
        }
    }
    let source = format!(
        r#"
        use std::*;
        fn advance(cursor: &mut ByteCursor, bytes: Slice<u8>, count: usize) -> () {{
            handle count == 0 {{
                true => (),
                false => {{ ByteCursor::u8(&mut *cursor, bytes); advance(cursor, bytes, count - 1) }},
            }}
        }}
        fn read(cursor: &mut ByteCursor, bytes: Slice<u8>, offset: usize, width: usize, expected: u64) -> i64 {{
            advance(&mut *cursor, bytes, offset);
            handle ByteCursor::u64(&mut *cursor, bytes) {{
                Result::Ok(value) => handle width == 8 {{
                    false => 0,
                    true => handle value == expected {{
                        false => 0, true => handle ByteCursor::position(& *cursor) == offset + 8 {{ true => 1, false => 0 }},
                    }},
                }},
                Result::Err(ByteError::Truncated) => handle width < 8 {{
                    false => 0, true => handle ByteCursor::position(& *cursor) == offset {{ true => 1, false => 0 }},
                }},
                _ => 0,
            }}
        }}
        fn check(bytes: Slice<u8>, offset: usize, width: usize, expected: u64) -> i64 {{
            handle Slice::slice(bytes, Range<usize> {{ start: 0, end: offset + width }}) {{
                Result::Err(_) => 0,
                Result::Ok(window) => {{ let cursor = ByteCursor::new(); read(&mut cursor, window, offset, width, expected) }},
            }}
        }}
        fn sample() -> Slice<'static, u8> {{ b"{literal}" }}
        pub fn main() -> i64 {{
            let literal = sample();
            let owned = Vec<u8>::new(); Vec::extend_from_slice(&mut owned, literal);
            let score = as<i64>(0);
            {checks}
            score
        }}
    "#
    );
    let program = StageZeroCompiler::new()
        .compile(request(&source))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(program.run_std_i64().unwrap(), 144);
}

#[test]
fn source_result_clones_cover_owned_and_unrestricted_payloads() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let scalar = Result<i64, ()>::Ok(42);
            let scalar_copy = Clone::clone(&scalar);
            let owned = Result<String, String>::Err(Str::to_string("failure"));
            let owned_copy = Clone::clone(&owned);
            handle owned_copy {
                Result::Ok(_) => 0,
                Result::Err(message) => handle String::len(&message) == 7 {
                    false => 0,
                    true => handle scalar_copy { Result::Ok(value) => value, Result::Err(_) => 0 },
                },
            }
        }
    "#;
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(artifact.run_std_i64().unwrap(), 42);
}

#[test]
fn standard_prelude_and_source_defined_control_are_importable() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            r#"
                use std::*;
                pub fn main() -> i64 {
                    if(Result<(), ()>::Ok(())) { 42 } else { 0 }
                }
            "#,
        ))
        .expect("the distributed standard prelude must compile");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn standard_lifetime_generic_trait_method_preserves_nested_map_call_instances() {
    let source = r#"
        use std::*;
        pub struct World { private values: HashMap<u64, usize> }
        pub trait Lookup { get<'a>(value: &'a Self, key: u64) -> Option<&'a usize>; }
        fn lookup<'a>(value: &'a World, key: u64) -> Option<&'a usize> { HashMap::get(&value.values, &key) }
        pub impl Lookup for World {
            get<'a>(value: &'a World, key: u64) -> Option<&'a usize> { lookup(value, key) }
        }
        fn main() -> i64 {
            let map = HashMap<u64, usize>::new();
            HashMap::insert(&mut map, as<u64>(10), as<usize>(32));
            let world = World { values: map };
            handle Lookup::get(&world, 10) { Result::Err(_) => 0, Result::Ok(value) => as<i64>(*value) }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let decoded = grandiose_stage0::decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    assert_eq!(decoded.run_std_i64().unwrap(), 32);
}

#[test]
fn standard_lifetime_generic_trait_method_does_not_extend_a_local_map_owner() {
    let source = r#"
        use std::*;
        pub struct World { private values: HashMap<u64, usize> }
        pub trait Lookup { get<'a>(value: &'a Self, key: u64) -> Option<&'a usize>; }
        fn lookup<'a>(value: &'a World, key: u64) -> Option<&'a usize> { HashMap::get(&value.values, &key) }
        pub impl Lookup for World {
            get<'a>(value: &'a World, key: u64) -> Option<&'a usize> { lookup(value, key) }
        }
        fn escape() -> Option<&'static usize> {
            let map = HashMap<u64, usize>::new();
            HashMap::insert(&mut map, as<u64>(10), as<usize>(32));
            let world = World { values: map }; Lookup::get(&world, 10)
        }
        fn main() -> i64 { handle escape() { Result::Err(_) => 0, Result::Ok(value) => as<i64>(*value) } }
    "#;
    let error = StageZeroCompiler::new().compile(request(source)).unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5017"), "{error:#?}");
}

#[test]
fn standard_string_traits_use_exact_bytes_and_resolve_hash_collisions() {
    fn literal(value: &str) -> String {
        format!("b\"{}\"", value.bytes().map(|byte| format!("\\x{byte:02x}")).collect::<String>())
    }
    fn fingerprint(value: &str) -> usize {
        value.bytes().fold(5381_usize.wrapping_mul(33).wrapping_add(value.len()),
            |state, byte| state.wrapping_mul(33).wrapping_add(byte as usize))
    }
    let long = "a".repeat(100);
    let pairs = [
        ("", ""), ("", "a"), ("a", ""), ("a", "a"), ("a", "b"), ("a", "aa"),
        ("ab", "a"), ("é", "z"), ("é", "e\u{301}"), ("a\0b", "a\0c"),
        ("😀", "🦀"), ("Ab", "BA"), (long.as_str(), long.as_str()),
    ];
    let cases = pairs.iter().map(|(left, right)| {
        let order = match left.cmp(right) { std::cmp::Ordering::Less => -1, std::cmp::Ordering::Equal => 0, std::cmp::Ordering::Greater => 1 };
        format!("score = score + pair({}, {}, {order}, {}, {});\n", literal(left), literal(right), fingerprint(left), fingerprint(right))
    }).collect::<String>();
    let application = format!(r#"
        use std::*;
        fn equal(a: i64, b: i64) -> i64 {{ handle a == b {{ true => 1, false => 0 }} }}
        fn text(bytes: Slice<u8>) -> String {{ let owned = Vec<u8>::new(); Vec::extend_from_slice(&mut owned, bytes);
            handle String::from_utf8(owned) {{ Result::Ok(value) => value, Result::Err(_) => String::new() }} }}
        fn hash(value: &String) -> usize {{ let state = Hasher::new(); Hash::hash(value, &mut state); Hasher::finish(state) }}
        fn order(value: Ordering) -> i64 {{ handle value {{ Ordering::Less => -1, Ordering::Equal => 0, Ordering::Greater => 1 }} }}
        fn is_equal(value: Bool) -> i64 {{ handle value {{ true => 1, false => 0 }} }}
        fn pair(a: Slice<u8>, b: Slice<u8>, expected: i64, a_hash: usize, b_hash: usize) -> i64 {{
            let left = text(a); let right = text(b);
            equal(order(Ord::compare(&left, &right)), expected)
                * equal(is_equal(Eq::eq(&left, &right)), is_equal(expected == 0))
                * equal(as<i64>(hash(&left)), as<i64>(a_hash)) * equal(as<i64>(hash(&right)), as<i64>(b_hash))
        }}
        fn lookup(map: &HashMap<String, usize>, key: Str, expected: usize) -> i64 {{
            let key = Str::to_string(key);
            handle HashMap::get(map, &key) {{ Result::Err(_) => 0, Result::Ok(value) => equal(as<i64>(*value), as<i64>(expected)) }}
        }}
        fn maps() -> i64 {{
            let a = Str::to_string("Ab"); let b = Str::to_string("BA");
            let score = equal(as<i64>(hash(&a)), as<i64>(hash(&b))) * equal(is_equal(Eq::eq(&a, &b)), 0);
            let map = HashMap<String, usize>::new();
            HashMap::insert(&mut map, a, as<usize>(11)); HashMap::insert(&mut map, b, as<usize>(22));
            score = score + lookup(&map, "Ab", 11) + lookup(&map, "BA", 22);
            let previous = HashMap::insert(&mut map, Str::to_string("Ab"), as<usize>(33));
            score + old(previous) + lookup(&map, "Ab", 33) + equal(as<i64>(HashMap::len(&map)), 2)
        }}
        fn old(value: Option<usize>) -> i64 {{ handle value {{ Result::Ok(value) => equal(as<i64>(value), 11), _ => 0 }} }}
        main() -> i64 {{ let score = as<i64>(0); {cases} score + maps() }}
    "#);
    let outcome = StageZeroCompiler::new().compile(request(&application)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    let verified = grandiose_stage0::decode_and_verify_program(&bytes).unwrap();
    assert_eq!(verified.run_std_i64().unwrap(), pairs.len() as i64 + 6);
}

#[test]
fn standard_slice_of_owned_strings_preserves_nested_view_provenance() {
    let source = r#"
        use std::*;
        struct Capability { private value: String }
        fn view<'a>(value: &'a Capability) -> Str<'a> { String::as_str(&value.value) }
        fn score(left: Str, right: Str) -> i64 {
            handle Slice::lex_compare(Str::as_bytes(left), Str::as_bytes(right)) { Ordering::Equal => 1, _ => 0 }
        }
        fn rows(values: Slice<Capability>, expected: &Vec<String>, cursor: usize, total: i64) -> i64 {
            handle cursor == Slice::len(&values) {
                true => total,
                false => {
                    let item = Slice::get_unchecked(values, cursor);
                    let actual = view(item);
                    let wanted = String::as_str(Vec::get_unchecked(expected, cursor));
                    rows(values, expected, cursor + 1, total + score(actual, wanted))
                },
            }
        }
        main() -> i64 {
            let values = Vec<Capability>::new(); let expected = Vec<String>::new();
            Vec::push(&mut values, Capability { value: Str::to_string("a") });
            Vec::push(&mut values, Capability { value: Str::to_string("é") });
            Vec::push(&mut expected, Str::to_string("a")); Vec::push(&mut expected, Str::to_string("é"));
            rows(Vec::as_slice(&values), &expected, 0, 0)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let program = grandiose_stage0::decode_and_verify_program(&outcome.artifact.unwrap().canonical_bytes()).unwrap();
    assert_eq!(program.run_std_i64().unwrap(), 2);
}

#[test]
fn slice_element_accessors_preserve_the_explicit_input_lifetime() {
    let source = r#"
        use std::*;
        fn first<'a>(values: Slice<'a, i64>) -> Option<&'a i64> { Slice::get(values, 0) }
        fn direct<'a>(values: Slice<'a, i64>) -> &'a i64 { Slice::get_unchecked(values, 0) }
        main() -> i64 {
            let values = Vec<i64>::new(); Vec::push(&mut values, 7);
            let result = first(Vec::as_slice(&values));
            handle result { Result::Err(_) => 0, Result::Ok(value) => *value + *direct(Vec::as_slice(&values)) }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let program = grandiose_stage0::decode_and_verify_program(&outcome.artifact.unwrap().canonical_bytes()).unwrap();
    assert_eq!(program.run_std_i64().unwrap(), 14);
}

#[test]
fn hash_map_resident_views_borrow_move_only_values_without_exposing_mutable_keys() {
    let source = r#"
        use std::*;
        struct Payload { number: i64 }
        pub impl Use<[0, 1]> for Payload {}
        fn total(rows: Slice<HashMapEntry<String, Payload>>, cursor: usize, value: i64) -> i64 {
            handle cursor == Slice::len(&rows) {
                true => value,
                false => {
                    let entry = Slice::get_unchecked(rows, cursor);
                    let key = HashMapEntry::key(entry); let payload = HashMapEntry::value(entry);
                    total(rows, cursor + 1, value + payload.number + as<i64>(String::len(key)))
                },
            }
        }
        main() -> i64 {
            let values = HashMap<String, Payload>::new();
            HashMap::insert(&mut values, Str::to_string("Ab"), Payload { number: 11 });
            HashMap::insert(&mut values, Str::to_string("BA"), Payload { number: 22 });
            let first = total(HashMap::entries(&values), 0, 0);
            HashMap::insert(&mut values, Str::to_string("Ab"), Payload { number: 33 });
            let second = total(HashMap::entries(&values), 0, 0);
            let key = Str::to_string("BA"); HashMap::remove(&mut values, &key);
            HashMap::insert(&mut values, Str::to_string("c"), Payload { number: 44 });
            first + second + total(HashMap::entries(&values), 0, 0)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let program = grandiose_stage0::decode_and_verify_program(&outcome.artifact.unwrap().canonical_bytes()).unwrap();
    assert_eq!(program.run_std_i64().unwrap(), 37 + 59 + 80);
}

#[test]
fn hash_map_resident_views_do_not_escape_the_map_owner() {
    let source = r#"
        use std::*;
        fn escape<'a>() -> &'a String {
            let values = HashMap<String, String>::new();
            HashMap::insert(&mut values, Str::to_string("a"), Str::to_string("b"));
            let entries = HashMap::entries(&values);
            let entry = Slice::get_unchecked(entries, 0);
            HashMapEntry::key(entry)
        }
        main() -> i64 { let result = escape(); as<i64>(String::len(result)) }
    "#;
    let error = StageZeroCompiler::new().compile(request(source)).unwrap_err();
    assert!(error.diagnostics().iter().any(|error| matches!(error.code, "G4107" | "G5017" | "G5018")), "{error:#?}");
}

#[test]
fn standard_usize_display_preserves_unsigned_decimal_boundaries() {
    let values = [
        0usize, 1, 9, 10, 99, 100, 999, 1000,
        u32::MAX as usize, u32::MAX as usize + 1,
        i64::MAX as usize, i64::MAX as usize + 1,
        usize::MAX - 1, usize::MAX,
    ];
    let groups = values
        .chunks(4)
        .enumerate()
        .map(|(index, values)| {
            let cases = values
                .iter()
                .map(|value| format!("check({value}, \"{value}\")"))
                .collect::<Vec<_>>()
                .join(" + ");
            format!("fn group{index}() -> i64 {{ {cases} }}")
        })
        .collect::<Vec<_>>()
        .join("\n");
    let source = format!(
        r#"
        use std::*;
        fn check(value: usize, expected: Str) -> i64 {{
            let rendered = format(&value);
            handle Slice::lex_compare(Str::as_bytes(String::as_str(&rendered)), Str::as_bytes(expected)) {{
                Ordering::Equal => 1, _ => 0,
            }}
        }}
        {groups}
        pub fn main() -> i64 {{ group0() + group1() + group2() + group3() }}
    "#
    );
    let outcome = StageZeroCompiler::new()
        .compile(request(&source))
        .expect("source decimal formatting must compile without a native formatting leaf");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    let program = grandiose_stage0::decode_and_verify_program(&bytes).unwrap();
    assert_eq!(program.run_std_i64().unwrap(), values.len() as i64);
}

#[test]
fn standard_take_uses_a_receiverless_default_constructor() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            r#"
                use std::*;
                pub fn main() -> i64 {
                    let value = 7;
                    let previous = take(&mut value);
                    previous + value
                }
            "#,
        ))
        .expect("generic take must select Default::default from its result context");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 7);
}

#[test]
fn default_and_take_cover_empty_standard_library_collections() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let values = Vec<i64>::new();
            Vec::push(&mut values, 7);
            let previous = take(&mut values);
            Vec::len(&previous) + Vec::len(&values)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn default_covers_optional_and_compiler_collection_types() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let value = default_value<Option<i64>>();
            let map = default_value<HashMap<i64, i64>>();
            let queue = default_value<VecDeque<i64>>();
            handle Option::is_none(value) {
                false => 0,
                true => handle HashMap::is_empty(&map) {
                    false => 0,
                    true => handle VecDeque::is_empty(&queue) { true => 42, false => 0 },
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn option_get_or_insert_default_constructs_only_a_vacant_resident() {
    let source = r#"
        use std::*;
        pub fn empty_i64() -> Option<i64> { None }
        pub fn main() -> i64 {
            let value = empty_i64();
            let inserted = Option::get_or_insert_default(&mut value);
            *inserted = 42;
            handle value {
                Result::Ok(item) => item,
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_resize_copies_only_duplicable_fill_values() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec<i64>::new();
            Vec::resize(&mut values, 3, 7);
            Vec::resize(&mut values, 1, 0);
            handle Vec::pop(&mut values) {
                Result::Ok(value) => value,
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 7);
}

#[test]
fn bundled_stable_sort_keeps_equal_values_in_source_order() {
    let source = r#"
        use std::*;
        pub struct Entry { key: i64, tag: i64 }
        pub impl Ord for Entry {
            compare(left: &Entry, right: &Entry) -> Ordering {
                handle left.key < right.key {
                    true => Ordering::Less,
                    false => handle left.key == right.key {
                        true => Ordering::Equal,
                        false => Ordering::Greater,
                    },
                }
            }
        }
        pub fn main() -> i64 {
            let values = Vec<Entry>::new();
            Vec::push(&mut values, Entry { key: 2, tag: 10 });
            Vec::push(&mut values, Entry { key: 1, tag: 20 });
            Vec::push(&mut values, Entry { key: 2, tag: 30 });
            Vec::sort_stable(&mut values);
            (*Vec::get_unchecked(&values, 0)).tag * 100
                + (*Vec::get_unchecked(&values, 1)).tag * 10
                + (*Vec::get_unchecked(&values, 2)).tag
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 2130);
}

#[test]
fn capture_free_named_predicates_are_duplicable_callbacks() {
    let source = r#"
        use std::*;
        pub fn below_two(value: &i64) -> Bool { *value < 2 }
        pub fn twice<F>(predicate: F, first: &i64, second: &i64) -> i64
            where F: Fn<(&i64), Output = Bool>, F: Use<[0, *]> {
            handle predicate(first) {
                false => 0,
                true => handle predicate(second) { true => 42, false => 0 },
            }
        }
        pub fn main() -> i64 {
            let first = 0;
            let second = 1;
            twice(below_two, &first, &second)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_partition_by_uses_a_reusable_source_predicate() {
    let source = r#"
        use std::*;
        pub fn below_two(value: &i64) -> Bool { *value < 2 }
        pub fn main() -> i64 {
            let values = Vec<i64>::new();
            Vec::push(&mut values, 3);
            Vec::push(&mut values, 1);
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 0);
            let boundary = Vec::partition_by(&mut values, below_two);
            handle boundary == 2 {
                false => 0,
                true => handle *Vec::get_unchecked(&values, 0) < 2 {
                    false => 0,
                    true => handle *Vec::get_unchecked(&values, 1) < 2 {
                        false => 0,
                        true => handle *Vec::get_unchecked(&values, 2) >= 2 {
                            false => 0,
                            true => handle *Vec::get_unchecked(&values, 3) >= 2 { true => 42, false => 0 },
                        },
                    },
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_partition_by_accepts_a_duplicable_capturing_closure() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let threshold = 2;
            let values = Vec<i64>::new();
            Vec::push(&mut values, 3);
            Vec::push(&mut values, 1);
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 0);
            Vec::partition_by(&mut values, (value: &i64) -> Bool { *value < threshold })
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 2);
}

#[test]
fn scalar_eq_and_ord_are_standard_library_trait_implementations() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let left = 20;
            let right = 22;
            handle Eq::eq(&left, &left) {
                true => handle Ord::compare(&left, &right) {
                    Ordering::Less => 42,
                    _ => 0,
                },
                false => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn scalar_ord_supports_byte_and_character_slice_algorithms() {
    let source = r#"
        use std::*;
        pub fn compare_bytes(left: u8, right: u8) -> i64 {
            handle Ord::compare(&left, &right) {
                Ordering::Less => 1,
                Ordering::Equal => 2,
                Ordering::Greater => 3,
            }
        }
        pub fn compare_chars(left: char, right: char) -> i64 {
            handle Ord::compare(&left, &right) {
                Ordering::Less => 10,
                Ordering::Equal => 20,
                Ordering::Greater => 30,
            }
        }
        pub fn main() -> i64 { compare_bytes(1, 2) + compare_chars('a', 'b') }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 11);
}

#[test]
fn bundled_vec_sort_unstable_accepts_standard_byte_ordering() {
    let source = r#"
        use std::*;
        pub fn sort_bytes(three: u8, one: u8, two: u8) -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, three);
            Vec::push(&mut values, one);
            Vec::push(&mut values, two);
            Vec::sort_unstable(&mut values);
            handle *Vec::get_unchecked(&values, 0) == one {
                true => 42,
                false => 0,
            }
        }
        pub fn main() -> i64 { sort_bytes(3, 1, 2) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_char_api_validates_unicode_scalars_and_reports_utf8_width() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            handle char_from_u32(65) {
                Result::Ok(value) => handle char_to_u32(value) == 65 {
                    true => handle char_utf8_len('🦀') == 4 { true => 42, false => 0 },
                    false => 0,
                },
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_char_api_rejects_surrogates_and_out_of_range_values() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            handle char_from_u32(55296) {
                Result::Ok(_) => 0,
                Result::Err(_) => handle char_from_u32(1114112) {
                    Result::Ok(_) => 0,
                    Result::Err(_) => 42,
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_checked_and_wrapping_numeric_conversions_are_source_wrappers() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            handle i64_to_u32_checked(42) {
                Result::Ok(checked) => handle checked == 42 {
                    true => handle i64_to_u32_checked(-1) {
                        Result::Ok(_) => 0,
                        Result::Err(_) => handle i64_to_u32_wrapping(-1) > 0 {
                            true => 42,
                            false => 0,
                        },
                    },
                    false => 0,
                },
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_bitwise_and_shift_helpers_cover_multiple_integer_widths() {
    let source = r#"
        use std::*;
        pub fn byte_bits(left: u8, right: u8, count: u32) -> u8 {
            bit_or(bit_and(left, right), bit_shl(1, count))
        }
        pub fn wide_bits(value: i64, count: u32) -> i64 {
            bit_xor(bit_not(value), bit_shr(16, count))
        }
        pub fn main() -> i64 {
            let byte = byte_bits(12, 10, 1);
            let wide = wide_bits(0, 2);
            handle byte == 10 {
                true => handle wide == -5 { true => 42, false => 0 },
                false => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_trait_based_min_max_and_clamp_work_for_scalar_values() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let smallest = min(9, 3);
            let largest = max(9, 3);
            let middle = clamp(20, 2, 7);
            handle smallest == 3 {
                true => handle largest == 9 {
                    true => handle middle == 7 { true => 42, false => 0 },
                    false => 0,
                },
                false => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_ord_covers_integer_widths_using_generic_vm_comparisons() {
    let source = r#"
        use std::*;
        pub fn u16_less(left: u16, right: u16) -> i64 {
            handle Ord::compare(&left, &right) { Ordering::Less => 1, _ => 0 }
        }
        pub fn i32_greater(left: i32, right: i32) -> i64 {
            handle Ord::compare(&left, &right) { Ordering::Greater => 1, _ => 0 }
        }
        pub fn u128_equal(left: u128, right: u128) -> i64 {
            handle Ord::compare(&left, &right) { Ordering::Equal => 1, _ => 0 }
        }
        pub fn main() -> i64 {
            handle u16_less(2, 7) == 1 {
                true => handle i32_greater(7, 2) == 1 {
                    true => handle u128_equal(9, 9) == 1 { true => 42, false => 0 },
                    false => 0,
                },
                false => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_get_mut_checks_the_index_before_materializing_a_unique_borrow() {
    let source = r#"
        use std::*;
        pub fn missing_index_is_err() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 4);
            handle Vec::get_mut(&mut values, 1) {
                Result::Ok(_) => 0,
                Result::Err(_) => 1,
            }
        }
        pub fn present_index_yields_a_unique_borrow() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 4);
            handle Vec::get_mut(&mut values, 0) {
                Result::Ok(item) => { *item = 9; 1 },
                Result::Err(_) => 0,
            }
        }
        pub fn main() -> i64 {
            handle missing_index_is_err() == 1 {
                true => handle present_index_yields_a_unique_borrow() == 1 {
                    true => 42,
                    false => 0,
                },
                false => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_option_lazy_insertion_only_constructs_an_empty_slot() {
    let source = r#"
        use std::*;
        pub fn build() -> i64 { 7 }
        pub fn empty_value() -> Option<i64> { None }
        pub fn occupied() -> i64 {
            let value = Some(4);
            let stored = Option::get_or_insert_with(&mut value, build);
            *stored
        }
        pub fn empty() -> i64 {
            let value = empty_value();
            let stored = Option::get_or_insert_with(&mut value, build);
            *stored
        }
        pub fn main() -> i64 {
            handle occupied() == 4 {
                true => handle empty() == 7 { true => 42, false => 0 },
                false => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_hash_map_accepts_i64_keys_through_the_standard_hash_impl() {
    let source = r#"
        use std::*;
        pub fn lookup(key: i64) -> i64 {
            let values = HashMap::new();
            HashMap::insert(&mut values, key, 42);
            handle HashMap::get(&values, &key) {
                Result::Ok(value) => *value,
                Result::Err(_) => 0,
            }
        }
        pub fn main() -> i64 { lookup(-7) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_ranges_and_str_subslices_reject_invalid_offsets_without_wrapping() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let reversed = Range<usize> { start: 9, end: 3 };
            handle Range::len(&reversed) == 0 {
                true => handle Str::subslice("ok", 3, 1) {
                    Result::Ok(_) => 0,
                    Result::Err(StringRangeError::OutOfBounds) => 42,
                    Result::Err(_) => 0,
                },
                false => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_string_borrows_coerce_to_str_at_standard_library_calls() {
    let source = r#"
        use std::*;
        pub fn show(value: Str) -> usize { Str::len(value) }
        pub fn main() -> usize {
            let owned = Str::to_string("Grandiose");
            show(&owned)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 9);
}

#[test]
fn bundled_hash_map_accepts_byte_and_character_keys() {
    let source = r#"
        use std::*;
        pub fn byte_value(key: u8) -> i64 {
            let bytes = HashMap::new();
            HashMap::insert(&mut bytes, key, 10);
            handle HashMap::get(&bytes, &key) {
                Result::Ok(value) => *value,
                Result::Err(_) => 0,
            }
        }
        pub fn char_value(key: char) -> i64 {
            let chars = HashMap::new();
            HashMap::insert(&mut chars, key, 32);
            handle HashMap::get(&chars, &key) {
                Result::Ok(value) => *value,
                Result::Err(_) => 0,
            }
        }
        pub fn main() -> i64 { byte_value(7) + char_value('x') }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_checked_float_to_integer_conversion_returns_option() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            handle f64_to_i64_checked(42.75) {
                Result::Ok(value) => handle value == 42 {
                    true => handle f64_to_i64_checked(0.0 / 0.0) {
                        Result::Ok(_) => 0,
                        Result::Err(_) => handle f64_to_i64_checked(9223372036854775808.0) {
                            Result::Ok(_) => 0,
                            Result::Err(_) => 42,
                        },
                    },
                    false => 0,
                },
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_str_lifetime_elision_ties_one_input_to_its_output_and_rejects_ambiguity() {
    let accepted = r#"
        use std::*;
        pub fn trim(text: Str) -> Str { text }
        pub fn main() -> usize { Str::len(trim("ok")) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 2);

    let rejected = r#"
        use std::*;
        pub fn choose(left: Str, right: Str) -> Str { left }
        pub fn main() -> usize { 0 }
    "#;
    assert!(
        StageZeroCompiler::new().compile(request(rejected)).is_err(),
        "an elided result lifetime with two unrelated Str inputs must remain ambiguous"
    );
}

#[test]
fn hasher_is_source_defined_and_deterministic() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let state = Hasher::new();
            Hasher::write_usize(&mut state, 7);
            Hasher::finish(state)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 177580);
}

#[test]
fn hash_trait_dispatches_to_the_standard_library_scalar_implementation() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let state = Hasher::new();
            let values = Vec<i64>::new();
            Vec::push(&mut values, 7);
            let input = Vec::len(&values);
            Hash::hash(&input, &mut state);
            Hasher::finish(state)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 177574);
}

#[test]
fn explicit_output_lifetime_can_select_one_of_two_borrowed_inputs() {
    let source = r#"
        use std::*;
        pub struct Holder { value: i64 }
        pub fn select<'a>(holder: &'a Holder, ignored: &i64) -> &'a i64 { &(*holder).value }
        pub fn main() -> i64 {
            let holder = Holder { value: 42 };
            let ignored = 7;
            *select(&holder, &ignored)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn nested_map_vector_views_preserve_the_explicit_owner_lifetime() {
    let source = r#"
        use std::*;
        pub struct Row { values: Vec<i64> }
        pub struct Store { rows: HashMap<u32, Row> }
        pub fn item<'a>(store: &'a Store, key: u32) -> Option<&'a i64> {
            handle HashMap<u32, Row>::get<'a>(&store.rows, &key) {
                Result::Err(_) => None,
                Result::Ok(row) => Vec::get(&row.values, 0),
            }
        }
        pub fn view<'a>(store: &'a Store, key: u32) -> Option<Slice<'a, i64>> {
            handle HashMap<u32, Row>::get<'a>(&store.rows, &key) {
                Result::Err(_) => None,
                Result::Ok(row) => Result::Ok(Vec::as_slice(&row.values)),
            }
        }
        pub fn item_mut<'a>(store: &'a mut Store, key: u32) -> Option<&'a mut i64> {
            handle HashMap<u32, Row>::get_mut<'a>(&mut store.rows, &key) {
                Result::Err(_) => None,
                Result::Ok(row) => Vec::get_mut(&mut row.values, 0),
            }
        }
        pub fn view_mut<'a>(values: &'a mut Vec<i64>) -> SliceMut<'a, i64> {
            Vec::as_mut_slice(values)
        }
        pub fn initialize(values: &mut Vec<i64>) -> () {
            let window = view_mut(values);
            let value = SliceMut::get_unchecked(window, 0);
            *value = 20;
            ()
        }
        pub fn update(store: &mut Store) -> () {
            handle item_mut(&mut *store, 7) {
                Result::Err(_) => (), Result::Ok(value) => { *value = *value + 1; () },
            }
        }
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 19);
            initialize(&mut values);
            let store = Store { rows: HashMap::new() };
            HashMap::insert(&mut store.rows, 7, Row { values: values });
            update(&mut store);
            handle item(&store, 7) {
                Result::Err(_) => 1,
                Result::Ok(value) => handle view(&store, 7) {
                    Result::Err(_) => 2,
                    Result::Ok(values) => *value + *Slice::get_unchecked(values, 0),
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn named_vector_view_lifetimes_do_not_allow_local_owner_escape() {
    let source = r#"
        use std::*;
        pub fn escape<'a>() -> &'a i64 {
            let values = Vec::new();
            Vec::push(&mut values, 42);
            Vec::get_unchecked(&values, 0)
        }
        pub fn main() -> i64 { 42 }
    "#;
    let error = StageZeroCompiler::new().compile(request(source)).unwrap_err();
    assert!(
        error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5017"),
        "{error:?}"
    );
}

#[test]
fn nested_unique_field_reborrow_reaches_a_vec_push_call() {
    let source = r#"
        use std::*;
        pub struct Holder { entries: Vec<i64> }
        pub fn push(holder: &mut Holder, item: i64) -> () {
            Vec::push(&mut (*holder).entries, item)
        }
        pub fn main() -> usize {
            let holder = Holder { entries: Vec<i64>::new() };
            push(&mut holder, 42);
            Vec::len(&holder.entries)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn generic_nested_unique_field_reborrow_reaches_a_vec_push_call() {
    let source = r#"
        use std::*;
        pub struct Entry<K, V> { key: K, value: V }
        pub struct Holder<K, V> { entries: Vec<Entry<K, V>> }
        pub fn push<K, V>(holder: &mut Holder<K, V>, key: K, item: V) -> () {
            Vec::push(&mut (*holder).entries, Entry { key: key, value: item })
        }
        pub fn main() -> usize {
            let holder = Holder<usize, i64> { entries: Vec<Entry<usize, i64>>::new() };
            let values = Vec<i64>::new();
            Vec::push(&mut values, 7);
            let key = Vec::len(&values);
            push(&mut holder, key, 42);
            Vec::len(&holder.entries)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn generic_hash_dispatch_before_a_vec_push_runs() {
    let source = r#"
        use std::*;
        pub struct Entry<K, V> { key: K, value: V }
        pub struct Holder<K, V> { entries: Vec<Entry<K, V>> }
        pub fn push<K, V>(holder: &mut Holder<K, V>, key: K, item: V) -> () where K: Hash {
            let state = Hasher::new();
            Hash::hash(&key, &mut state);
            Vec::push(&mut (*holder).entries, Entry { key: key, value: item })
        }
        pub fn main() -> usize {
            let holder = Holder<usize, i64> { entries: Vec<Entry<usize, i64>>::new() };
            let values = Vec<i64>::new();
            Vec::push(&mut values, 7);
            let key = Vec::len(&values);
            push(&mut holder, key, 42);
            Vec::len(&holder.entries)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn generic_hash_map_style_recursive_lookup_runs_on_an_empty_vec() {
    let source = r#"
        use std::*;
        pub struct Entry<K, V> { key: K, value: V }
        pub struct Holder<K, V> { entries: Vec<Entry<K, V>> }
        pub fn find_from<K, V>(holder: &Holder<K, V>, key: &K, index: usize) -> Option<usize> where K: Eq {
            handle index < Vec::len(&(*holder).entries) {
                false => Result::Err(()),
                true => {
                    let entry = Vec::get_unchecked(&(*holder).entries, index);
                    handle Eq::eq(&(*entry).key, key) {
                        true => Result::Ok(index),
                        false => find_from(holder, key, index + 1),
                    }
                },
            }
        }
        pub fn find<K, V>(holder: &Holder<K, V>, key: &K) -> Option<usize> where K: Eq, K: Hash {
            let state = Hasher::new();
            Hash::hash(key, &mut state);
            find_from(holder, key, 0)
        }
        pub fn main() -> usize {
            let holder = Holder<usize, i64> { entries: Vec<Entry<usize, i64>>::new() };
            let values = Vec<i64>::new();
            Vec::push(&mut values, 7);
            let key = Vec::len(&values);
            handle find(&holder, &key) { Result::Err(_) => 42, Result::Ok(_) => 0 }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 42);
}

#[test]
fn generic_hash_map_style_lookup_then_push_runs() {
    let source = r#"
        use std::*;
        pub struct Entry<K, V> { key: K, value: V }
        pub struct Holder<K, V> { entries: Vec<Entry<K, V>> }
        pub fn find_from<K, V>(holder: &Holder<K, V>, key: &K, index: usize) -> Option<usize> where K: Eq {
            handle index < Vec::len(&(*holder).entries) {
                false => Result::Err(()),
                true => {
                    let entry = Vec::get_unchecked(&(*holder).entries, index);
                    handle Eq::eq(&(*entry).key, key) {
                        true => Result::Ok(index),
                        false => find_from(holder, key, index + 1),
                    }
                },
            }
        }
        pub fn insert<K, V>(holder: &mut Holder<K, V>, key: K, item: V) -> () where K: Eq, K: Hash {
            let state = Hasher::new();
            Hash::hash(&key, &mut state);
            handle find_from(& *holder, &key, 0) {
                Result::Err(_) => Vec::push(&mut (*holder).entries, Entry { key: key, value: item }),
                Result::Ok(_) => (),
            }
        }
        pub fn main() -> usize {
            let holder = Holder<usize, i64> { entries: Vec<Entry<usize, i64>>::new() };
            let values = Vec<i64>::new();
            Vec::push(&mut values, 7);
            let key = Vec::len(&values);
            insert(&mut holder, key, 42);
            Vec::len(&holder.entries)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn hash_map_insert_remove_and_contains_are_source_defined() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let map = HashMap<usize, i64>::new();
            let values = Vec<i64>::new();
            Vec::push(&mut values, 7);
            let key = Vec::len(&values);
            HashMap::insert(&mut map, key, 42);
            handle HashMap::contains_key(&map, &key) {
                false => 0,
                true => handle HashMap::remove(&mut map, &key) {
                    Result::Err(_) => 0,
                    Result::Ok(value) => handle value == 42 { true => HashMap::len(&map), false => 0 },
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 0);
}

#[test]
fn hash_map_get_borrows_from_the_map_not_the_lookup_key() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let map = HashMap<usize, i64>::new();
            let values = Vec<i64>::new();
            Vec::push(&mut values, 7);
            let key = Vec::len(&values);
            HashMap::insert(&mut map, key, 42);
            handle HashMap::get(&map, &key) {
                Result::Ok(value) => *value,
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn hash_set_is_a_source_defined_deterministic_collection() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let set = HashSet<usize>::new();
            let probe = HashSet::len(&set) + 7;
            let first = HashSet::insert(&mut set, 7);
            let duplicate = HashSet::insert(&mut set, 7);
            handle first {
                false => 0,
                true => handle duplicate {
                    true => 0,
                    false => handle HashSet::contains(&set, &probe) {
                        false => 0,
                        true => handle HashSet::remove(&mut set, &probe) {
                            Result::Err(_) => 0,
                            Result::Ok(value) => value + HashSet::len(&set),
                        },
                    },
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 7);
}

#[test]
fn hash_tables_preserve_affine_values_across_growth_collisions_and_relocation() {
    let template = r#"
        use std::*;
        pub struct Key { code: i64 }
        pub impl Use<[0, 1]> for Key {}
        pub impl Eq for Key {
            eq(left: &Key, right: &Key) -> Bool { left.code == right.code }
        }
        pub impl Hash for Key {
            hash(value: &Key, state: &mut Hasher) -> () { Hasher::write_usize(state, @HASH@); }
        }
        pub struct Payload { number: i64 }
        pub impl Use<[0, 1]> for Payload {}
        pub type Map = HashMap<Key, Payload>;

        fn fill(map: &mut Map, next: i64) -> () {
            handle next == 24 {
                true => (),
                false => {
                    HashMap::insert(&mut *map, Key { code: next }, Payload { number: next });
                    fill(&mut *map, next + 1)
                },
            }
        }
        fn remove(map: &mut Map, code: i64) -> i64 {
            let key = Key { code: code };
            handle HashMap::remove(&mut *map, &key) {
                Result::Err(_) => 0,
                Result::Ok(value) => handle value.number == code { false => 0, true => 1 },
            }
        }
        fn replace_seven(map: &mut Map) -> i64 {
            handle HashMap::insert(&mut *map, Key { code: 7 }, Payload { number: 70 }) {
                Result::Err(_) => 0,
                Result::Ok(value) => handle value.number == 7 { false => 0, true => 1 },
            }
        }
        fn expected(code: i64) -> i64 { handle code == 7 { true => 70, false => code } }
        fn present(map: &Map, code: i64, expected: i64) -> i64 {
            let key = Key { code: code };
            handle HashMap::get(map, &key) {
                Result::Err(_) => 0,
                Result::Ok(value) => handle value.number == expected { false => 0, true => 1 },
            }
        }
        fn absent(map: &Map, code: i64) -> i64 {
            let key = Key { code: code };
            handle HashMap::contains_key(map, &key) { true => 0, false => 1 }
        }
        fn row(map: &Map, code: i64) -> i64 {
            handle code {
                0 => absent(map, code), 10 => absent(map, code), 23 => absent(map, code),
                _ => present(map, code, expected(code)),
            }
        }
        fn check(map: &Map, next: i64) -> i64 {
            handle next == 24 { true => 0, false => row(map, next) + check(map, next + 1) }
        }
        fn finish(map: &Map, changed: i64) -> i64 {
            handle changed == 4 {
                false => 0,
                true => handle HashMap::len(map) == 22 {
                    false => 0,
                    true => handle check(map, 0) == 24 {
                        false => 0,
                        true => handle present(map, 100, 1000) == 1 { false => 0, true => 42 },
                    },
                },
            }
        }
        pub fn main() -> i64 {
            let map = HashMap<Key, Payload>::new();
            fill(&mut map, 0);
            let replaced = replace_seven(&mut map);
            let first = remove(&mut map, 0);
            let middle = remove(&mut map, 10);
            let last = remove(&mut map, 23);
            HashMap::insert(&mut map, Key { code: 100 }, Payload { number: 1000 });
            finish(&map, replaced + first + middle + last)
        }
    "#;
    for hash in ["as<usize>(value.code)", "0"] {
        let source = template.replace("@HASH@", hash);
        let outcome = StageZeroCompiler::new().compile(request(&source)).unwrap();
        assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
        let bytes = outcome.artifact.unwrap().canonical_bytes();
        let program = grandiose_stage0::decode_and_verify_program(&bytes).unwrap();
        assert_eq!(
            program.run_std_i64().unwrap(),
            42,
            "hash implementation: {hash}"
        );
    }
}

#[test]
fn hash_tables_preserve_the_original_affine_set_resident_on_duplicate_insert() {
    let source = r#"
        use std::*;
        pub struct Key { code: i64, payload: i64 }
        pub impl Use<[0, 1]> for Key {}
        pub impl Eq for Key {
            eq(left: &Key, right: &Key) -> Bool { left.code == right.code }
        }
        pub impl Hash for Key {
            hash(value: &Key, state: &mut Hasher) -> () { Hasher::write_usize(state, 0); }
        }
        fn removed(set: &HashSet<Key>, resident: Key) -> i64 {
            let key = Key { code: 2, payload: 0 };
            handle resident.payload == 10 {
                false => 0,
                true => handle HashSet::len(set) == 1 {
                    false => 0,
                    true => handle HashSet::contains(set, &key) {
                        false => 0, true => 42,
                    },
                },
            }
        }
        fn remove_first(set: &mut HashSet<Key>) -> i64 {
            let key = Key { code: 1, payload: 0 };
            handle HashSet::remove(&mut *set, &key) {
                Result::Err(_) => 0, Result::Ok(resident) => removed(& *set, resident),
            }
        }
        pub fn main() -> i64 {
            let set = HashSet<Key>::new();
            HashSet::insert(&mut set, Key { code: 1, payload: 10 });
            HashSet::insert(&mut set, Key { code: 2, payload: 20 });
            handle HashSet::insert(&mut set, Key { code: 1, payload: 99 }) {
                true => 0, false => remove_first(&mut set),
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    assert_eq!(
        grandiose_stage0::decode_and_verify_program(&bytes)
            .unwrap()
            .run_std_i64()
            .unwrap(),
        42
    );
}

#[test]
fn hash_tables_probe_past_tombstones_and_reuse_empty_tables() {
    let source = r#"
        use std::*;
        pub struct Key { code: i64 }
        pub impl Eq for Key { eq(left: &Key, right: &Key) -> Bool { left.code == right.code } }
        pub impl Hash for Key {
            hash(value: &Key, state: &mut Hasher) -> () { Hasher::write_usize(state, 0); }
        }
        pub type Map = HashMap<Key, i64>;
        fn fill(map: &mut Map, code: i64) -> () {
            handle code == 7 {
                true => (),
                false => {
                    HashMap::insert(&mut *map, Key { code: code }, code);
                    fill(&mut *map, code + 1)
                },
            }
        }
        fn remove(map: &mut Map, code: i64, expected: i64) -> i64 {
            let key = Key { code: code };
            handle HashMap::remove(&mut *map, &key) {
                Result::Err(_) => 0,
                Result::Ok(value) => handle value == expected { false => 0, true => 1 },
            }
        }
        fn absent(map: &Map, code: i64) -> i64 {
            let key = Key { code: code };
            handle HashMap::get(map, &key) { Result::Ok(_) => 0, Result::Err(_) => 1 }
        }
        fn replace_three(map: &mut Map) -> i64 {
            handle HashMap::insert(map, Key { code: 3 }, 30) {
                Result::Err(_) => 0,
                Result::Ok(old) => handle old == 3 { false => 0, true => 1 },
            }
        }
        fn remove_even(map: &mut Map) -> i64 {
            remove(&mut *map, 2, 2) + remove(&mut *map, 4, 4) + remove(&mut *map, 6, 6)
        }
        fn remove_odd(map: &mut Map) -> i64 {
            remove(&mut *map, 1, 1) + remove(&mut *map, 3, 30) + remove(&mut *map, 5, 5)
        }
        fn cycle(map: &mut Map) -> i64 {
            fill(&mut *map, 0);
            let first = remove(&mut *map, 0, 0);
            let replaced = replace_three(&mut *map);
            let even = remove_even(&mut *map);
            // Three residents and four tombstones trigger same-size cleanup.
            HashMap::insert(&mut *map, Key { code: 7 }, 7);
            let missing = absent(& *map, 0) + absent(& *map, 8);
            let odd = remove_odd(&mut *map);
            let last = remove(&mut *map, 7, 7);
            let head = first + replaced + even;
            handle HashMap::is_empty(& *map) { false => 0, true => head + missing + odd + last }
        }
        fn repeat(map: &mut Map, remaining: i64) -> i64 {
            handle remaining == 0 {
                true => 42,
                false => handle cycle(&mut *map) == 11 {
                    false => 0, true => repeat(&mut *map, remaining - 1),
                },
            }
        }
        pub fn main() -> i64 { let map = HashMap<Key, i64>::new(); repeat(&mut map, 20) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    let program = grandiose_stage0::decode_and_verify_program(&bytes).unwrap();
    assert_eq!(program.run_std_i64().unwrap(), 42);
    // SAFETY: same freshly compiled, trusted source as the ordinary run above.
    let (value, profile) = unsafe { program
        .run_i64_for_authoring_with_unsafe(grandiose_stage0::VmExecutionLimits {
            max_call_depth: 64,
            ..Default::default()
        }) }
        .unwrap();
    assert_eq!(value, 42);
    assert!(profile.peak_call_depth < 64);
}

#[test]
fn hash_table_mutable_lookup_and_entry_removal_preserve_the_resident_key() {
    let source = r#"
        use std::*;
        pub struct Key { code: i64, stamp: i64 }
        pub impl Use<[0, 1]> for Key {}
        pub impl Eq for Key { eq(left: &Key, right: &Key) -> Bool { left.code == right.code } }
        pub impl Hash for Key {
            hash(value: &Key, state: &mut Hasher) -> () { Hasher::write_usize(state, as<usize>(value.code)); }
        }
        pub struct Item { value: i64 }
        pub impl Use<[0, 1]> for Item {}
        pub type Map = HashMap<Key, Item>;
        // The generic API must not demand that either field can be discarded.
        fn take_entry<K, V>(map: &mut HashMap<K, V>, key: &K) -> Option<(K, V)>
            where K: Eq, K: Hash { HashMap::remove_entry(map, key) }
        fn update(map: &mut Map, key: &Key) -> () {
            handle HashMap::get_mut(map, key) {
                Result::Err(_) => (),
                Result::Ok(item) => { (*item).value = item.value + 10; },
            }
        }
        fn finish(map: &mut Map, key: &Key) -> i64 {
            update(&mut *map, key);
            handle take_entry(&mut *map, key) {
                Result::Err(_) => 0,
                Result::Ok((resident, item)) => handle resident.stamp == 10 {
                    false => 0,
                    true => handle HashMap::is_empty(& *map) { false => 0, true => item.value },
                },
            }
        }
        pub fn main() -> i64 {
            let map = HashMap<Key, Item>::new();
            HashMap::insert(&mut map, Key { code: 1, stamp: 10 }, Item { value: 7 });
            let key = Key { code: 1, stamp: 0 };
            handle HashMap::insert(&mut map, Key { code: 1, stamp: 99 }, Item { value: 32 }) {
                Result::Err(_) => 0,
                Result::Ok(old) => handle old.value == 7 { false => 0, true => finish(&mut map, &key) },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    assert_eq!(
        grandiose_stage0::decode_and_verify_program(&bytes)
            .unwrap()
            .run_std_i64()
            .unwrap(),
        42
    );
}

#[test]
fn hash_table_indexed_lookup_work_does_not_scan_unrelated_entries() {
    let template = include_str!("fixtures/hash_indexing_profile.glorious");
    // Subtract the identical construction workload. These are logical VM
    // work ticks, NOT a claim about backing-object copies or physical bytes.
    let mut lookup_work = Vec::new();
    for size in [8, 64] {
        let mut work = Vec::new();
        for read in [0, 1] {
            let source = template
                .replace("@SIZE@", &size.to_string())
                .replace("@READ@", &read.to_string());
            let outcome = StageZeroCompiler::new().compile(request(&source)).unwrap();
            let bytes = outcome.artifact.unwrap().canonical_bytes();
            let program = grandiose_stage0::decode_and_verify_program(&bytes).unwrap();
            // SAFETY: this fixed source fixture uses only trusted stdlib unsafe code.
            let (value, profile) = unsafe { program
                .run_i64_for_authoring_with_unsafe(grandiose_stage0::VmExecutionLimits {
                    max_call_depth: 64,
                    ..Default::default()
                }) }
                .unwrap();
            assert_eq!(value, 42);
            assert!(profile.peak_call_depth < 64);
            eprintln!("hash table size={size}, read={read}: {profile:?}");
            work.push(profile.work_ticks);
        }
        lookup_work.push(work[1].checked_sub(work[0]).unwrap());
    }
    assert!(lookup_work[0] > 0);
    assert_eq!(lookup_work[0], lookup_work[1], "{lookup_work:?}");
}

#[test]
fn vec_drain_moves_a_checked_window_into_the_owned_iterator() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec<i64>::new();
            Vec::push(&mut values, 10);
            Vec::push(&mut values, 20);
            Vec::push(&mut values, 30);
            let range = Range { start: Vec::len(&values) - 2, end: Vec::len(&values) };
            handle Vec::drain(&mut values, range) {
                Result::Err(_) => 0,
                Result::Ok(iterator) => handle VecIntoIter::next(&mut iterator) {
                    Result::Err(_) => 0,
                    Result::Ok(first) => handle VecIntoIter::next(&mut iterator) {
                        Result::Err(_) => 0,
                        Result::Ok(second) => handle Vec::pop(&mut values) {
                            Result::Err(_) => 0,
                            Result::Ok(remaining) => first + second + remaining,
                        },
                    },
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 60);
}

#[test]
fn source_defined_slice_search_and_vec_algorithms_preserve_ordered_results() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let values = Vec<i64>::new();
            Vec::push(&mut values, 1);
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 3);
            Vec::sort_unstable(&mut values);
            Vec::sort_stable(&mut values);
            Vec::dedup(&mut values);
            let view = Vec::as_slice(&values);
            let needle = Vec::last(&values);
            handle needle {
                Result::Err(_) => 0,
                Result::Ok(needle) => handle Slice::binary_search(view, needle) {
                    Result::Err(_) => 0,
                    Result::Ok(found) => handle Slice::lex_compare(view, view) {
                        Ordering::Equal => found + Slice::lower_bound(view, needle) + Slice::upper_bound(view, needle),
                        _ => 0,
                    },
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 7);
}

#[test]
fn conditional_move_of_generic_value_keeps_the_selected_arm_live() {
    let source = r#"
        use std::*;
        pub struct Holder<T> { entries: Vec<T> }
        pub fn insert<T>(holder: &mut Holder<T>, item: T) -> () {
            handle false {
                false => Vec::push(&mut (*holder).entries, item),
                true => (),
            }
        }
        pub fn main() -> usize {
            let holder = Holder<i64> { entries: Vec<i64>::new() };
            insert(&mut holder, 42);
            Vec::len(&holder.entries)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn result_branch_move_of_generic_value_keeps_the_selected_arm_live() {
    let source = r#"
        use std::*;
        pub struct Holder<T> { entries: Vec<T> }
        pub fn insert<T>(holder: &mut Holder<T>, item: T) -> () {
            let missing = Result<usize, ()>::Err(());
            handle missing {
                Result::Err(_) => Vec::push(&mut (*holder).entries, item),
                Result::Ok(_) => (),
            }
        }
        pub fn main() -> usize {
            let holder = Holder<i64> { entries: Vec<i64>::new() };
            insert(&mut holder, 42);
            Vec::len(&holder.entries)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn returned_non_reference_result_releases_a_shared_reborrow_before_mutation() {
    let source = r#"
        use std::*;
        pub struct Holder<T> { entries: Vec<T> }
        pub fn probe<T>(holder: &Holder<T>) -> Option<usize> { Result::Err(()) }
        pub fn insert<T>(holder: &mut Holder<T>, item: T) -> () {
            handle probe(& *holder) {
                Result::Err(_) => Vec::push(&mut (*holder).entries, item),
                Result::Ok(_) => (),
            }
        }
        pub fn main() -> usize {
            let holder = Holder<i64> { entries: Vec<i64>::new() };
            insert(&mut holder, 42);
            Vec::len(&holder.entries)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn range_helpers_are_source_defined_half_open_operations() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let left = Range<usize> { start: 2, end: 8 };
            let right = Range<usize> { start: 5, end: 11 };
            handle Range::intersection(&left, &right) {
                Result::Ok(shared) => Range::len(&shared),
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 3);
}

#[test]
fn range_checked_offset_is_a_source_defined_checked_operation() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let range = Range<usize> { start: 2, end: 8 };
            handle Range::checked_offset(&range, 3) {
                Result::Ok(shifted) => Range::len(&shifted),
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 6);
}

#[test]
fn bundled_fold_until_threads_state_and_can_leave_through_a_label() {
    let source = r#"
        use std::*;
        pub fn add_until_three(total: i64, index: usize) -> Result<i64, i64> {
            handle index == 3 {
                true => Result::Err(total),
                false => Result::Ok(total + 1),
            }
        }
        pub fn main() -> i64 {
            @found: i64 {
                fold_until(
                    Range<usize> { start: 0, end: 8 },
                    0,
                    @found,
                    add_until_three,
                )
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 3);
}

#[test]
fn bundled_loop_state_uses_source_defined_break_and_continue_values() {
    let source = r#"
        use std::*;
        pub fn count_to_three(state: i64) -> LoopStep<i64, i64> {
            handle state == 3 {
                true => break(state),
                false => continue(state + 1),
            }
        }
        pub fn main() -> i64 { loop_state(0, count_to_three) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 3);
}

#[test]
fn bundled_return_forwards_to_a_named_function_implicit_label() {
    let source = r#"
        use std::*;
        pub fn select() -> i64 { return(42, @select) }
        pub fn main() -> i64 { select() }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_return_can_be_selected_from_a_conditional_branch() {
    let source = r#"
        use std::*;
        pub fn select(value: i64) -> i64 {
            handle value == 0 {
                true => return(42, @select),
                false => value,
            }
        }
        pub fn main() -> i64 { select(0) + select(1) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 43);
}

#[test]
fn bundled_yield_await_and_fail_are_source_defined_effect_operations() {
    let source = r#"
        use std::*;
        pub fn yielded() -> i64 {
            handle yield(7) {
                Yield<i64>::yield(_) => (),
            };
            42
        }
        pub fn awaited() -> i64 {
            handle await(42) {
                Await<i64>::await(value) => value,
            }
        }
        pub fn failed() -> i64 {
            handle fail(42) {
                Fail<i64>::fail(error) => error,
            }
        }
        pub fn main() -> i64 { yielded() + awaited() + failed() }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 126);
}

#[test]
fn compiler_bundles_std_for_regular_application_requests() {
    let mut input = request(
        r#"
            use std::*;
            pub fn main() -> i64 { identity(42) }
        "#,
    );
    input.sources.truncate(1);
    let outcome = StageZeroCompiler::new()
        .compile(input)
        .expect("regular requests must receive the bundled standard package");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_owns_native_storage_in_source() {
    let mut input = request(
        r#"
            use std::*;
            pub fn main() -> i64 {
                let values = Vec::new();
                Vec::push(&mut values, 20);
                Vec::push(&mut values, 22);
                handle Vec::pop(&mut values) {
                    Result::Ok(value) => value,
                    Result::Err(_) => 0,
                }
            }
        "#,
    );
    input.sources.truncate(1);
    let outcome = StageZeroCompiler::new()
        .compile(input)
        .unwrap_or_else(|failure| {
            for diagnostic in failure.diagnostics() {
                let source = include_str!("../../../stdlib/src/lib.glorious");
                let location = diagnostic.primary.map(|span| {
                    let start = span.start as usize;
                    let end = span.end as usize;
                    format!("line {}: {}", source[..start.min(source.len())].lines().count(), source.get(start..end).unwrap_or("<application>"))
                }).unwrap_or_default();
                eprintln!("{} {} {location}", diagnostic.code, diagnostic.message);
            }
            panic!("bundled source Vec failed to compile")
        });
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    // SAFETY: this fixture executes the locally compiled bundled library;
    // no user-defined unsafe function or untrusted bytecode is supplied.
    assert_eq!(unsafe { outcome.artifact.unwrap().run_i64_with_unsafe(grandiose_stage0::VmExecutionLimits::default()) }.unwrap(), 22);
}

#[test]
fn bundled_vec_exposes_borrowed_element_access_through_library_functions() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            r#"
                use std::*;
                pub fn main() -> i64 {
                    let values = Vec::new();
                    Vec::push(&mut values, 40);
                    *Vec::get_unchecked(&values, 0) + 2
                }
            "#,
        ))
        .expect("Vec borrowed access must lower through trusted array leaves");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_uses_source_capacity_helper() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let values = Vec::with_capacity(4);
            Vec::push(&mut values, 17);
            Vec::capacity(&values)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert!(outcome.artifact.unwrap().run_std_usize().unwrap() >= 4);
}

#[test]
fn bundled_vec_exposes_an_ordinary_borrowed_slice_view() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let values = Vec::new();
            Vec::push(&mut values, 17);
            let view = Vec::as_slice(&values);
            Slice::len(&view)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn bundled_slice_get_checks_its_window_and_preserves_the_borrow() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 40);
            let view = Vec::as_slice(&values);
            handle Slice::get(view, 0) {
                Result::Ok(value) => *value + 2,
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_slice_subslice_is_checked_and_uses_the_same_backing_storage() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 10);
            Vec::push(&mut values, 32);
            let view = Vec::as_slice(&values);
            handle Slice::slice(view, Range<usize> { start: 1, end: 2 }) {
                Result::Ok(window) => *Slice::get_unchecked(window, 0) + 10,
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_slice_split_at_returns_two_checked_views() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 20);
            Vec::push(&mut values, 22);
            handle Slice::split_at(Vec::as_slice(&values), 1) {
                Result::Ok((left, right)) => *Slice::get_unchecked(left, 0) + *Slice::get_unchecked(right, 0),
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_mut_slice_exposes_checked_unique_element_borrows() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 2);
            let view = Vec::as_mut_slice(&mut values);
            handle SliceMut::get(view, 0) {
                Result::Ok(item) => {
                    *item = 42;
                    *Vec::get_unchecked(&values, 0)
                },
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_mut_slice_split_at_returns_two_disjoint_mutable_views() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 22);
            let view = Vec::as_mut_slice(&mut values);
            handle SliceMut::split_at(view, 1) {
                Result::Ok((left, right)) => handle SliceMut::get(left, 0) {
                    Result::Ok(first) => handle SliceMut::get(right, 0) {
                        Result::Ok(second) => {
                            *first = 20;
                            *first + *second
                        },
                        Result::Err(_) => 0,
                    },
                    Result::Err(_) => 0,
                },
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_get_is_checked() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 40);
            handle Vec::get(&values, 1) {
                Result::Ok(value) => *value,
                Result::Err(_) => 42,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_first_and_last_are_source_defined_checked_borrows() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 40);
            handle Vec::first(&values) {
                Result::Ok(first) => handle Vec::last(&values) {
                    Result::Ok(last) => *first + *last,
                    Result::Err(_) => 0,
                },
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_swap_moves_elements_out_and_restores_them() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 40);
            Vec::swap(&mut values, 0, 1);
            *Vec::get_unchecked(&values, 0) + *Vec::get_unchecked(&values, 1)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_swap_remove_transfers_the_selected_element() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 40);
            handle Vec::swap_remove(&mut values, 0) {
                Result::Ok(removed) => removed + *Vec::get_unchecked(&values, 0),
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_insert_and_remove_preserve_element_order() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 40);
            handle Vec::insert(&mut values, 1, 7) {
                Result::Err(_) => 0,
                Result::Ok(_) => handle Vec::remove(&mut values, 1) {
                    Result::Err(_) => 0,
                    Result::Ok(removed) => removed
                        + *Vec::get_unchecked(&values, 0)
                        + *Vec::get_unchecked(&values, 1),
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 49);
}

#[test]
fn bundled_vec_insert_from_slice_copies_a_borrowed_window() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let source = Vec::new();
            Vec::push(&mut source, 2);
            let destination = Vec::new();
            Vec::push(&mut destination, 40);
            handle Vec::insert_from_slice(&mut destination, 0, Vec::as_slice(&source)) {
                Result::Err(_) => 0,
                Result::Ok(_) => *Vec::get_unchecked(&destination, 0)
                    + *Vec::get_unchecked(&destination, 1),
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_append_transfers_exact_linear_elements() {
    let source = r#"
        use std::*;
        struct Ticket { value: i64 }
        impl Use<[1, 1]> for Ticket {}

        pub fn main() -> i64 {
            let destination = Vec::new();
            let source = Vec::new();
            Vec::push(&mut source, Ticket { value: 42 });
            Vec::append(&mut destination, source);
            handle Vec::pop(&mut destination) {
                Result::Ok(ticket) => ticket.value,
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_truncate_and_clear_discard_affine_or_duplicable_residents() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 40);
            Vec::truncate(&mut values, 1);
            handle Vec::pop(&mut values) {
                Result::Err(_) => 0,
                Result::Ok(retained) => retained,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 2);
}

#[test]
fn bundled_vec_clear_discards_duplicable_residents() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let values = Vec::new();
            Vec::push(&mut values, 2);
            Vec::clear(&mut values);
            Vec::len(&values)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 0);
}

#[test]
fn bundled_vec_clear_rejects_exact_linear_residents() {
    let source = r#"
        use std::*;
        struct Ticket { value: i64 }
        impl Use<[1, 1]> for Ticket {}
        pub fn main() -> () {
            let values = Vec::new();
            Vec::push(&mut values, Ticket { value: 42 });
            Vec::clear(&mut values)
        }
    "#;
    assert!(
        StageZeroCompiler::new().compile(request(source)).is_err(),
        "an exact-linear Vec must not satisfy Vec::clear's affine-discard bound",
    );
}

#[test]
fn bundled_vec_reverse_preserves_exact_linear_elements() {
    let source = r#"
        use std::*;
        struct Ticket { value: i64 }
        impl Use<[1, 1]> for Ticket {}
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, Ticket { value: 2 });
            Vec::push(&mut values, Ticket { value: 40 });
            Vec::reverse(&mut values);
            handle Vec::pop(&mut values) {
                Result::Err(_) => 0,
                Result::Ok(first) => handle Vec::pop(&mut values) {
                    Result::Err(_) => 0,
                    Result::Ok(second) => first.value + second.value,
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_split_off_transfers_an_exact_linear_suffix() {
    let source = r#"
        use std::*;
        struct Ticket { value: i64 }
        impl Use<[1, 1]> for Ticket {}
        pub fn main() -> i64 {
            let values = Vec::new();
            Vec::push(&mut values, Ticket { value: 2 });
            Vec::push(&mut values, Ticket { value: 40 });
            handle Vec::split_off(&mut values, 1) {
                Result::Err(_) => 0,
                Result::Ok(tail) => handle Vec::pop(&mut values) {
                    Result::Err(_) => 0,
                    Result::Ok(left) => handle Vec::pop(&mut tail) {
                        Result::Err(_) => 0,
                        Result::Ok(right) => left.value + right.value,
                    },
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_deque_is_a_source_level_fifo_wrapper() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = VecDeque::new();
            VecDeque::push_back(&mut values, 40);
            VecDeque::push_front(&mut values, 2);
            handle VecDeque::pop_front(&mut values) {
                Result::Err(_) => 0,
                Result::Ok(first) => handle VecDeque::pop_back(&mut values) {
                    Result::Err(_) => 0,
                    Result::Ok(second) => first + second,
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_stack_and_work_list_are_source_level_lifo_wrappers() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let stack = Stack::new();
            Stack::push(&mut stack, 2);
            Stack::push(&mut stack, 40);
            let work = WorkList::new();
            WorkList::push(&mut work, 2);
            WorkList::push(&mut work, 40);
            handle Stack::pop(&mut stack) {
                Result::Err(_) => 0,
                Result::Ok(stack_top) => handle WorkList::pop(&mut work) {
                    Result::Err(_) => 0,
                    Result::Ok(work_top) => stack_top + work_top,
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 80);
}

#[test]
fn bundled_formatter_and_generic_display_dispatch_are_source_defined() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let original = Str::to_string("hi");
            let rendered = format(&original);
            let debugged = format_debug(&original);
            String::len(&rendered) + String::len(&debugged)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 4);
}

#[test]
fn string_insert_splices_utf8_at_a_character_boundary() {
    let source = r#"
        use std::*;
        pub fn main() -> u8 {
            let value = Str::to_string("ho");
            handle String::insert(&mut value, 1, "ell") {
                Result::Err(_) => 0,
                Result::Ok(_) => handle Slice::get(Str::as_bytes(String::as_str(&value)), 2) {
                    Result::Ok(byte) => *byte,
                    Result::Err(_) => 0,
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_u8().unwrap(), b'l');
}

#[test]
fn string_insert_rejects_a_non_character_boundary() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let value = Str::to_string("aé");
            handle String::insert(&mut value, 2, "x") {
                Result::Err(StringRangeError::NotCharBoundary) => String::len(&value),
                _ => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 3);
}

#[test]
fn string_pop_removes_one_complete_utf8_character() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let value = Str::to_string("aé");
            handle String::pop(&mut value) {
                Result::Err(_) => 0,
                Result::Ok(last) => {
                    let rendered = String::new();
                    String::push(&mut rendered, last);
                    String::len(&value) + String::len(&rendered)
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 3);
}

#[test]
fn str_chars_iterates_complete_utf8_characters_from_static_data() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let chars = Str::chars("aé");
            let output = String::new();
            handle Chars::next(&mut chars) {
                Result::Err(_) => 0,
                Result::Ok(first) => {
                    String::push(&mut output, first);
                    handle Chars::next(&mut chars) {
                        Result::Err(_) => 0,
                        Result::Ok(second) => {
                            String::push(&mut output, second);
                            handle Chars::next(&mut chars) {
                                Result::Ok(_) => 0,
                                Result::Err(_) => String::len(&output),
                            }
                        },
                    }
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 3);
}

#[test]
fn str_char_at_checks_byte_boundaries_and_returns_owned_scalars_from_static_and_dynamic_views() {
    let source = r#"
        use std::*;
        fn scalar(value: Str, index: usize, expected: u32) -> usize {
            handle Str::char_at(value, index) {
                Result::Err(_) => 0,
                Result::Ok(character) => handle char_to_u32(character) == expected { true => 1, false => 0 },
            }
        }
        fn error(value: Str, index: usize, expected: usize) -> usize {
            handle Str::char_at(value, index) {
                Result::Ok(_) => 0,
                Result::Err(problem) => handle problem {
                    StringRangeError::OutOfBounds => handle expected == 0 { true => 1, false => 0 },
                    StringRangeError::NotCharBoundary => handle expected == 1 { true => 1, false => 0 },
                    _ => 0,
                },
            }
        }
        fn owned() -> Result<char, StringRangeError> {
            let local = Str::to_string("é");
            let view = String::as_str(&local);
            Str::char_at(view, 0)
        }
        fn owned_case() -> usize {
            handle owned() {
                Result::Err(_) => 0, Result::Ok(character) => handle char_to_u32(character) == 233 { true => 1, false => 0 },
            }
        }
        pub fn main() -> usize {
            let text = Str::to_string("aé😀\0");
            let view = String::as_str(&text);
            let characters = scalar(view, 0, 97) + scalar(view, 1, 233) + scalar(view, 3, 128512) + scalar(view, 7, 0);
            let boundaries = error(view, 2, 1) + error(view, 4, 1) + error(view, 5, 1) + error(view, 6, 1);
            let bounds = error(view, 8, 0) + error(view, 9, 0) + error(view, 18446744073709551615, 0) + error("", 0, 0);
            let literals = scalar("é", 0, 233) + error("é", 1, 1) + error("é", 2, 0);
            characters + boundaries + bounds + literals + owned_case()
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 16);
}

#[test]
fn str_chars_uses_the_same_iterator_for_dynamic_string_storage() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let text = Str::to_string("é");
            let view = String::as_str(&text);
            let chars = Str::chars(view);
            handle Chars::next(&mut chars) {
                Result::Err(_) => 0,
                Result::Ok(character) => {
                    let output = String::new();
                    String::push(&mut output, character);
                    String::len(&output)
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 2);
}

#[test]
fn string_owns_a_vec_and_borrows_the_same_str_view() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let value = String::new();
            Str::len(String::as_str(&value))
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 0);
}

#[test]
fn named_string_views_preserve_the_nested_owner_lifetime() {
    let source = r#"
        use std::*;
        pub struct Blob { text: String }
        pub fn text<'a>(blob: &'a Blob) -> Str<'a> { String::as_str(&blob.text) }
        pub fn bytes<'a>(blob: &'a Blob) -> Slice<'a, u8> { Str::as_bytes(text(blob)) }
        pub fn main() -> i64 {
            let blob = Blob { text: Str::to_string("*é😀") };
            let view = bytes(&blob);
            as<i64>(*Slice::get_unchecked(view, 0)) + as<i64>(Slice::len(&view))
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 49);
}

#[test]
fn named_string_views_do_not_allow_local_owner_escape() {
    let source = r#"
        use std::*;
        pub fn escape<'a>() -> Slice<'a, u8> {
            let text = Str::to_string("local");
            Str::as_bytes(String::as_str(&text))
        }
        pub fn main() -> i64 { 42 }
    "#;
    let error = StageZeroCompiler::new().compile(request(source)).unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5017"), "{error:?}");
}

#[test]
fn implicit_string_views_do_not_allow_local_owner_escape() {
    let source = r#"
        use std::*;
        fn view(value: Str) -> Str { value }
        pub fn escape<'a>() -> Str<'a> {
            let text = Str::to_string("local");
            view(&text)
        }
        pub fn main() -> i64 { 42 }
    "#;
    let error = StageZeroCompiler::new().compile(request(source)).unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5017"), "{error:?}");
}

#[test]
fn static_literal_views_satisfy_generic_lifetime_call_contexts() {
    let source = r#"
        use std::*;
        fn text<'a>(value: Str<'a>) -> Slice<'a, u8> { Str::as_bytes(value) }
        fn bytes<'a>(value: Slice<'a, u8>) -> Slice<'a, u8> { value }
        pub fn literal<'a>() -> Str<'a> { "static" }
        pub fn main() -> usize {
            let direct = Str::as_bytes("abc");
            let empty = Str::as_bytes("");
            let unicode = text("é😀");
            let raw = bytes(b"\x00\xff");
            Slice::len(&direct) + Slice::len(&empty) + Slice::len(&unicode)
                + Slice::len(&raw) + Str::len(literal<'static>())
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 17);
}

#[test]
fn generic_literal_view_contexts_do_not_promote_local_string_borrows_to_static() {
    let source = r#"
        use std::*;
        fn view<'a>(value: Str<'a>) -> Str<'a> { value }
        pub fn escape() -> Str<'static> {
            let text = Str::to_string("local");
            view(&text)
        }
        pub fn main() -> i64 { 42 }
    "#;
    let error = StageZeroCompiler::new().compile(request(source)).unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5017"), "{error:?}");
}

#[test]
fn empty_string_views_survive_nested_vector_extraction_and_calls() {
    let source = r#"
        use std::*;
        fn owned(value: Slice<u8>) -> Vec<u8> {
            let bytes = Vec<u8>::new();
            Vec::extend_from_slice(&mut bytes, value);
            bytes
        }
        fn digest(value: Vec<u8>) -> usize {
            handle String::from_utf8(value) {
                Result::Err(_) => 0,
                Result::Ok(text) => {
                    let fingerprint = blake3(Str::as_bytes(String::as_str(&text)));
                    Vec::len(&fingerprint)
                },
            }
        }
        pub fn main() -> usize {
            let inputs = Vec<Vec<u8>>::new();
            Vec::push(&mut inputs, owned(b""));
            handle Vec::get(&inputs, 0) { Result::Err(_) => 0, Result::Ok(bytes) => digest(*bytes) }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let program = outcome.artifact.unwrap();
    assert_eq!(program.run_std_usize().unwrap(), 32);
}

#[test]
fn blake3_returns_the_complete_digest_for_empty_text_and_binary_input() {
    let source = r#"
        use std::*;
        fn check(value: &Vec<u8>, expected: Slice<u8>, index: usize) -> i64 {
            handle index < Slice::len(&expected) {
                false => 42,
                true => handle *Vec::get_unchecked(value, index) == *Slice::get_unchecked(expected, index) {
                    false => 0,
                    true => check(value, expected, index + 1),
                },
            }
        }
        pub fn main() -> i64 {
            let digest = blake3(@INPUT@);
            handle Vec::len(&digest) == 32 {
                false => 0,
                true => check(&digest, @EXPECTED@, 0),
            }
        }
    "#;
    let bytes_literal = |bytes: &[u8]| {
        format!("b\"{}\"", bytes.iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>())
    };
    for input in [b"".as_slice(), b"abc", b"\x00\xff\xc3\xa9"] {
        let expected = blake3::hash(input);
        assert_eq!(expected.as_bytes().len(), 32);
        let application = source.replace("@INPUT@", &bytes_literal(input))
            .replace("@EXPECTED@", &bytes_literal(expected.as_bytes()));
        let program = StageZeroCompiler::new().compile(request(&application)).unwrap().artifact.unwrap();
        assert_eq!(program.run_std_i64().unwrap(), 42);
    }
}

#[test]
fn string_borrow_coerces_to_an_elided_str_parameter() {
    let source = r#"
        use std::*;
        fn show(value: Str) -> usize { Str::len_bytes(value) }
        pub fn main() -> usize {
            let value = Str::to_string("hello");
            show(&value)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 5);
}

#[test]
fn string_push_encodes_a_char_into_its_vec_backing() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let value = String::new();
            String::push(&mut value, 'A');
            String::push(&mut value, 'é');
            Str::len_bytes(String::as_str(&value))
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 3);
}

#[test]
fn vec_extend_from_slice_and_string_push_str_copy_borrowed_bytes() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let bytes = Vec::new();
            Vec::push(&mut bytes, 65);
            let bytes_view = Vec::as_slice(&bytes);
            Vec::extend_from_slice(&mut bytes, bytes_view);

            let value = String::new();
            String::push_str(&mut value, "hé");
            Vec::len(&bytes) + Str::len_bytes(String::as_str(&value))
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 5);
}

#[test]
fn str_to_string_allocates_an_owned_utf8_copy() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let owned = Str::to_string("hé");
            Str::len_bytes(String::as_str(&owned))
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 3);
}

#[test]
fn string_from_utf8_validates_its_vec_storage_without_a_text_scalar() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let bytes = Vec<u8>::new();
            Vec::push(&mut bytes, 104);
            Vec::push(&mut bytes, 105);
            handle String::from_utf8(bytes) {
                Result::Ok(value) => String::len(&value),
                Result::Err(error) => Utf8Error::valid_up_to(&error),
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 2);
}

#[test]
fn string_from_utf8_returns_its_bytes_and_valid_prefix_on_error() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            let bytes = Vec<u8>::new();
            Vec::push(&mut bytes, 97);
            Vec::push(&mut bytes, 255);
            handle String::from_utf8(bytes) {
                Result::Ok(_) => 0,
                Result::Err(error) => {
                    let valid = Utf8Error::valid_up_to(&error);
                    let restored = Utf8Error::into_bytes(error);
                    handle Vec::len(&restored) { 2 => valid, _ => 0 }
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 1);
}

#[test]
fn str_slice_checks_range_order_bounds_and_utf8_boundaries() {
    let source = r#"
        use std::*;
        pub fn main() -> usize {
            handle Str::slice("a", Range<usize> { start: 2, end: 1 }) {
                Result::Err(StringRangeError::Reversed) => handle Str::slice("a", Range<usize> { start: 0, end: 2 }) {
                    Result::Err(StringRangeError::OutOfBounds) => handle Str::slice("aé", Range<usize> { start: 1, end: 3 }) {
                        Result::Ok(value) => handle Str::slice(value, Range<usize> { start: 1, end: 2 }) {
                            Result::Ok(_) => 0,
                            Result::Err(StringRangeError::NotCharBoundary) => Str::len_bytes(value),
                            Result::Err(_) => 0,
                        },
                        Result::Err(_) => 0,
                    },
                    Result::Err(_) => 0,
                    Result::Ok(_) => 0,
                },
                Result::Err(_) => 0,
                Result::Ok(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_usize().unwrap(), 2);
}

#[test]
fn option_is_the_source_defined_temporary_slot_without_default() {
    let mut input = request(
        r#"
            use std::*;
            struct Ticket { value: i64 }
            pub fn main() -> i64 {
                let slot = Some(Ticket { value: 41 });
                let previous = Option::insert(&mut slot, Ticket { value: 1 });
                let replacement = Option::take(&mut slot);
                handle previous {
                    Result::Ok(ticket) => handle replacement {
                        Result::Ok(old) => ticket.value + old.value,
                        Result::Err(_) => 0,
                    },
                    Result::Err(_) => 0,
                }
            }
        "#,
    );
    input.sources.truncate(1);
    let outcome = StageZeroCompiler::new()
        .compile(input)
        .expect("Option must supply take/insert without requiring Default");
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn option_replace_preserves_the_complete_previous_state() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let slot = Some(40);
            handle Option::replace(&mut slot, 2) {
                Result::Ok(previous) => previous + 1,
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 41);
}

#[test]
fn option_insertion_helpers_borrow_the_resident_value() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let empty = None;
            let inserted = Option::get_or_insert(&mut empty, 20);
            *inserted = *inserted + 1;
            handle empty {
                Result::Err(_) => 0,
                Result::Ok(left) => left + 21,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_iter_lends_elements_in_source_defined_order() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec<i64>::new();
            Vec::push(&mut values, 20);
            Vec::push(&mut values, 22);
            let iterator = Vec::iter(&values);
            handle SliceIter::next(&mut iterator) {
                Result::Err(_) => 0,
                Result::Ok(first) => {
                    let first_value = *first;
                    handle SliceIter::next(&mut iterator) {
                        Result::Err(_) => 0,
                        Result::Ok(second) => first_value + *second,
                    }
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_vec_into_iter_transfers_elements_in_source_defined_order() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec<i64>::new();
            Vec::push(&mut values, 20);
            Vec::push(&mut values, 22);
            let iterator = Vec::into_iter(values);
            handle VecIntoIter::next(&mut iterator) {
                Result::Err(_) => 0,
                Result::Ok(first) => handle VecIntoIter::next(&mut iterator) {
                    Result::Err(_) => 0,
                    Result::Ok(second) => first + second,
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_mut_slice_subslice_transfers_the_unique_view() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec<i64>::new();
            Vec::push(&mut values, 1);
            Vec::push(&mut values, 2);
            Vec::push(&mut values, 3);
            let view = Vec::as_mut_slice(&mut values);
            handle SliceMut::slice(view, Range<usize> { start: 1, end: 3 }) {
                Result::Err(_) => 0,
                Result::Ok(window) => handle SliceMut::get(window, 0) {
                    Result::Err(_) => 0,
                    Result::Ok(item) => {
                        *item = 42;
                        handle Vec::get(&values, 1) {
                            Result::Ok(updated) => *updated,
                            Result::Err(_) => 0,
                        }
                    },
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_wrapping_integer_helpers_preserve_each_scalar_width() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let wrapped_byte = wrapping_add<u8>(255, 1);
            handle wrapped_byte == 0 {
                false => 0,
                true => wrapping_mul(wrapping_sub(0, 1), 42),
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), -42);
}

#[test]
fn bundled_checked_i64_narrowing_returns_option_without_vm_overflow() {
    let source = r#"
        use std::*;
        pub fn main() -> u8 {
            handle i64_to_u8_checked(42) {
                Result::Err(_) => 0,
                Result::Ok(value) => value,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_u8().unwrap(), 42);
}

#[test]
fn bundled_checked_i64_narrowing_rejects_out_of_range_values_in_source() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            handle i64_to_i8_checked(128) {
                Result::Ok(_) => 0,
                Result::Err(_) => handle i64_to_u8_checked(-1) {
                    Result::Ok(_) => 0,
                    Result::Err(_) => 42,
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_i64_wrapping_conversions_follow_twos_complement_widths() {
    let source = r#"
        use std::*;
        pub fn main() -> u8 { i64_to_u8_wrapping(-1) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_u8().unwrap(), 255);
}

#[test]
fn bundled_try_propagates_result_errors_through_the_named_function_label() {
    let source = r#"
        use std::*;
        fn read(value: Bool) -> Result<i64, i64> {
            handle value {
                Result::Ok(_) => Result::Ok(41),
                Result::Err(_) => Result::Err(42),
            }
        }
        pub fn parse(value: Bool) -> Result<u8, i64> {
            let item = try(read(value), @parse);
            Result::Ok(i64_to_u8_wrapping(item + 1))
        }
        pub fn main() -> i64 {
            handle parse(false) {
                Result::Ok(_) => 0,
                Result::Err(error) => error,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_f32_to_i64_conversion_is_checked_in_the_public_library() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            handle f32_to_i64_checked(i64_to_f32(42)) {
                Result::Err(_) => 0,
                Result::Ok(value) => value,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_f32_to_i64_rejects_the_rounded_upper_boundary() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            handle f32_to_i64_checked(i64_to_f32(9223372036854775807)) {
                Result::Ok(_) => 0,
                Result::Err(_) => 42,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_f32_arithmetic_and_comparison_are_source_level_wrappers() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let sum = f32_add(i64_to_f32(40), i64_to_f32(2));
            handle f32_eq(sum, i64_to_f32(42)) {
                false => 0,
                true => handle f32_to_i64_checked(sum) {
                    Result::Err(_) => 0,
                    Result::Ok(value) => value,
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_f64_arithmetic_and_comparison_are_source_level_wrappers() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let sum = f64_add(40.0, 2.0);
            handle f64_eq(sum, 42.0) {
                false => 0,
                true => handle f64_to_i64_checked(sum) {
                    Result::Err(_) => 0,
                    Result::Ok(value) => value,
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn string_remove_checks_character_boundaries_and_moves_one_utf8_scalar() {
    let source = r#"
        use std::*;
        pub fn main() -> u32 {
            let value = Str::to_string("aé!");
            handle String::remove(&mut value, 1) {
                Result::Err(_) => 0,
                Result::Ok(character) => char_to_u32(character),
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_u32().unwrap(), 233);
}

#[test]
fn string_remove_rejects_a_utf8_continuation_offset() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let value = Str::to_string("aé");
            handle String::remove(&mut value, 2) {
                Result::Ok(_) => 0,
                Result::Err(StringRangeError::NotCharBoundary) => 42,
                Result::Err(_) => 0,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}

#[test]
fn bundled_mut_slice_iter_consumes_the_unique_view_and_lends_elements() {
    let source = r#"
        use std::*;
        pub fn main() -> i64 {
            let values = Vec<i64>::new();
            Vec::push(&mut values, 20);
            Vec::push(&mut values, 22);
            let iterator = SliceMut::iter(Vec::as_mut_slice(&mut values));
            handle SliceIter::next(&mut iterator) {
                Result::Err(_) => 0,
                Result::Ok(first) => {
                    let first_value = *first;
                    handle SliceIter::next(&mut iterator) {
                        Result::Err(_) => 0,
                        Result::Ok(second) => first_value + *second,
                    }
                },
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_std_i64().unwrap(), 42);
}
