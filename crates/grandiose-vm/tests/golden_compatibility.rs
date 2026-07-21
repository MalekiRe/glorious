use std::panic::{AssertUnwindSafe, catch_unwind};

use grandiose_vm::{Artifact, LoadError, Value, Vm, load_verified};

const UNIT: &[u8] = include_bytes!("fixtures/g1-unit-return.grbc");
const I64: &[u8] = include_bytes!("fixtures/g1-i64-return.grbc");

const DIRECTORY_START: usize = 64;
const DIRECTORY_ENTRY_LEN: usize = 32;

#[test]
fn checked_in_g1_goldens_decode_verify_execute_and_reencode_identically() {
    for (name, bytes, expected) in [
        ("g1-unit-return", UNIT, Value::Unit),
        ("g1-i64-return", I64, Value::I64(42)),
    ] {
        let decoded = Artifact::decode(bytes)
            .unwrap_or_else(|error| panic!("{name} did not decode: {error}"));
        assert_eq!(decoded.encode(), bytes, "{name} is not canonical");

        let verified =
            load_verified(bytes).unwrap_or_else(|error| panic!("{name} did not verify: {error}"));
        let entry = verified.entry_function().unwrap_or(0);
        assert_eq!(
            Vm::new(verified).run(entry, vec![]),
            Ok(expected),
            "{name} execution drifted"
        );
    }
}

#[test]
fn every_golden_truncation_fails_closed_without_panicking() {
    for (name, bytes) in [("unit", UNIT), ("i64", I64)] {
        for end in 0..bytes.len() {
            assert_rejected(&format!("{name} truncation at {end}"), &bytes[..end]);
        }
    }
}

#[test]
fn deterministic_structural_corruption_corpus_fails_closed() {
    let mut cases = Vec::new();

    let mut bad_magic = UNIT.to_vec();
    bad_magic[0] ^= 0xff;
    cases.push(("bad magic", bad_magic));

    let mut unsupported_major = UNIT.to_vec();
    unsupported_major[8..10].copy_from_slice(&u16::MAX.to_le_bytes());
    cases.push(("unsupported major", unsupported_major));

    let mut false_file_length = UNIT.to_vec();
    false_file_length[56..64].copy_from_slice(&u64::MAX.to_le_bytes());
    cases.push(("false file length", false_file_length));

    let mut duplicate_section = UNIT.to_vec();
    duplicate_section
        [DIRECTORY_START + DIRECTORY_ENTRY_LEN..DIRECTORY_START + DIRECTORY_ENTRY_LEN + 4]
        .copy_from_slice(&1_u32.to_le_bytes());
    cases.push(("duplicate section", duplicate_section));

    let mut impossible_width = UNIT.to_vec();
    impossible_width[DIRECTORY_START + 28..DIRECTORY_START + 32]
        .copy_from_slice(&u32::MAX.to_le_bytes());
    cases.push(("impossible section width", impossible_width));

    let mut invalid_entry = UNIT.to_vec();
    invalid_entry[28..32].copy_from_slice(&u32::MAX.to_le_bytes());
    cases.push(("invalid entry function", invalid_entry));

    for (name, bytes) in cases {
        assert_rejected(name, &bytes);
    }
}

#[test]
fn allocation_amplification_counts_are_rejected_on_small_inputs() {
    let directory_count = u32::from_le_bytes(UNIT[20..24].try_into().unwrap()) as usize;
    let mut cases = Vec::new();

    let mut hostile_directory_count = UNIT.to_vec();
    hostile_directory_count[20..24].copy_from_slice(&u32::MAX.to_le_bytes());
    cases.push(("directory count", hostile_directory_count));

    for index in 0..directory_count {
        let mut hostile = UNIT.to_vec();
        let count = DIRECTORY_START + index * DIRECTORY_ENTRY_LEN + 24;
        hostile[count..count + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        cases.push(("section element count", hostile));
    }

    // Section 8 is the fixed-width function table. Its first record stores the
    // inferred register count at byte 12. This count previously represented a
    // particularly direct tiny-input-to-huge-allocation amplification path.
    let mut hostile_register_count = UNIT.to_vec();
    let functions = section_offset(&hostile_register_count, 8);
    hostile_register_count[functions + 12..functions + 16].copy_from_slice(&u32::MAX.to_le_bytes());
    cases.push(("function register count", hostile_register_count));

    for (name, bytes) in cases {
        assert!(bytes.len() < 2048, "hostile corpus input unexpectedly grew");
        assert_rejected(name, &bytes);
    }
}

fn section_offset(bytes: &[u8], wanted: u32) -> usize {
    let count = u32::from_le_bytes(bytes[20..24].try_into().unwrap()) as usize;
    for index in 0..count {
        let entry = DIRECTORY_START + index * DIRECTORY_ENTRY_LEN;
        let id = u32::from_le_bytes(bytes[entry..entry + 4].try_into().unwrap());
        if id == wanted {
            return usize::try_from(u64::from_le_bytes(
                bytes[entry + 8..entry + 16].try_into().unwrap(),
            ))
            .unwrap();
        }
    }
    panic!("missing section {wanted}");
}

fn assert_rejected(name: &str, bytes: &[u8]) {
    let outcome = catch_unwind(AssertUnwindSafe(|| load_verified(bytes)));
    assert!(outcome.is_ok(), "{name} panicked");
    assert!(
        matches!(
            outcome.unwrap(),
            Err(LoadError::Decode(_) | LoadError::Verify(_))
        ),
        "{name} was accepted"
    );
}
