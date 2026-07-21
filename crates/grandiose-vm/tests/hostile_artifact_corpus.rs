use std::panic::{AssertUnwindSafe, catch_unwind};

use grandiose_vm::{LoadError, load_verified};

const UNIT: &[u8] = include_bytes!("fixtures/g1-unit-return.grbc");
const I64: &[u8] = include_bytes!("fixtures/g1-i64-return.grbc");
const DIRECTORY_START: usize = 64;
const DIRECTORY_ENTRY_LEN: usize = 32;

fn load_without_panicking(label: &str, bytes: &[u8]) {
    let outcome = catch_unwind(AssertUnwindSafe(|| load_verified(bytes)));
    assert!(
        outcome.is_ok(),
        "verified loader panicked for {label} ({} bytes)",
        bytes.len()
    );
}

fn assert_rejected_without_panicking(label: &str, bytes: &[u8]) {
    let outcome = catch_unwind(AssertUnwindSafe(|| load_verified(bytes)));
    assert!(outcome.is_ok(), "verified loader panicked for {label}");
    assert!(
        matches!(
            outcome.unwrap(),
            Err(LoadError::Decode(_) | LoadError::Verify(_))
        ),
        "verified loader accepted {label}"
    );
}

fn directory_count(bytes: &[u8]) -> usize {
    u32::from_le_bytes(bytes[20..24].try_into().unwrap()) as usize
}

fn section_offset(bytes: &[u8], wanted: u32) -> usize {
    for index in 0..directory_count(bytes) {
        let entry = DIRECTORY_START + index * DIRECTORY_ENTRY_LEN;
        let id = u32::from_le_bytes(bytes[entry..entry + 4].try_into().unwrap());
        if id == wanted {
            return usize::try_from(u64::from_le_bytes(
                bytes[entry + 8..entry + 16].try_into().unwrap(),
            ))
            .unwrap();
        }
    }
    panic!("missing section {wanted}")
}

#[test]
fn deterministic_verified_loader_mutation_corpus_never_panics() {
    for (name, canonical) in [("unit", UNIT), ("i64", I64)] {
        for end in 0..=canonical.len() {
            load_without_panicking(&format!("{name} truncation at {end}"), &canonical[..end]);
        }

        for offset in 0..canonical.len() {
            for mask in [0x01, 0x80, 0xff] {
                let mut bytes = canonical.to_vec();
                bytes[offset] ^= mask;
                load_without_panicking(&format!("{name} byte mutation at {offset}"), &bytes);
            }
        }

        for offset in (0..canonical.len().saturating_sub(3)).step_by(4) {
            for value in [0, 1, u32::MAX, 0x8000_0000, canonical.len() as u32] {
                let mut bytes = canonical.to_vec();
                bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
                load_without_panicking(&format!("{name} u32 mutation at {offset}"), &bytes);
            }
        }

        for offset in (0..canonical.len().saturating_sub(7)).step_by(8) {
            for value in [
                0,
                1,
                u64::MAX,
                0x8000_0000_0000_0000,
                canonical.len() as u64,
            ] {
                let mut bytes = canonical.to_vec();
                bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
                load_without_panicking(&format!("{name} u64 mutation at {offset}"), &bytes);
            }
        }
    }

    let mut state = 0x243f_6a88_85a3_08d3_u64;
    let mut random = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for case in 0..2_000 {
        let length = match case % 4 {
            0 => case % 96,
            1 => random() as usize % 512,
            2 => random() as usize % 2_048,
            _ => random() as usize % 4_096,
        };
        let mut bytes = Vec::with_capacity(length);
        while bytes.len() < length {
            bytes.extend_from_slice(&random().to_le_bytes());
        }
        bytes.truncate(length);
        if case % 3 == 0 {
            let prefix = bytes.len().min(UNIT.len()).min(random() as usize % 65);
            bytes[..prefix].copy_from_slice(&UNIT[..prefix]);
        }
        load_without_panicking("fixed-seed arbitrary input", &bytes);
    }
}

#[test]
fn small_inputs_cannot_amplify_wire_counts_offsets_or_widths() {
    let count = directory_count(UNIT);
    let mut cases = Vec::new();

    let mut directory = UNIT.to_vec();
    directory[20..24].copy_from_slice(&u32::MAX.to_le_bytes());
    cases.push(("directory count", directory));

    for index in 0..count {
        let entry = DIRECTORY_START + index * DIRECTORY_ENTRY_LEN;
        for (field, range) in [
            ("offset", entry + 8..entry + 16),
            ("length", entry + 16..entry + 24),
        ] {
            let mut bytes = UNIT.to_vec();
            bytes[range].copy_from_slice(&u64::MAX.to_le_bytes());
            cases.push((field, bytes));
        }
        for (field, range) in [
            ("element count", entry + 24..entry + 28),
            ("element width", entry + 28..entry + 32),
        ] {
            let mut bytes = UNIT.to_vec();
            bytes[range].copy_from_slice(&u32::MAX.to_le_bytes());
            cases.push((field, bytes));
        }
    }

    let mut registers = UNIT.to_vec();
    let functions = section_offset(&registers, 8);
    registers[functions + 12..functions + 16].copy_from_slice(&u32::MAX.to_le_bytes());
    cases.push(("function register count", registers));

    for (label, bytes) in cases {
        assert!(
            bytes.len() < 2_048,
            "bounded corpus input unexpectedly grew"
        );
        assert_rejected_without_panicking(label, &bytes);
    }
}
