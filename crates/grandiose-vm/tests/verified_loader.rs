use grandiose_vm::{
    Artifact, BYTES, Constant, DecodeError, Function, Instruction, LoadError, RuntimeError, TEXT,
    UNIT, Value, VerifyError, Vm, load_verified, verify::with_generated_cleanup_plans,
};

fn encoded_unit_program() -> Vec<u8> {
    let artifact = Artifact {
        entry_function: Some(0),
        functions: vec![Function {
            name: "main".into(),
            flags: 0,
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT],
            code_start: 0,
            code_len: 1,
            label_slot_count: 0,
        }],
        code: vec![Instruction::Return { src: None }],
        ..Artifact::default()
    };
    with_generated_cleanup_plans(artifact).unwrap().encode()
}

fn encoded_constant_program(constant: Constant, ty: u32) -> Vec<u8> {
    let artifact = Artifact {
        constants: vec![constant],
        functions: vec![Function {
            name: "main".into(),
            flags: 0,
            params: vec![],
            return_type: ty,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, ty],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        }],
        code: vec![
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Return { src: Some(1) },
        ],
        ..Artifact::default()
    };
    with_generated_cleanup_plans(artifact).unwrap().encode()
}

fn u64_at(bytes: &[u8], offset: usize) -> usize {
    usize::try_from(u64::from_le_bytes(
        bytes[offset..offset + 8].try_into().unwrap(),
    ))
    .unwrap()
}

fn section_offset(bytes: &[u8], wanted: u32) -> usize {
    let count = u32::from_le_bytes(bytes[20..24].try_into().unwrap()) as usize;
    for index in 0..count {
        let entry = 64 + index * 32;
        let id = u32::from_le_bytes(bytes[entry..entry + 4].try_into().unwrap());
        if id == wanted {
            return u64_at(bytes, entry + 8);
        }
    }
    panic!("missing section {wanted}")
}

#[test]
fn execution_image_outlives_the_raw_encoded_sections() {
    let encoded = encoded_unit_program();
    let verified = load_verified(&encoded).unwrap();
    drop(encoded);

    assert_eq!(verified.entry_function(), Some(0));
    assert_eq!(Vm::new(verified).run(0, vec![]), Ok(Value::Unit));
}

#[test]
fn wire_backed_text_and_blob_constants_execute_after_input_release() {
    let text = "borrowed from the verified wire image".repeat(64);
    let encoded = encoded_constant_program(Constant::Text(text.clone()), TEXT);
    let verified = load_verified(&encoded).unwrap();
    drop(encoded);
    assert_eq!(
        Vm::new(verified).run(0, vec![]),
        Ok(Value::Text(text.into()))
    );

    let bytes = vec![0x5a; 8192];
    let encoded = encoded_constant_program(Constant::Bytes(bytes.clone()), BYTES);
    let verified = load_verified(&encoded).unwrap();
    drop(encoded);
    assert_eq!(
        Vm::new(verified).run(0, vec![]),
        Ok(Value::Bytes(bytes.into()))
    );
}

#[test]
fn wire_backed_abort_message_executes_after_input_release() {
    let message = "wire-backed fatal detail".repeat(128);
    let artifact = Artifact {
        functions: vec![Function {
            name: "aborter".into(),
            flags: 0,
            params: vec![],
            return_type: 1,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT],
            code_start: 0,
            code_len: 1,
            label_slot_count: 0,
        }],
        code: vec![Instruction::Abort {
            message: Some(message.clone()),
        }],
        ..Artifact::default()
    };
    let encoded = with_generated_cleanup_plans(artifact).unwrap().encode();
    let verified = load_verified(&encoded).unwrap();
    drop(encoded);
    assert_eq!(
        Vm::new(verified).run(0, vec![]),
        Err(RuntimeError::Aborted(Some(message)))
    );
}

#[test]
fn compatibility_materialization_preserves_canonical_encoding() {
    let encoded = encoded_unit_program();
    let verified = load_verified(&encoded).unwrap();
    assert_eq!(verified.artifact().encode(), encoded);
}

#[test]
fn hostile_truncations_fail_closed_during_decode() {
    let encoded = encoded_unit_program();
    for end in [0, 1, 7, 63, 64, encoded.len() / 2, encoded.len() - 1] {
        assert!(
            matches!(load_verified(&encoded[..end]), Err(LoadError::Decode(_))),
            "truncation at {end} bytes was accepted"
        );
    }
}

#[test]
fn hostile_function_id_fails_during_verification() {
    let mut encoded = encoded_unit_program();
    encoded[28..32].copy_from_slice(&1_u32.to_le_bytes());
    assert_eq!(
        load_verified(&encoded).unwrap_err(),
        LoadError::Verify(VerifyError::InvalidFunction(1))
    );
}

#[test]
fn malformed_utf8_and_section_ids_fail_during_decode() {
    let mut invalid_utf8 = encoded_unit_program();
    let strings_offset = u64_at(&invalid_utf8, 64 + 8);
    let string_bytes = strings_offset + 16;
    invalid_utf8[string_bytes] = 0xff;
    assert_eq!(
        load_verified(&invalid_utf8).unwrap_err(),
        LoadError::Decode(DecodeError::InvalidUtf8)
    );

    let mut invalid_id = encoded_unit_program();
    invalid_id[64..68].copy_from_slice(&2_u32.to_le_bytes());
    assert!(matches!(
        load_verified(&invalid_id),
        Err(LoadError::Decode(
            DecodeError::DuplicateSection(2) | DecodeError::MissingSection(1)
        ))
    ));
}

#[test]
fn hostile_text_offsets_and_blob_lengths_fail_closed() {
    let mut invalid_text_offset = encoded_unit_program();
    let strings = section_offset(&invalid_text_offset, 1);
    // count, byte length, zero offset, first end offset
    invalid_text_offset[strings + 12..strings + 16].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(matches!(
        load_verified(&invalid_text_offset),
        Err(LoadError::Decode(DecodeError::InvalidTable("strings")))
    ));

    let mut invalid_blob_length = Artifact {
        constants: vec![grandiose_vm::Constant::Bytes(vec![1, 2, 3, 4])],
        ..Artifact::default()
    }
    .encode();
    let constants = section_offset(&invalid_blob_length, 3);
    // One variable record: count + two offsets + eight-byte record header.
    let payload = constants + 4 + 8 + 8;
    invalid_blob_length[payload..payload + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(matches!(
        load_verified(&invalid_blob_length),
        Err(LoadError::Decode(DecodeError::Truncated))
    ));
}
