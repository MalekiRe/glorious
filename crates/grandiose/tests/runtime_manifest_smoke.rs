use grandiose::{
    GenericParameterKind, MachineTypeRole, ManifestMachineType, ManifestPrimitiveLeaf,
    TrustedRuntimeManifest, TrustedTraitManifest, compile_bundle_to_phases_with_manifest,
    compile_source_to_bytecode, compile_source_to_phases,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{I64, Instruction, Primitive, Type, verify};

fn manifest() -> TrustedTraitManifest {
    let runtime = TrustedRuntimeManifest::new(
        vec![ManifestMachineType {
            id: 100,
            display_name: "Raw".into(),
            parameters: vec![GenericParameterKind::Type],
            role: MachineTypeRole::Array,
        }],
        vec![
            ManifestPrimitiveLeaf {
                id: 101,
                display_name: "birth".into(),
                primitive: Primitive::ArrayEmpty,
            },
            ManifestPrimitiveLeaf {
                id: 102,
                display_name: "seal".into(),
                primitive: Primitive::ArrayFinishDrained,
            },
        ],
    )
    .unwrap();
    TrustedTraitManifest::trusted_default().with_runtime(runtime)
}

#[test]
fn arbitrary_bound_names_lower_through_specialized_primitive_leaf_bodies() {
    let standard_library = r#"
        birth<T>() -> Raw<T> { () }
        seal<T>(value: Raw<T>) -> () { () }
        make() -> Raw<i64> { birth() }
        close(value: Raw<i64>) -> () { seal(move value) }
    "#;
    let primary = r#"
        main() -> () {
            let value = make();
            close(move value);
            ()
        }
    "#;
    let bundle = SourceBundle::raw_with_trusted_standard_for_conformance(
        Segment::new("std.glorious", standard_library),
        Segment::new("main.glorious", primary),
        [],
    );
    let phases = compile_bundle_to_phases_with_manifest(&bundle, &manifest()).unwrap();
    verify(phases.artifact.clone()).unwrap();

    assert!(
        phases
            .artifact
            .types
            .iter()
            .any(|ty| matches!(ty.representation(), Type::Array { element } if *element == I64))
    );
    let primitives = phases
        .artifact
        .functions
        .iter()
        .flat_map(|function| {
            let start = function.code_start as usize;
            &phases.artifact.code[start..start + function.code_len as usize]
        })
        .filter_map(|instruction| match instruction {
            Instruction::Primitive { op, .. } => Some(*op),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(primitives.contains(&Primitive::ArrayEmpty));
    assert!(primitives.contains(&Primitive::ArrayFinishDrained));
}

#[test]
fn packaged_array_manifest_and_all_trusted_leaf_signatures_bind_by_default() {
    let first = compile_source_to_phases("packaged-array.glorious", "main() -> () { () }")
        .expect("the embedded layer-one declarations match their distribution manifest");
    let second = compile_source_to_phases("packaged-array.glorious", "main() -> () { () }")
        .expect("the packaged manifest is deterministic");
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    verify(first.artifact).unwrap();
}

#[test]
fn packaged_array_leaf_spelling_does_not_grant_user_primitive_authority() {
    let errors = compile_source_to_bytecode(
        "forged-array-leaf.glorious",
        r#"
            steal() -> Array<i64> { __g1_array_empty() }
            main() -> () { () }
        "#,
    )
    .unwrap_err();
    assert!(errors.iter().any(|error| {
        error.message.contains(
            "manifest-bound primitive leaves may be called only from their trusted standard-library source segment",
        )
    }), "{errors:#?}");
}
