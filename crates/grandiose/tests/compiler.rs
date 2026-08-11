use grandiose::source_bundle::{Segment, SourceBundle};
use grandiose::{
    CompileOptions, OptimizationLevel, compile_bundle_to_bytecode, compile_source_to_bytecode,
    compile_source_to_phases, compile_source_to_phases_with_options,
};
use grandiose_vm::{Artifact, Instruction, Type, Value, Vm, verify};

fn compile_raw_source(
    source_name: &str,
    source: &str,
) -> Result<Artifact, Vec<grandiose::diagnostic::Diagnostic>> {
    compile_bundle_to_bytecode(&SourceBundle::raw_for_conformance(
        Segment::new("empty-std.glorious", ""),
        Segment::new(source_name, source),
        [],
    ))
}

fn function_code<'a>(
    artifact: &'a Artifact,
    function: &grandiose_vm::Function,
) -> &'a [Instruction] {
    &artifact.code[function.code_start as usize..(function.code_start + function.code_len) as usize]
}

fn nominal_type_id(artifact: &Artifact, expected_name: &str) -> u32 {
    let matches = artifact
        .types
        .iter()
        .enumerate()
        .filter_map(|(id, ty)| match ty.representation() {
            Type::Struct { name, .. } | Type::Enum { name, .. } if name == expected_name => {
                Some(id as u32)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        matches.len(),
        1,
        "expected exactly one nominal descriptor named `{expected_name}`, found {matches:?}"
    );
    matches[0]
}

fn user_drop_glue<'a>(artifact: &'a Artifact) -> impl Iterator<Item = &'a grandiose_vm::DropGlue> {
    artifact.drop_glue.iter().filter(|glue| {
        !matches!(
            artifact.types[glue.ty as usize].representation(),
            Type::Struct { name, .. } if name == "ByteBufCheckpoint"
        )
    })
}

fn assert_direct_only_functions(artifact: &Artifact, mut relevant: impl FnMut(&str) -> bool) {
    for function in artifact
        .functions
        .iter()
        .filter(|function| relevant(&function.name))
    {
        assert!(
            !function_code(artifact, function).iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::MakeCallable { .. } | Instruction::CallIndirect { .. }
                )
            }),
            "{} unexpectedly retained a first-class callable operation",
            function.name
        );
    }
    assert!(artifact.types.iter().all(|ty| {
        !matches!(
            ty,
            Type::Callable { identity_name, .. } if identity_name.starts_with("closure:")
        )
    }));
}

#[test]
fn stored_first_class_closure_constructs_and_calls_indirectly() {
    let source = "run()->i64 { let answer = { => 42 }; answer() } main()->{()}";
    let phases = compile_source_to_phases("stored-closure.glorious", source).unwrap();
    assert!(
        phases
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::MakeCallable { .. }))
    );
    assert!(
        phases
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::CallIndirect { .. }))
    );
    let verified = verify(phases.artifact.clone()).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(Vm::new(verified).run(run, vec![]).unwrap(), Value::I64(42));
}

#[test]
fn stored_copy_capture_closure_can_be_invoked_repeatedly() {
    let source =
        "run()->i64 { let value = 21; let twice = { => value }; twice() + twice() } main()->{()}";
    let phases = compile_source_to_phases("stored-copy-closure.glorious", source).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        function_code(&phases.artifact, &phases.artifact.functions[run as usize])
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::CallIndirect { .. }))
            .count(),
        2
    );
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn stored_owned_capture_closure_is_invoked_exactly_once() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        run() -> i64 {
            let ticket = Ticket { value: 42 };
            let consume = { => { let Ticket { value } = move ticket; value } };
            consume()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("stored-owned-closure.glorious", source).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    let run_code = function_code(&phases.artifact, &phases.artifact.functions[run as usize]);
    let indirect = run_code.iter().find_map(|instruction| {
        let Instruction::CallIndirect { receiver_mode, .. } = instruction else {
            return None;
        };
        Some(*receiver_mode)
    });
    if let Some(receiver_mode) = indirect {
        assert_eq!(receiver_mode, 2);
    } else {
        assert!(
            run_code
                .iter()
                .all(|instruction| !matches!(instruction, Instruction::MakeCallable { .. }))
        );
    }
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn returned_closure_value_can_be_stored_and_invoked() {
    let source = r#"
        retain<F>(body: F) -> F where F: Fn<(), Output=i64> { body }
        run() -> i64 {
            let answer = retain({ => 42 });
            answer()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("returned-closure.glorious", source).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn returned_closure_identity_uses_the_exact_result_binder() {
    let source = r#"
        choose<F, G>(left: F, right: G) -> G
            where F: Fn<(), Output=i64>, G: Fn<(), Output=i64> { right }
        run() -> i64 {
            let first = 1;
            let second = 42;
            let answer = choose({ => first }, { => second });
            answer()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("returned-closure-identity.glorious", source).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn closure_value_round_trips_through_a_monomorphic_tuple() {
    let source = r#"
        run() -> i64 {
            let answer = { => 42 };
            let stored = (answer,);
            let (restored,) = stored;
            restored()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("tuple-stored-closure.glorious", source).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn closure_value_round_trips_through_a_mixed_tuple() {
    let source = r#"
        run() -> i64 {
            let base = 40;
            let answer = { => 2 };
            let stored = (base, answer);
            let (value, restored) = stored;
            value + restored()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("mixed-tuple-stored-closure.glorious", source).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn tuple_extraction_preserves_distinct_same_shape_closure_identities() {
    let source = r#"
        run() -> i64 {
            let first_value = 1;
            let second_value = 42;
            let first = { => first_value };
            let second = { => second_value };
            let stored = (first, second);
            let (_, answer) = stored;
            answer()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("tuple-closure-identities.glorious", source).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn stored_outward_effectful_closure_runs_under_a_handler() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        run() -> i64 {
            let answer = { => perform Ask::ask() };
            handle { answer() } {
                Ask::ask() with k => resume(k, 42)
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("stored-effectful-closure.glorious", source).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn explicit_reference_regions_validate_outlives_escape_and_canonical_order() {
    let positive = r#"
        first<'a, 'b>(left: &'a i64, right: &'b i64) -> &'a i64 { left }
        shorten<'a, 'b, 'c>(value: &'a i64) -> &'c i64
            where 'a: 'b, 'b: 'c { value }
        main() -> { () }
    "#;
    let reordered = r#"
        first<'a, 'b>(left: &'a i64, right: &'b i64) -> &'a i64 { left }
        shorten<'a, 'b, 'c>(value: &'a i64) -> &'c i64
            where 'b: 'c, 'a: 'b { value }
        main() -> { () }
    "#;
    let first = compile_source_to_phases("regions.glorious", positive).unwrap();
    let second = compile_source_to_phases("regions-reordered.glorious", reordered).unwrap();
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    let core = first.core.canonical_text();
    assert!(core.contains("region r"), "{core}");
    assert!(core.contains("outlives"), "{core}");

    let missing = r#"
        bad<'a, 'b>(value: &'a i64) -> &'b i64 { value }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("missing-outlives.glorious", missing).unwrap_err();
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("does not outlive the callable's declared result lifetime")),
        "{errors:#?}"
    );

    let wrong_parameter = r#"
        bad<'a, 'b>(left: &'a i64, right: &'b i64) -> &'a i64 { right }
        main() -> { () }
    "#;
    assert!(compile_source_to_bytecode("wrong-region.glorious", wrong_parameter).is_err());

    let local_escape = r#"
        bad<'a>() -> &'a i64 { let local = 1; &local }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("region-local-escape.glorious", local_escape).unwrap_err();
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("reference to a local place cannot escape")),
        "{errors:#?}"
    );
}

#[test]
fn monomorphic_drop_hooks_emit_verify_roundtrip_and_execute_before_children() {
    let source = r#"
        struct Child { value: i64 }
        struct Parent { child: Child, marker: i64 }
        struct Owner { value: &mut i64 }
        struct Residual { owner: Owner, marker: i64 }
        struct PlainResidual { owner: Owner, marker: i64 }
        enum EmptyChoice { Empty }
        observe(value: i64) -> { () }
        impl Drop for Child {
            drop(&mut self) -> { self.value + 9223372036854775807; () }
        }
        impl Drop for Parent {
            drop(&mut self) -> { observe(self.marker); 1 / 0; () }
        }
        impl Drop for Residual { drop(&mut self) -> { () } }
        impl Drop for EmptyChoice { drop(&mut self) -> { () } }
        inspect_residual(value: Residual) -> i64 { value.marker }
        take_plain(value: PlainResidual) -> i64 {
            let owner = value.owner;
            value.marker
        }
        discard_choice(value: EmptyChoice) -> { () }
        main() -> {
            let value = Parent { child: Child { value: 1 }, marker: 2 };
            ()
        }
    "#;
    let first = compile_source_to_phases("drop.glorious", source).unwrap();
    let second = compile_source_to_phases("drop.glorious", source).unwrap();
    let verified = verify(first.artifact.clone()).unwrap();
    assert_eq!(user_drop_glue(&first.artifact).count(), 4);
    assert!(
        first
            .artifact
            .drop_glue
            .windows(2)
            .all(|pair| pair[0].ty < pair[1].ty)
    );
    for glue in &first.artifact.drop_glue {
        let hook = &first.artifact.functions[glue.function as usize];
        assert_eq!(
            hook.flags & grandiose_vm::DROP_HOOK,
            grandiose_vm::DROP_HOOK
        );
        assert_eq!(hook.params.len(), 1);
        assert_eq!(hook.return_type, grandiose_vm::UNIT);
    }
    let bytes = first.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(bytes, second.artifact.encode());
    assert!(first.core.canonical_text().contains("$drop$Parent"));
    assert!(first.mir.canonical_text().contains("ProjectCopy"));
    assert!(first.mir.canonical_text().contains("ProjectMove"));
    let error = Vm::new(verified)
        .run(first.artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");
}

#[test]
fn custom_drop_preserves_structural_copy_for_owner_and_containers() {
    let source = r#"
        struct CopyDrop { marker: i64 }
        struct Holder { value: CopyDrop }
        impl Drop for CopyDrop { drop(&mut self) -> { self.marker; () } }
        duplicate(value: CopyDrop) -> i64 {
            let copy = value;
            copy.marker + value.marker
        }
        holder(value: Holder) -> Holder { value }
        main() -> {
            let value = CopyDrop { marker: 1 };
            duplicate(value);
            ()
        }
    "#;
    let phases = compile_source_to_phases("copy-drop.glorious", source).unwrap();
    let artifact = &phases.artifact;
    let copy_drop = artifact
        .types
        .iter()
        .position(|ty| matches!(ty.representation(), Type::Struct { name, copy: true, .. } if name == "CopyDrop"))
        .unwrap() as u32;
    assert!(
        artifact
            .types
            .iter()
            .any(|ty| matches!(ty.representation(), Type::Struct { name, copy: true, .. } if name == "Holder"))
    );
    assert_eq!(user_drop_glue(artifact).count(), 1);
    assert!(user_drop_glue(artifact).any(|glue| glue.ty == copy_drop));
    assert!(artifact.types[copy_drop as usize].claimed_zero_use_allowed());
    let mut typed_copies = 0;
    let mut typed_drops = 0;
    for function in &artifact.functions {
        let start = function.code_start as usize;
        let end = start + function.code_len as usize;
        for instruction in &artifact.code[start..end] {
            match instruction {
                Instruction::Copy { src, .. }
                    if function.register_types[*src as usize] == copy_drop =>
                {
                    typed_copies += 1;
                }
                Instruction::Drop { register }
                    if function.register_types[*register as usize] == copy_drop =>
                {
                    typed_drops += 1;
                }
                _ => {}
            }
        }
    }
    assert!(typed_copies >= 2);
    assert!(typed_drops >= 3);

    let bytes = artifact.encode();
    let decoded = Artifact::decode(&bytes).unwrap();
    assert!(matches!(
        decoded.types[copy_drop as usize].representation(),
        Type::Struct { copy: true, .. }
    ));
    assert!(user_drop_glue(&decoded).any(|glue| glue.ty == copy_drop));
    assert_eq!(decoded.encode(), bytes);
    assert_eq!(
        Vm::new(verify(artifact.clone()).unwrap())
            .run(artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );

    let reordered = r#"
        main() -> {
            let value = CopyDrop { marker: 1 };
            duplicate(value);
            ()
        }
        holder(value: Holder) -> Holder { value }
        duplicate(value: CopyDrop) -> i64 {
            let copy = value;
            copy.marker + value.marker
        }
        impl Drop for CopyDrop { drop(&mut self) -> { self.marker; () } }
        struct Holder { value: CopyDrop }
        struct CopyDrop { marker: i64 }
    "#;
    assert_eq!(
        compile_source_to_bytecode("copy-drop-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn principal_use_affine_narrowing_propagates_and_roundtrips() {
    let source = r#"
        struct Ticket { value: i64 }
        struct Holder { ticket: Ticket }
        impl Use<[0,1]> for Ticket {}
        forward(value: Ticket) -> Ticket { value }
        hold(value: Holder) -> Holder { value }
        main() -> { let value = Ticket { value: 1 }; () }
    "#;
    let phases = compile_source_to_phases("principal-use.glorious", source).unwrap();
    let artifact = &phases.artifact;
    for name in ["Ticket", "Holder"] {
        let ty = artifact
            .types
            .iter()
            .find(|ty| matches!(ty.representation(), Type::Struct { name: found, copy: true, .. } if found == name))
            .unwrap();
        assert!(!ty.claimed_duplicable());
        assert!(ty.claimed_zero_use_allowed());
        assert!(matches!(ty, Type::Restricted { .. }));
    }
    assert!(phases.core.canonical_text().contains("local l0 copy=false"));
    assert!(phases.mir.canonical_text().contains("Move"));
    let bytes = artifact.encode();
    let decoded = Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);
    assert_eq!(
        Vm::new(verify(decoded).unwrap())
            .run(artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );

    let reordered = r#"
        main() -> { let value = Ticket { value: 1 }; () }
        hold(value: Holder) -> Holder { value }
        forward(value: Ticket) -> Ticket { value }
        impl Use<[0,1]> for Ticket {}
        struct Holder { ticket: Ticket }
        struct Ticket { value: i64 }
    "#;
    assert_eq!(
        compile_source_to_bytecode("principal-use-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn principal_use_ground_generic_narrowing_is_exact() {
    let source = r#"
        struct Box<T> { value: T }
        impl Use<[0,1]> for Box<i64> {}
        forward(value: Box<i64>) -> Box<i64> { value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("ground-use.glorious", source).unwrap();
    let ty = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "forward")
        .unwrap()
        .params[0];
    assert!(!phases.artifact.types[ty as usize].claimed_duplicable());
    assert!(phases.artifact.types[ty as usize].claimed_zero_use_allowed());
    verify(phases.artifact).unwrap();
}

#[test]
fn principal_use_rejects_widening_duplicates_and_invalid_forms() {
    let cases = [
        "struct Owner { value: &mut i64 } impl Use<[0,infinity]> for Owner {} main() -> { () }",
        "struct Item { value: i64 } impl Use<[0,1]> for Item {} impl Use<[0,0]> for Item {} main() -> { () }",
        "struct Item { value: i64 } impl Use<[1,0]> for Item {} main() -> { () }",
        "struct Item<T> { value: T } impl<T> Use<[0,1]> for Item<T> {} main() -> { () }",
        "impl Use<[0,1]> for i64 {} main() -> { () }",
        "struct Item { value: i64 } impl Use<[0,1]> for &Item {} main() -> { () }",
        "struct Item { value: i64 } impl Use<[0,1]> for (Item,) {} main() -> { () }",
        "struct Item { value: i64 } type Alias = Item; impl Use<[0,1]> for Alias {} main() -> { () }",
        "struct Item { value: i64 } impl Use<[0,1]> for Item { method } main() -> { () }",
    ];
    for source in cases {
        let errors = compile_source_to_bytecode("invalid-use.glorious", source).unwrap_err();
        assert!(errors.iter().all(|error| error.span.is_some()));
        assert!(errors.iter().all(|error| error.code.is_some()));
    }

    let repeated = r#"
        struct Ticket { value: i64 }
        impl Use<[0,1]> for Ticket {}
        bad(value: Ticket) -> i64 { let first = value; let second = value; 0 }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("repeated-affine-use.glorious", repeated).unwrap_err();
    assert!(errors[0].message.contains("already moved"));
}

#[test]
fn principal_use_and_drop_remain_orthogonal() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[0,1]> for Ticket {}
        impl Drop for Ticket { drop(&mut self) -> { self.value; () } }
        forward(value: Ticket) -> Ticket { value }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("use-drop.glorious", source).unwrap();
    assert_eq!(user_drop_glue(&artifact).count(), 1);
    let ty = user_drop_glue(&artifact).next().unwrap().ty;
    assert!(!artifact.types[ty as usize].claimed_duplicable());
    assert!(artifact.types[ty as usize].claimed_zero_use_allowed());
    verify(artifact).unwrap();

    let erased = compile_source_to_bytecode(
        "erased-drop.glorious",
        "struct Erased { value: i64 } impl Use<[0,0]> for Erased {} impl Drop for Erased { drop(&mut self) -> { () } } main() -> { () }",
    )
    .unwrap();
    assert_eq!(user_drop_glue(&erased).count(), 1);
    let erased_ty = user_drop_glue(&erased).next().unwrap().ty;
    assert!(erased.types[erased_ty as usize].claimed_zero_use_allowed());
    verify(erased).unwrap();

    for (name, interval) in [
        ("linear-drop.glorious", "[1,1]"),
        ("relevant-drop.glorious", "[1,infinity]"),
    ] {
        let source = format!(
            "struct MustMove {{ value: i64 }} impl Use<{interval}> for MustMove {{}} impl Drop for MustMove {{ drop(&mut self) -> {{ () }} }} main() -> {{ () }}"
        );
        let errors = compile_source_to_bytecode(name, &source).unwrap_err();
        assert!(errors.iter().any(|error| {
            error.message.contains(
                "custom Drop requires its target principal Use interval to support `[0,0]`",
            )
        }));
    }
}

#[test]
fn actual_use_accepts_arbitrary_bounded_intervals_and_lowers_flags() {
    let source = r#"
        struct Erased { value: i64 }
        struct AtMostTwo { value: i64 }
        struct OneOrTwo { value: i64 }
        struct ExactlyTwo { value: i64 }
        struct AtLeastTwo { value: i64 }
        struct Pair02 { left: AtMostTwo, right: AtMostTwo }
        struct Pair12 { left: OneOrTwo, right: OneOrTwo }
        enum Envelope12 { Empty, Full(OneOrTwo) }
        impl Use<[0,0]> for Erased {}
        impl Use<[0,2]> for AtMostTwo {}
        impl Use<[1,2]> for OneOrTwo {}
        impl Use<[2,2]> for ExactlyTwo {}
        impl Use<[2,infinity]> for AtLeastTwo {}
        zero(value: Erased) -> { () }
        twice02(value: AtMostTwo) -> Pair02 { Pair02 { left: value, right: value } }
        twice12(value: OneOrTwo) -> Pair12 { Pair12 { left: value, right: move value } }
        wrap12(value: OneOrTwo) -> Envelope12 { Envelope12::Full(move value) }
        nested(value: OneOrTwo) -> (Pair12,) {
            (Pair12 { left: value, right: move value },)
        }
        main() -> { let erased = Erased { value: 0 }; () }
    "#;
    let phases = compile_source_to_phases("bounded-use.glorious", source).unwrap();
    let claims = |name: &str| {
        let ty = phases
            .artifact
            .types
            .iter()
            .find(|ty| matches!(ty.representation(), Type::Struct { name: found, .. } if found == name))
            .unwrap();
        (ty.claimed_duplicable(), ty.claimed_zero_use_allowed())
    };
    assert_eq!(claims("Erased"), (false, true));
    assert_eq!(claims("AtMostTwo"), (true, true));
    assert_eq!(claims("OneOrTwo"), (true, false));
    assert_eq!(claims("ExactlyTwo"), (true, false));
    assert_eq!(claims("AtLeastTwo"), (true, false));
    assert_eq!(claims("Pair02"), (true, true));
    assert_eq!(claims("Pair12"), (true, false));
    let envelope = phases
        .artifact
        .types
        .iter()
        .find(|ty| matches!(ty.representation(), Type::Enum { name, .. } if name == "Envelope12"))
        .unwrap();
    assert!(envelope.claimed_duplicable());
    assert!(!envelope.claimed_zero_use_allowed());
    assert!(phases.core.canonical_text().contains("local l0 copy=true"));
    assert!(phases.mir.canonical_text().contains("Copy"));
    let bytes = phases.artifact.encode();
    let decoded = Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);
    assert_eq!(
        Vm::new(verify(decoded).unwrap())
            .run(phases.artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );

    let reordered = r#"
        main() -> { let erased = Erased { value: 0 }; () }
        nested(value: OneOrTwo) -> (Pair12,) { (Pair12 { left: value, right: move value },) }
        wrap12(value: OneOrTwo) -> Envelope12 { Envelope12::Full(move value) }
        twice12(value: OneOrTwo) -> Pair12 { Pair12 { left: value, right: move value } }
        twice02(value: AtMostTwo) -> Pair02 { Pair02 { left: value, right: value } }
        zero(value: Erased) -> { () }
        impl Use<[2,infinity]> for AtLeastTwo {}
        impl Use<[2,2]> for ExactlyTwo {}
        impl Use<[1,2]> for OneOrTwo {}
        impl Use<[0,2]> for AtMostTwo {}
        impl Use<[0,0]> for Erased {}
        enum Envelope12 { Empty, Full(OneOrTwo) }
        struct Pair12 { left: OneOrTwo, right: OneOrTwo }
        struct Pair02 { left: AtMostTwo, right: AtMostTwo }
        struct AtLeastTwo { value: i64 }
        struct ExactlyTwo { value: i64 }
        struct OneOrTwo { value: i64 }
        struct AtMostTwo { value: i64 }
        struct Erased { value: i64 }
    "#;
    assert_eq!(
        compile_source_to_bytecode("bounded-use-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn actual_use_counts_copy_destinations_temporaries_and_projection_boundaries() {
    let positive = r#"
        struct Token { value: i64 }
        struct Pair { left: Token, right: Token }
        struct Linear { value: &mut i64 }
        impl Use<[1,2]> for Token {}
        impl Use<[1,1]> for Linear {}
        make() -> Token { Token { value: 1 } }
        copied(value: Token) -> Token { move value }
        both(value: Token) -> Pair { Pair { left: value, right: move value } }
        inspect_then_use(value: Token) -> Token { value.value; move value }
        borrow_then_use(value: Token) -> Token { &value; move value }
        nested_tail(value: Token) -> Token { { { move value } } }
        inline() -> Token { copied(Token { value: 2 }) }
        call_bound() -> Token { let value = make(); move value }
        transfer_move(value: Linear) -> Linear { let owner = value; owner }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("actual-use-boundaries.glorious", positive).unwrap();
    verify(artifact).unwrap();

    let cases = [
        "struct Token { value: i64 } impl Use<[1,infinity]> for Token {} bad(value: Token) -> Token { let copy = value; value } main() -> { () }",
        "struct Token { value: i64 } impl Use<[1,infinity]> for Token {} bad() -> { Token { value: 1 }; () } main() -> { () }",
        "struct Token { value: i64 } impl Use<[1,infinity]> for Token {} make() -> Token { Token { value: 1 } } bad() -> i64 { make().value } main() -> { () }",
        "struct Token { value: i64 } impl Use<[1,infinity]> for Token {} bad() -> i64 { Token { value: 1 }.value } main() -> { () }",
        "struct Erased { value: i64 } impl Use<[0,0]> for Erased {} bad(value: Erased) -> Erased { value } main() -> { () }",
        "struct Erased { value: &mut i64 } struct Outer { child: Erased } impl Use<[0,0]> for Erased {} bad(value: Outer) -> Erased { value.child } main() -> { () }",
        "struct UpToTwo { value: i64 } struct Triple { a: UpToTwo, b: UpToTwo, c: UpToTwo } impl Use<[0,2]> for UpToTwo {} bad(value: UpToTwo) -> Triple { Triple { a: value, b: value, c: value } } main() -> { () }",
        "struct OneOrTwo { value: i64 } impl Use<[1,2]> for OneOrTwo {} bad(value: OneOrTwo) -> { () } main() -> { () }",
        "struct ExactlyTwo { value: i64 } impl Use<[2,2]> for ExactlyTwo {} bad() -> ExactlyTwo { ExactlyTwo { value: 1 } } main() -> { () }",
        "struct AtLeastTwo { value: i64 } impl Use<[2,infinity]> for AtLeastTwo {} bad() -> AtLeastTwo { AtLeastTwo { value: 1 } } main() -> { () }",
    ];
    for source in cases {
        let errors = compile_source_to_bytecode("invalid-actual-use.glorious", source).unwrap_err();
        assert!(errors.iter().all(|error| error.span.is_some()));
        assert!(errors.iter().all(|error| error.code.is_some()));
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("actual Use count")),
            "expected count diagnostic, got {errors:#?}"
        );
    }

    let moved_then_discarded = "struct Linear { value: i64 } impl Use<[1,1]> for Linear {} bad(value: Linear) -> { let owner = value; owner; () } main() -> { () }";
    let errors = compile_source_to_bytecode("moved-then-discarded.glorious", moved_then_discarded)
        .unwrap_err();
    assert!(errors.iter().any(|error| {
        error
            .message
            .contains("must-move value cannot be discarded after a whole-value move")
            && error.span.is_some()
            && error.code.as_deref() == Some("G1BC002")
    }));

    let involved_effect = "effect Stop { stop() -> ! } struct Bounded { value: i64 } impl Use<[0,2]> for Bounded {} bad(value: Bounded) -> { handle perform Stop::stop() { Stop::stop() => () } } main() -> { () }";
    verify(
        compile_source_to_bytecode("involved-bounded-effect.glorious", involved_effect).unwrap(),
    )
    .unwrap();

    let bounded_global = "struct Bounded { value: i64 } impl Use<[0,2]> for Bounded {} let cached = Bounded { value: 1 }; main() -> { () }";
    let errors = compile_source_to_bytecode("bounded-global.glorious", bounded_global).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("restricted-use global")),
        "unexpected bounded-global diagnostics: {errors:#?}"
    );

    let unrelated_effect = r#"
        effect Stop { stop() -> ! }
        struct Bounded { value: i64 }
        impl Use<[0,2]> for Bounded {}
        run() -> { handle perform Stop::stop() { Stop::stop() => () } }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("unrelated-bounded-effect.glorious", unrelated_effect).unwrap();
    verify(artifact).unwrap();
}

#[test]
fn explicit_and_inferred_final_moves_transfer_duplicable_relevant_owners() {
    let source = r#"
        struct Relevant { value: i64 }
        impl Use<[1,infinity]> for Relevant {}
        forward(value: Relevant) -> Relevant { move value }
        copy_then_move(value: Relevant) -> (Relevant, Relevant) { (value, move value) }
        through_call(value: Relevant) -> Relevant { forward(move value) }
        through_let(value: Relevant) -> Relevant { let owner = move value; move owner }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("explicit-move.glorious", source).unwrap();
    verify(phases.artifact).unwrap();
    assert!(phases.core.canonical_text().contains("move l0"));
    assert!(phases.mir.canonical_text().contains("Copy"));
    assert!(phases.mir.canonical_text().contains("Move"));

    let copies_only = r#"
        struct Relevant { value: i64 }
        impl Use<[1,infinity]> for Relevant {}
        bad(value: Relevant) -> (Relevant, Relevant) { (value, value) }
        main() -> { () }
    "#;
    let inferred = compile_source_to_phases("copies-only.glorious", copies_only).unwrap();
    assert!(inferred.mir.canonical_text().contains("Copy"));
    assert!(inferred.mir.canonical_text().contains("Move"));

    let live_local = r#"
        struct Relevant { value: i64 }
        impl Use<[1,infinity]> for Relevant {}
        make() -> Relevant { Relevant { value: 1 } }
        bad() -> Relevant { let original = make(); let copy = original; move copy }
        main() -> { () }
    "#;
    compile_source_to_bytecode("live-copy-local.glorious", live_local).unwrap();
}

#[test]
fn bounded_use_drop_compatibility_and_cleanup_are_checked_by_interval() {
    let source = r#"
        struct OptionalDrop { value: i64 }
        impl Use<[0,2]> for OptionalDrop {}
        impl Drop for OptionalDrop { drop(&mut self) -> { self.value; () } }
        unused() -> { let value = OptionalDrop { value: 1 }; () }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("bounded-drop.glorious", source).unwrap();
    let ty = artifact
        .drop_glue
        .iter()
        .find_map(|glue| {
            matches!(
                artifact.types[glue.ty as usize].representation(),
                Type::Struct { name, .. } if name == "OptionalDrop"
            )
            .then_some(glue.ty)
        })
        .expect("OptionalDrop has custom drop glue");
    assert!(artifact.types[ty as usize].claimed_duplicable());
    assert!(artifact.types[ty as usize].claimed_zero_use_allowed());
    verify(artifact).unwrap();

    let errors = compile_source_to_bytecode(
        "incompatible-bounded-drop.glorious",
        "struct Twice { value: i64 } impl Use<[2,infinity]> for Twice {} impl Drop for Twice { drop(&mut self) -> { () } } main() -> { () }",
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("support `[0,0]`"))
    );
}

#[test]
fn conditional_exact_use_selects_marker_proofs_and_is_canonical() {
    let source = r#"
        trait Marker {}
        struct Wrap<T> { value: T }
        struct Ground<T> { marker: i64 }
        struct Yes { value: i64 }
        struct No { value: i64 }
        impl Marker for i64 {}
        impl<T> Marker for Wrap<T> where T: Marker {}
        impl Use<[0,1]> for Yes where Wrap<i64>: Marker {}
        impl Use<[0,1]> for No where Wrap<Text>: Marker {}
        impl Use<[0,1]> for Ground<i64> where Wrap<i64>: Marker {}
        impl Use<[0,1]> for Ground<Text> where Wrap<Text>: Marker {}
        yes(value: Yes) -> Yes { value }
        no(value: No) -> No { value }
        ground_yes(value: Ground<i64>) -> Ground<i64> { value }
        ground_no(value: Ground<Text>) -> Ground<Text> { value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("conditional-exact-use.glorious", source).unwrap();
    let yes = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "yes")
        .unwrap()
        .params[0];
    let no = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "no")
        .unwrap()
        .params[0];
    assert!(!phases.artifact.types[yes as usize].claimed_duplicable());
    assert!(phases.artifact.types[yes as usize].claimed_zero_use_allowed());
    assert!(phases.artifact.types[no as usize].claimed_duplicable());
    assert!(phases.artifact.types[no as usize].claimed_zero_use_allowed());
    let ground_yes = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "ground_yes")
        .unwrap()
        .params[0];
    let ground_no = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "ground_no")
        .unwrap()
        .params[0];
    assert!(!phases.artifact.types[ground_yes as usize].claimed_duplicable());
    assert!(phases.artifact.types[ground_no as usize].claimed_duplicable());
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(phases.artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );

    let reordered = r#"
        main() -> { () }
        no(value: No) -> No { value }
        yes(value: Yes) -> Yes { value }
        ground_no(value: Ground<Text>) -> Ground<Text> { value }
        ground_yes(value: Ground<i64>) -> Ground<i64> { value }
        impl Use<[0,1]> for Ground<Text> where Wrap<Text>: Marker {}
        impl Use<[0,1]> for Ground<i64> where Wrap<i64>: Marker {}
        impl Use<[0,1]> for No where Wrap<Text>: Marker {}
        impl Use<[0,1]> for Yes where Wrap<i64>: Marker {}
        impl<T> Marker for Wrap<T> where T: Marker {}
        impl Marker for i64 {}
        struct No { value: i64 }
        struct Yes { value: i64 }
        struct Ground<T> { marker: i64 }
        struct Wrap<T> { value: T }
        trait Marker {}
    "#;
    assert_eq!(
        compile_source_to_bytecode("conditional-exact-use-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );

    let monomorphic_only = r#"
        trait Marker {}
        struct Ticket { value: i64 }
        impl Marker for i64 {}
        impl Use<[0,1]> for Ticket where i64: Marker {}
        forward(value: Ticket) -> Ticket { value }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("monomorphic-conditional-use.glorious", monomorphic_only)
            .unwrap();
    let ticket = artifact
        .functions
        .iter()
        .find(|function| function.name == "forward")
        .unwrap()
        .params[0];
    assert!(!artifact.types[ticket as usize].claimed_duplicable());
}

#[test]
fn conditional_use_reports_ambiguous_cycles_and_solver_overflow() {
    let cyclic = r#"
        trait Marker {}
        struct Loop<T> { value: T }
        struct Ticket { value: i64 }
        impl<T> Marker for Loop<T> where Loop<T>: Marker {}
        impl Use<[0,1]> for Ticket where Loop<i64>: Marker {}
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("cyclic-conditional-use.glorious", cyclic).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.message
            == "recursive implementation where-goal for `Marker` does not strictly decrease the type-constructor measure"
            && error.code.as_deref() == Some("G1TR001")
            && error.span.is_some()
    }));

    let mut subject = "i64".to_owned();
    for _ in 0..=128 {
        subject = format!("Wrap<{subject}>");
    }
    let overflow = format!(
        "trait Marker {{}} struct Wrap<T> {{ value: T }} struct Ticket {{ value: i64 }} \
         impl Marker for i64 {{}} impl<T> Marker for Wrap<T> where T: Marker {{}} \
         impl Use<[0,1]> for Ticket where {subject}: Marker {{}} main() -> {{ () }}"
    );
    let errors = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("solver-boundary-use".into())
            .stack_size(16 * 1024 * 1024)
            .spawn_scoped(scope, || {
                compile_source_to_bytecode("overflow-conditional-use.glorious", &overflow)
            })
            .unwrap()
            .join()
            .unwrap()
    })
    .unwrap_err();
    let limit = errors
        .iter()
        .find(|error| error.message.contains("exceeded the solver limit"))
        .unwrap();
    assert_eq!(limit.code.as_deref(), Some("G1BC002"));
    assert!(limit.span.is_some());
    assert!(
        limit
            .message
            .contains("nested solver frames limit 128 exceeded; trace:"),
        "{}",
        limit.message
    );
    let overflow_reordered = format!(
        "main() -> {{ () }} impl Use<[0,1]> for Ticket where {subject}: Marker {{}} \
         impl<T> Marker for Wrap<T> where T: Marker {{}} impl Marker for i64 {{}} \
         struct Ticket {{ value: i64 }} struct Wrap<T> {{ value: T }} trait Marker {{}}"
    );
    let reordered_errors = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("solver-boundary-use-reordered".into())
            .stack_size(16 * 1024 * 1024)
            .spawn_scoped(scope, || {
                compile_source_to_bytecode(
                    "overflow-conditional-use-reordered.glorious",
                    &overflow_reordered,
                )
            })
            .unwrap()
            .join()
            .unwrap()
    })
    .unwrap_err();
    assert_eq!(
        reordered_errors
            .iter()
            .find(|error| error.message.contains("exceeded the solver limit"))
            .unwrap()
            .message,
        limit.message
    );
}

#[test]
fn non_decreasing_recursive_marker_impls_have_stable_structured_diagnostics() {
    let direct = r#"
        trait Marker {}
        struct Wrap<T> { value: T }
        impl<T> Marker for Wrap<T> where Wrap<T>: Marker {}
        main() -> { () }
    "#;
    let direct_reordered = r#"
        main() -> { () }
        impl<T> Marker for Wrap<T> where Wrap<T>: Marker {}
        struct Wrap<T> { value: T }
        trait Marker {}
    "#;
    let mutual = r#"
        trait Left {}
        trait Right {}
        struct Wrap<T> { value: T }
        impl<T> Left for Wrap<T> where Wrap<T>: Right {}
        impl<T> Right for Wrap<T> where Wrap<T>: Left {}
        main() -> { () }
    "#;
    let mutual_reordered = r#"
        main() -> { () }
        impl<T> Right for Wrap<T> where Wrap<T>: Left {}
        impl<T> Left for Wrap<T> where Wrap<T>: Right {}
        struct Wrap<T> { value: T }
        trait Right {}
        trait Left {}
    "#;

    let signature = |source: &str| {
        let mut errors = compile_source_to_bytecode("recursive-impl.glorious", source)
            .unwrap_err()
            .into_iter()
            .map(|error| {
                let span = error
                    .span
                    .expect("recursive impl diagnostic must have a span");
                (
                    error.code,
                    error.title,
                    error.message,
                    source[span.range()].to_owned(),
                )
            })
            .collect::<Vec<_>>();
        errors.sort();
        errors
    };
    let direct_errors = signature(direct);
    assert_eq!(direct_errors, signature(direct_reordered));
    assert_eq!(
        direct_errors,
        vec![(
            Some("G1TR001".into()),
            "marker trait error".into(),
            "recursive implementation where-goal for `Marker` does not strictly decrease the type-constructor measure".into(),
            "impl<T> Marker for Wrap<T> where Wrap<T>: Marker {}".into(),
        )]
    );

    let mutual_errors = signature(mutual);
    assert_eq!(mutual_errors, signature(mutual_reordered));
    assert_eq!(mutual_errors.len(), 2);
    assert_eq!(
        mutual_errors
            .iter()
            .map(|(_, _, message, _)| message.as_str())
            .collect::<Vec<_>>(),
        vec![
            "recursive implementation where-goal for `Left` does not strictly decrease the type-constructor measure",
            "recursive implementation where-goal for `Right` does not strictly decrease the type-constructor measure",
        ]
    );
    assert!(mutual_errors.iter().all(|(code, title, _, span)| {
        code.as_deref() == Some("G1TR001")
            && title == "marker trait error"
            && span.starts_with("impl<T>")
    }));
}

#[test]
fn decreasing_marker_recursion_composes_with_gats_polarity_and_param_envs() {
    let source = r#"
        trait Family { type Member<T>; }
        trait Positive {}
        trait Negative {}
        struct Wrap<T> { value: T }
        struct Ticket<T> { marker: i64 }
        impl Family for i64 { type Member<T> = T; }
        impl Positive for i64 {}
        impl<T> Positive for Wrap<T> where T: Positive {}
        impl !Negative for i64 {}
        impl<T> !Negative for Wrap<T> where T: !Negative {}
        impl<T> Use<[0,1]> for Ticket<T>
            where T: Positive,
                  T: !Negative,
                  i64: Family<Member<T> = T> {}
        pass<T>(value:T)->T
            where T: Positive,
                  T: !Negative,
                  i64: Family<Member<T> = T> { value }
        answer(value:Wrap<Wrap<i64>>)->Wrap<Wrap<i64>> { pass(value) }
        ticket(value:Ticket<Wrap<Wrap<i64>>>)->Ticket<Wrap<Wrap<i64>>> { value }
        main()->{ () }
    "#;
    let phases = compile_source_to_phases("decreasing-recursion.glorious", source).unwrap();
    let repeated = compile_source_to_phases("decreasing-recursion.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(phases.artifact.encode(), repeated.artifact.encode());
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$pass#"))
            .count(),
        1
    );
    let ticket = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "ticket")
        .unwrap()
        .params[0];
    assert!(!phases.artifact.types[ticket as usize].claimed_duplicable());
    assert!(phases.artifact.types[ticket as usize].claimed_zero_use_allowed());
    verify(phases.artifact).unwrap();
}

#[test]
fn projection_solver_limit_is_exact_structured_and_source_order_independent() {
    let compile = |name: &str, source: &str| {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name("projection-boundary".into())
                .stack_size(32 * 1024 * 1024)
                .spawn_scoped(scope, || compile_source_to_bytecode(name, source))
                .unwrap()
                .join()
                .unwrap()
        })
    };
    let nested_projection = |depth: usize| {
        (0..depth).fold("i64".to_owned(), |inner, _| {
            format!("<Wrap<{inner}> as Family>::Member")
        })
    };
    let program = |depth: usize, reordered: bool| {
        let projected = nested_projection(depth);
        if reordered {
            format!(
                "main()->{{()}} take_projected(value:{projected})->i64{{value}} \
                 impl<T> Family for Wrap<T>{{type Member=T;}} \
                 struct Wrap<T>{{value:T}} trait Family{{type Member;}}"
            )
        } else {
            format!(
                "trait Family{{type Member;}} struct Wrap<T>{{value:T}} \
                 impl<T> Family for Wrap<T>{{type Member=T;}} \
                 take_projected(value:{projected})->i64{{value}} main()->{{()}}"
            )
        }
    };

    let at_limit = program(256, false);
    let reordered_at_limit = program(256, true);
    let bytes = compile("projection-limit.glorious", &at_limit)
        .unwrap()
        .encode();
    assert_eq!(
        compile("projection-limit-reordered.glorious", &reordered_at_limit)
            .unwrap()
            .encode(),
        bytes
    );

    let above_limit = program(257, false);
    let reordered_above_limit = program(257, true);
    let messages = |source: &str| {
        let mut diagnostics = compile("projection-overflow.glorious", source)
            .unwrap_err()
            .into_iter()
            .map(|error| {
                assert_eq!(error.code.as_deref(), Some("G1BC002"));
                assert!(error.span.is_some());
                error.message
            })
            .collect::<Vec<_>>();
        diagnostics.sort();
        diagnostics
    };
    let overflow = messages(&above_limit);
    assert_eq!(overflow, messages(&reordered_above_limit));
    assert_eq!(overflow.len(), 1);
    assert!(
        overflow[0].contains("associated type projection normalization overflow")
            && overflow[0].contains("projection normalization steps limit 256 exceeded"),
        "{}",
        overflow[0]
    );
}

#[test]
fn gat_cycle_reports_the_shortest_deterministic_repeating_goal_trace() {
    let source = r#"
        trait Family { type Member<T>; }
        struct Wrap<T> { value: T }
        impl Family for i64 { type Member<T> = T; }
        impl<T> Family for Wrap<T> where T: Family {
            type Member<U> = <Wrap<T> as Family>::Member<U>;
        }
        bad(value:<Wrap<i64> as Family>::Member<Text>)->{ () }
        main()->{ () }
    "#;
    let reordered = r#"
        main()->{ () }
        bad(value:<Wrap<i64> as Family>::Member<Text>)->{ () }
        impl<T> Family for Wrap<T> where T: Family {
            type Member<U> = <Wrap<T> as Family>::Member<U>;
        }
        impl Family for i64 { type Member<T> = T; }
        struct Wrap<T> { value: T }
        trait Family { type Member<T>; }
    "#;
    let message = |source: &str| {
        let errors = compile_source_to_bytecode("gat-cycle.glorious", source).unwrap_err();
        assert_eq!(errors.len(), 1, "{errors:#?}");
        let error = &errors[0];
        assert_eq!(error.code.as_deref(), Some("G1BC002"));
        assert!(error.span.is_some());
        error.message.clone()
    };
    let first = message(source);
    assert_eq!(first, message(reordered));
    let trace = first
        .strip_prefix(
            "associated type projection is ambiguous or recursively cyclic; cycle trace: ",
        )
        .unwrap_or_else(|| panic!("unexpected cycle diagnostic: {first}"));
    let repeating = trace.split(" -> ").collect::<Vec<_>>();
    assert_eq!(repeating.len(), 2, "{trace}");
    assert_eq!(repeating[0], repeating[1]);
    assert!(
        trace.contains("Member") && trace.contains("Text"),
        "{trace}"
    );
}

#[test]
fn phantom_generic_use_specializes_only_reachable_marker_proven_grounds() {
    let source = r#"
        trait Marker {}
        struct Phantom<T> { marker: i64 }
        struct Leaf<T> { marker: i64 }
        struct Outer<T> { leaf: Leaf<T> }
        impl Marker for i64 {}
        impl<T> Use<[0,1]> for Phantom<T> {}
        impl<T> Use<[0,1]> for Leaf<T> where T: Marker {}
        integer(value: Phantom<i64>) -> Phantom<i64> { value }
        text(value: Phantom<Text>) -> Phantom<Text> { value }
        yes(value: Outer<i64>) -> Outer<i64> { value }
        no(value: Outer<Text>) -> Outer<Text> { value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("phantom-generic-use.glorious", source).unwrap();
    let param = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    for name in ["integer", "text", "yes"] {
        let ty = param(name);
        assert!(!phases.artifact.types[ty as usize].claimed_duplicable());
        assert!(phases.artifact.types[ty as usize].claimed_zero_use_allowed());
    }
    let no = param("no");
    assert!(phases.artifact.types[no as usize].claimed_duplicable());
    assert!(phases.artifact.types[no as usize].claimed_zero_use_allowed());
    assert!(phases.core.canonical_text().contains("copy=false"));
    assert!(phases.mir.canonical_text().contains("Move"));
    let bytes = phases.artifact.encode();
    verify(phases.artifact).unwrap();

    let reordered = r#"
        main() -> { () }
        no(value: Outer<Text>) -> Outer<Text> { value }
        yes(value: Outer<i64>) -> Outer<i64> { value }
        text(value: Phantom<Text>) -> Phantom<Text> { value }
        integer(value: Phantom<i64>) -> Phantom<i64> { value }
        impl<T> Use<[0,1]> for Leaf<T> where T: Marker {}
        impl<T> Use<[0,1]> for Phantom<T> {}
        impl Marker for i64 {}
        struct Outer<T> { leaf: Leaf<T> }
        struct Leaf<T> { marker: i64 }
        struct Phantom<T> { marker: i64 }
        trait Marker {}
    "#;
    assert_eq!(
        compile_source_to_bytecode("phantom-generic-use-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn symbolic_expected_type_fixes_phantom_nominal_construction_inside_enum() {
    let source = r#"
        struct Key<Tag> { raw: u32 }
        make<Tag, T>(item: T) -> Result<Key<Tag>, T> {
            Result::Ok(Key { raw: 7 })
        }
        main() -> { () }
    "#;
    let phases =
        compile_source_to_phases("phantom-nominal-expected-type.glorious", source).unwrap();
    verify(phases.artifact).unwrap();
}

#[test]
fn generic_use_rejects_dependent_layouts_and_overlaps_before_reachability() {
    let cases = [
        "struct Box<T> { value: T } impl<T> Use<[0,1]> for Box<T> {} main() -> { () }",
        "struct Phantom<T> { marker: i64 } impl<T> Use<[0,1]> for Phantom<T> {} impl<U> Use<[0,2]> for Phantom<U> {} main() -> { () }",
        "struct Phantom<T> { marker: i64 } impl<T> Use<[0,1]> for Phantom<T> {} impl Use<[0,2]> for Phantom<i64> {} main() -> { () }",
        "trait Left {} trait Right {} struct Item { marker: i64 } impl Use<[0,1]> for Item where Item: Left {} impl Use<[0,2]> for Item where Item: Right {} main() -> { () }",
        "trait Left {} trait Right {} struct Phantom<T> { marker: i64 } impl Use<[0,1]> for Phantom<i64> where i64: Left {} impl Use<[0,2]> for Phantom<i64> where i64: Right {} main() -> { () }",
    ];
    for source in cases {
        let errors =
            compile_source_to_bytecode("invalid-generic-use.glorious", source).unwrap_err();
        assert!(errors.iter().all(|error| error.span.is_some()));
        assert!(errors.iter().all(|error| error.code.is_some()));
    }

    let zero_roots = r#"
        struct Phantom<T> { marker: i64 }
        impl<T> Use<[0,2]> for Phantom<T> {}
        main() -> { () }
    "#;
    let artifact = compile_raw_source("unreached-generic-use.glorious", zero_roots).unwrap();
    assert_eq!(artifact.types.len(), Type::predefined().len());

    compile_source_to_bytecode(
        "permuted-generic-use.glorious",
        "struct Phantom<T, U> { marker: i64 } impl<T, U> Use<[0,1]> for Phantom<U, T> {} main() -> { () }",
    )
    .expect("structural generic Use heads may permute their bound arguments");
}

#[test]
fn binder_owned_generic_use_is_gated_by_intrinsic_principal_evidence() {
    let source = r#"
        trait Marker {}
        struct Erased { marker: i64 }
        struct Box<T> { value: T }
        struct Pair<A, B> { first: A, again: A, second: B }
        struct Marked<T> { value: T }
        struct ExactYes { marker: i64 }
        struct ExactNo { marker: i64 }
        impl Use<[0,0]> for Erased {}
        impl Marker for i64 {}
        impl<T> Use<[0,1]> for Box<T> where T: Use<[0,1]> {}
        impl<A, B> Use<[0,1]> for Pair<A, B>
            where A: Use<[0,1]>, B: Use<[0,1]> {}
        impl<T> Use<[0,1]> for Marked<T>
            where T: Marker, T: Use<[0,1]> {}
        impl Use<[0,1]> for ExactYes where i64: Use<[0,1]> {}
        impl Use<[0,1]> for ExactNo where Erased: Use<[0,1]> {}
        box_yes(value: Box<i64>) -> Box<i64> { value }
        box_no(value: Box<Erased>) -> { () }
        pair(value: Pair<i64, Text>) -> Pair<i64, Text> { value }
        marked_yes(value: Marked<i64>) -> Marked<i64> { value }
        marked_no(value: Marked<Text>) -> Marked<Text> { value }
        exact_yes(value: ExactYes) -> ExactYes { value }
        exact_no(value: ExactNo) -> ExactNo { value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("binder-use-evidence.glorious", source).unwrap();
    let parameter = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    for name in ["box_yes", "pair", "marked_yes", "exact_yes"] {
        let ty = parameter(name);
        assert!(!phases.artifact.types[ty as usize].claimed_duplicable());
        assert!(phases.artifact.types[ty as usize].claimed_zero_use_allowed());
    }
    let erased = parameter("box_no");
    assert!(!phases.artifact.types[erased as usize].claimed_duplicable());
    assert!(phases.artifact.types[erased as usize].claimed_zero_use_allowed());
    for name in ["marked_no", "exact_no"] {
        let unrestricted = parameter(name);
        assert!(phases.artifact.types[unrestricted as usize].claimed_duplicable());
        assert!(phases.artifact.types[unrestricted as usize].claimed_zero_use_allowed());
    }
    verify(phases.artifact).unwrap();
}

#[test]
fn intrinsic_generic_use_rejects_missing_weak_and_nested_binder_coverage() {
    let cases = [
        "struct Box<T> { value: T } impl<T> Use<[0,1]> for Box<T> {} main() -> { () }",
        "struct Box<T> { value: T } impl<T> Use<[1,1]> for Box<T> where T: Use<[0,0]> {} main() -> { () }",
        "struct Wrap<T> { value: T } struct Box<T> { value: Wrap<T> } impl<T> Use<[0,1]> for Box<T> where T: Use<[0,1]> {} main() -> { () }",
        "struct Pair<A, B> { first: A, second: B } impl<A, B> Use<[0,1]> for Pair<A, B> where A: Use<[0,1]> {} main() -> { () }",
    ];
    for source in cases {
        let errors = compile_source_to_bytecode("invalid-binder-use.glorious", source).unwrap_err();
        assert!(errors.iter().all(|error| error.span.is_some()));
        assert!(errors.iter().all(|error| error.code.is_some()));
    }
}

#[test]
fn nested_and_fixed_generic_use_fields_require_exact_intrinsic_evidence() {
    let source = r#"
        struct Erased { marker: i64 }
        struct Fixed { marker: i64 }
        struct Wrap<T> { value: T }
        struct Other<T> { value: T }
        struct Nested<T> { value: Wrap<T> }
        struct FixedOwner<T> { value: Fixed }
        struct Multiple<T> { left: Wrap<T>, right: Other<T> }
        impl Use<[0,0]> for Erased {}
        impl Use<[0,1]> for Fixed {}
        impl<T> Use<[0,1]> for Wrap<T> where T: Use<[0,1]> {}
        impl<T> Use<[0,1]> for Other<T> where T: Use<[0,1]> {}
        impl<T> Use<[0,1]> for Nested<T> where Wrap<T>: Use<[0,1]> {}
        impl<T> Use<[0,1]> for FixedOwner<T> where Fixed: Use<[0,1]> {}
        impl<T> Use<[0,1]> for Multiple<T>
            where Wrap<T>: Use<[0,1]>, Other<T>: Use<[0,1]> {}
        nested_yes(value: Nested<i64>) -> Nested<i64> { value }
        nested_no(value: Nested<Erased>) -> { () }
        fixed(value: FixedOwner<Text>) -> FixedOwner<Text> { value }
        multiple(value: Multiple<i64>) -> Multiple<i64> { value }
        main() -> {
            nested_yes(Nested { value: Wrap { value: 1 } });
            fixed(FixedOwner { value: Fixed { marker: 2 } });
            multiple(Multiple {
                left: Wrap { value: 3 },
                right: Other { value: 4 }
            });
            ()
        }
    "#;
    let reordered = r#"
        main() -> {
            nested_yes(Nested { value: Wrap { value: 1 } });
            fixed(FixedOwner { value: Fixed { marker: 2 } });
            multiple(Multiple {
                left: Wrap { value: 3 },
                right: Other { value: 4 }
            });
            ()
        }
        multiple(value: Multiple<i64>) -> Multiple<i64> { value }
        fixed(value: FixedOwner<Text>) -> FixedOwner<Text> { value }
        nested_no(value: Nested<Erased>) -> { () }
        nested_yes(value: Nested<i64>) -> Nested<i64> { value }
        impl<T> Use<[0,1]> for Multiple<T>
            where Other<T>: Use<[0,1]>, Wrap<T>: Use<[0,1]> {}
        impl<T> Use<[0,1]> for FixedOwner<T> where Fixed: Use<[0,1]> {}
        impl<T> Use<[0,1]> for Nested<T> where Wrap<T>: Use<[0,1]> {}
        impl<T> Use<[0,1]> for Other<T> where T: Use<[0,1]> {}
        impl<T> Use<[0,1]> for Wrap<T> where T: Use<[0,1]> {}
        impl Use<[0,1]> for Fixed {}
        impl Use<[0,0]> for Erased {}
        struct Multiple<T> { left: Wrap<T>, right: Other<T> }
        struct FixedOwner<T> { value: Fixed }
        struct Nested<T> { value: Wrap<T> }
        struct Other<T> { value: T }
        struct Wrap<T> { value: T }
        struct Fixed { marker: i64 }
        struct Erased { marker: i64 }
    "#;

    let phases = compile_source_to_phases("nested-generic-use.glorious", source).unwrap();
    let repeated = compile_source_to_phases("nested-generic-use.glorious", source).unwrap();
    let reordered_phases =
        compile_source_to_phases("nested-generic-use-reordered.glorious", reordered).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    let bytes = phases.artifact.encode();
    assert_eq!(bytes, reordered_phases.artifact.encode());
    let decoded = Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);

    for name in ["nested_yes", "nested_no", "fixed", "multiple"] {
        let ty = phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0];
        assert!(!phases.artifact.types[ty as usize].claimed_duplicable());
        assert!(phases.artifact.types[ty as usize].claimed_zero_use_allowed());
    }

    let verified = verify(decoded).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(phases.artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );
}

#[test]
fn nested_and_fixed_generic_use_reject_missing_mismatched_and_weak_evidence() {
    let cases = [
        r#"
            struct Wrap<T> { value: T }
            struct Outer<T> { value: Wrap<T> }
            impl<T> Use<[0,1]> for Outer<T> {}
            main() -> { () }
        "#,
        r#"
            struct Wrap<T> { value: T }
            struct Outer<T> { value: Wrap<T> }
            impl<T> Use<[0,1]> for Outer<T> where T: Use<[0,1]> {}
            main() -> { () }
        "#,
        r#"
            struct Wrap<T> { value: T }
            struct Outer<T> { value: Wrap<T> }
            impl<T> Use<[1,1]> for Outer<T> where Wrap<T>: Use<[0,0]> {}
            main() -> { () }
        "#,
        r#"
            struct Fixed { marker: i64 }
            struct Owner<T> { value: Fixed }
            impl Use<[0,1]> for Fixed {}
            impl<T> Use<[0,1]> for Owner<T> {}
            main() -> { () }
        "#,
        r#"
            struct Fixed { marker: i64 }
            struct Owner<T> { value: Fixed }
            impl Use<[0,0]> for Fixed {}
            impl<T> Use<[1,1]> for Owner<T> where Fixed: Use<[0,0]> {}
            main() -> { () }
        "#,
        r#"
            struct Wrap<T> { value: T }
            struct Other<T> { value: T }
            struct Multiple<T> { left: Wrap<T>, right: Other<T> }
            impl<T> Use<[0,1]> for Multiple<T> where Wrap<T>: Use<[0,1]> {}
            main() -> { () }
        "#,
    ];
    for source in cases {
        let errors =
            compile_source_to_bytecode("invalid-nested-generic-use.glorious", source).unwrap_err();
        assert!(errors.iter().all(|error| error.span.is_some()));
        assert!(errors.iter().all(|error| error.code.is_some()));
    }
}

#[test]
fn conditional_intrinsic_use_does_not_create_reachability_and_reports_cycles() {
    let no_reachability = r#"
        struct Wrap<T> { value: T }
        struct Box<T> { value: T }
        impl<T> Use<[0,1]> for Box<T> where T: Use<[0,1]>, Wrap<T>: Use<[0,1]> {}
        forward(value: Box<i64>) -> Box<i64> { value }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("use-no-reachability.glorious", no_reachability).unwrap();
    let ty = artifact
        .functions
        .iter()
        .find(|function| function.name == "forward")
        .unwrap()
        .params[0];
    assert!(artifact.types[ty as usize].claimed_duplicable());

    let cyclic = r#"
        struct A { marker: i64 }
        struct B { marker: i64 }
        impl Use<[0,1]> for A where B: Use<[0,1]> {}
        impl Use<[0,1]> for B where A: Use<[0,1]> {}
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("cyclic-intrinsic-use.glorious", cyclic).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("ambiguous or cyclic"))
    );
}

#[test]
fn conditional_intrinsic_use_reports_principal_solver_overflow() {
    let mut source = String::new();
    for index in 0..67 {
        source.push_str(&format!("struct N{index} {{ marker: i64 }} "));
    }
    for index in 0..66 {
        source.push_str(&format!(
            "impl Use<[0,1]> for N{index} where N{}: Use<[0,1]> {{}} ",
            index + 1
        ));
    }
    source.push_str("impl Use<[0,1]> for N66 {} main() -> { () }");
    let errors =
        compile_source_to_bytecode("overflow-intrinsic-use.glorious", &source).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("principal solver limit"))
    );
}

#[test]
fn substituted_intrinsic_use_goals_are_canonical_across_declaration_order() {
    let source = r#"
        struct Erased { marker: i64 }
        struct Box<T> { value: T }
        impl Use<[0,0]> for Erased {}
        impl<T> Use<[0,1]> for Box<T> where T: Use<[0,1]> {}
        yes(value: Box<i64>) -> Box<i64> { value }
        no(value: Box<Erased>) -> { () }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        no(value: Box<Erased>) -> { () }
        yes(value: Box<i64>) -> Box<i64> { value }
        impl<T> Use<[0,1]> for Box<T> where T: Use<[0,1]> {}
        impl Use<[0,0]> for Erased {}
        struct Box<T> { value: T }
        struct Erased { marker: i64 }
    "#;
    assert_eq!(
        compile_source_to_bytecode("canonical-intrinsic-use.glorious", source)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("canonical-intrinsic-use-reordered.glorious", reordered)
            .unwrap()
            .encode()
    );
}

#[test]
fn intrinsic_bound_generic_zero_use_is_compatible_with_drop_and_cleanup() {
    let accepted = r#"
        struct Resource<T> { value: T }
        impl<T> Use<[0,1]> for Resource<T> where T: Use<[0,1]> {}
        impl<T> Drop for Resource<T> { drop(&mut self) -> { () } }
        consume(value: Resource<i64>) -> { value; () }
        main() -> { consume(Resource { value: 1 }) }
    "#;
    let artifact = compile_source_to_bytecode("intrinsic-use-drop.glorious", accepted).unwrap();
    assert_eq!(user_drop_glue(&artifact).count(), 1);
    let bytes = artifact.encode();
    let decoded = Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);
    assert_eq!(
        Vm::new(verify(decoded).unwrap())
            .run(artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );

    let unused = r#"
        struct Resource<T> { value: T }
        impl<T> Use<[0,1]> for Resource<T> where T: Use<[0,1]> {}
        impl<T> Drop for Resource<T> { drop(&mut self) -> { () } }
        unused(value: Resource<i64>) -> { () }
        main() -> { () }
    "#;
    verify(compile_source_to_bytecode("unused-intrinsic-use-drop.glorious", unused).unwrap())
        .unwrap();
}

#[test]
fn conditional_generic_use_and_drop_select_the_same_ground_instance() {
    let source = r#"
        trait Marker {}
        struct Resource<T> { marker: i64 }
        impl Marker for i64 {}
        impl<T> Use<[0,1]> for Resource<T> where T: Marker {}
        impl<T> Drop for Resource<T> where T: Marker {
            drop(&mut self) -> { self.marker; () }
        }
        yes(value: Resource<i64>) -> Resource<i64> { value }
        no(value: Resource<Text>) -> Resource<Text> { value }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("conditional-use-drop.glorious", source).unwrap();
    let yes = artifact
        .functions
        .iter()
        .find(|function| function.name == "yes")
        .unwrap()
        .params[0];
    let no = artifact
        .functions
        .iter()
        .find(|function| function.name == "no")
        .unwrap()
        .params[0];
    assert!(artifact.drop_glue.iter().any(|glue| glue.ty == yes));
    assert!(artifact.drop_glue.iter().all(|glue| glue.ty != no));
    assert_ne!(yes, no);
    assert!(!artifact.types[yes as usize].claimed_duplicable());
    assert!(artifact.types[no as usize].claimed_duplicable());
    let bytes = artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    verify(artifact).unwrap();

    let widening = r#"
        trait Marker {}
        struct Owner { value: &mut i64 }
        impl Marker for Owner {}
        impl Use<[0,infinity]> for Owner where Owner: Marker {}
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("conditional-use-widening.glorious", widening).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("widens the structurally derived"))
    );

    let must_move_drop = r#"
        trait Marker {}
        struct Resource<T> { marker: i64 }
        impl Marker for i64 {}
        impl<T> Use<[1,1]> for Resource<T> where T: Marker {}
        impl<T> Drop for Resource<T> where T: Marker { drop(&mut self) -> { () } }
        make() -> Resource<i64> { Resource { marker: 1 } }
        bad() -> { let value = make(); () }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("conditional-use-drop-cleanup.glorious", must_move_drop)
            .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("support `[0,0]`"))
    );
}

#[test]
fn exact_linear_use_checks_straight_line_scopes_calls_and_flags() {
    let source = r#"
        struct Ticket { value: i64 }
        struct Holder { ticket: Ticket }
        enum Envelope { Empty, Full(Ticket) }
        impl Use<[1,1]> for Ticket {}
        make() -> Ticket { Ticket { value: 1 } }
        forward(value: Ticket) -> Ticket { value }
        inline() -> Ticket { forward(Ticket { value: 2 }) }
        roundtrip() -> Ticket { let value = make(); forward(value) }
        nested(value: Ticket) -> Ticket { { let shadow = value; shadow } }
        borrowed(value: Ticket) -> Ticket { &value; value }
        forward_holder(value: Holder) -> Holder { value }
        forward_envelope(value: Envelope) -> Envelope { value }
        forward_tuple(value: (Ticket, i64)) -> (Ticket, i64) { value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("exact-linear.glorious", source).unwrap();
    for name in ["Ticket", "Holder", "Envelope"] {
        let ty = phases
            .artifact
            .types
            .iter()
            .find(|ty| match ty.representation() {
                Type::Struct { name: found, .. } | Type::Enum { name: found, .. } => found == name,
                _ => false,
            })
            .unwrap();
        assert!(!ty.claimed_duplicable());
        assert!(!ty.claimed_zero_use_allowed());
    }
    assert!(phases.artifact.types.iter().any(|ty| {
        matches!(ty.representation(), Type::Tuple { fields, .. } if fields.len() == 2)
            && !ty.claimed_duplicable()
            && !ty.claimed_zero_use_allowed()
    }));
    assert!(phases.core.canonical_text().contains("local l0 copy=false"));
    assert!(phases.mir.canonical_text().contains("Move"));
    let bytes = phases.artifact.encode();
    let decoded = Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);
    assert_eq!(
        Vm::new(verify(decoded).unwrap())
            .run(phases.artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );

    let reordered = r#"
        main() -> { () }
        forward_tuple(value: (Ticket, i64)) -> (Ticket, i64) { value }
        forward_envelope(value: Envelope) -> Envelope { value }
        forward_holder(value: Holder) -> Holder { value }
        borrowed(value: Ticket) -> Ticket { &value; value }
        nested(value: Ticket) -> Ticket { { let shadow = value; shadow } }
        roundtrip() -> Ticket { let value = make(); forward(value) }
        inline() -> Ticket { forward(Ticket { value: 2 }) }
        forward(value: Ticket) -> Ticket { value }
        make() -> Ticket { Ticket { value: 1 } }
        impl Use<[1,1]> for Ticket {}
        struct Holder { ticket: Ticket }
        enum Envelope { Empty, Full(Ticket) }
        struct Ticket { value: i64 }
    "#;
    assert_eq!(
        compile_source_to_bytecode("exact-linear-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn exact_linear_use_rejects_underuse_double_use_discard_and_partial_move() {
    let cases = [
        "struct Ticket { value: i64 } impl Use<[1,1]> for Ticket {} bad(value: Ticket) -> { () } main() -> { () }",
        "struct Ticket { value: i64 } impl Use<[1,1]> for Ticket {} bad() -> { let value = Ticket { value: 1 }; () } main() -> { () }",
        "struct Ticket { value: i64 } impl Use<[1,1]> for Ticket {} bad(value: Ticket) -> i64 { let first = value; let second = value; 0 } main() -> { () }",
        "struct Ticket { value: i64 } impl Use<[1,1]> for Ticket {} make() -> Ticket { Ticket { value: 1 } } bad() -> { make(); () } main() -> { () }",
        "struct Owner { value: &mut i64 } struct Ticket { value: i64 } impl Use<[1,1]> for Ticket {} struct Pair { owner: Owner, ticket: Ticket } impl Use<[1,1]> for Pair {} bad(value: Pair) -> Owner { value.owner } main() -> { () }",
    ];
    for source in cases {
        let errors = compile_source_to_bytecode("invalid-exact-use.glorious", source).unwrap_err();
        assert!(errors.iter().all(|error| error.span.is_some()));
        assert!(errors.iter().all(|error| error.code.is_some()));
    }
}

#[test]
fn ground_generic_drop_requires_zero_use_containment() {
    let accepted = r#"
        struct Box<T> { value: T }
        impl Use<[0,0]> for Box<i64> {}
        impl<T> Drop for Box<T> { drop(&mut self) -> { self.value; () } }
        main() -> { let value = Box { value: 1 }; () }
    "#;
    let artifact = compile_source_to_bytecode("erased-ground-drop.glorious", accepted).unwrap();
    assert_eq!(user_drop_glue(&artifact).count(), 1);
    let ty = user_drop_glue(&artifact).next().unwrap().ty;
    assert!(!artifact.types[ty as usize].claimed_duplicable());
    assert!(artifact.types[ty as usize].claimed_zero_use_allowed());
    verify(artifact).unwrap();

    let must_move = r#"
        struct MustAccount { value: i64 }
        impl Use<[1,1]> for MustAccount {}
        impl Drop for MustAccount { drop(&mut self) -> { () } }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("must-move-drop.glorious", must_move).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("support `[0,0]`"))
    );
}

#[test]
fn exact_linear_use_is_scoped_to_involved_effect_control() {
    let unrelated = r#"
        effect Stop { stop() -> ! }
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        run() -> { handle perform Stop::stop() { Stop::stop() => () } }
        main() -> { () }
    "#;
    let unrelated_artifact =
        compile_source_to_bytecode("unrelated-exact-effect.glorious", unrelated).unwrap();
    verify(unrelated_artifact.clone()).unwrap();
    let unrelated_reordered = r#"
        main() -> { () }
        run() -> { handle perform Stop::stop() { Stop::stop() => () } }
        impl Use<[1,1]> for Ticket {}
        struct Ticket { value: i64 }
        effect Stop { stop() -> ! }
    "#;
    assert_eq!(
        compile_source_to_bytecode(
            "unrelated-exact-effect-reordered.glorious",
            unrelated_reordered
        )
        .unwrap()
        .encode(),
        unrelated_artifact.encode()
    );

    let involved = r#"
        effect Stop { stop() -> ! }
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        bad(value: Ticket) -> { handle perform Stop::stop() { Stop::stop() => () } }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("involved-exact-effect.glorious", involved).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("actual Use count")),
        "{errors:#?}"
    );
}

#[test]
fn relevant_use_checks_repeated_whole_copies_calls_layouts_and_flags() {
    let source = r#"
        struct Token { value: i64 }
        struct Pair { left: Token, right: Token }
        struct Holder { token: Token }
        struct Box<T> { value: T }
        enum Envelope { Empty, Full(Token) }
        impl Use<[1,infinity]> for Token {}
        impl Use<[1,infinity]> for Box<i64> {}
        make() -> Token { Token { value: 1 } }
        forward(value: Token) -> Token { move value }
        duplicate(value: Token) -> Pair { Pair { left: value, right: move value } }
        inline() -> Token { forward(Token { value: 2 }) }
        roundtrip() -> Token { let value = make(); &value; move value }
        forward_holder(value: Holder) -> Holder { move value }
        forward_envelope(value: Envelope) -> Envelope { move value }
        forward_tuple(value: (Token, i64)) -> (Token, i64) { move value }
        forward_box(value: Box<i64>) -> Box<i64> { move value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("relevant.glorious", source).unwrap();
    for name in ["Token", "Pair", "Holder", "Envelope"] {
        let ty = phases
            .artifact
            .types
            .iter()
            .find(|ty| match ty.representation() {
                Type::Struct { name: found, .. } | Type::Enum { name: found, .. } => found == name,
                _ => false,
            })
            .unwrap();
        assert!(ty.claimed_duplicable(), "{name} should remain duplicable");
        assert!(
            !ty.claimed_zero_use_allowed(),
            "{name} should require a use"
        );
    }
    let ground_box = phases
        .artifact
        .types
        .iter()
        .find(|ty| {
            matches!(ty.representation(), Type::Struct { name, fields, .. } if name.contains("Box") && fields.len() == 1)
        })
        .expect("reachable Box<i64> descriptor");
    assert!(ground_box.claimed_duplicable());
    assert!(!ground_box.claimed_zero_use_allowed());
    assert!(phases.artifact.types.iter().any(|ty| {
        matches!(ty.representation(), Type::Tuple { fields, .. } if fields.len() == 2)
            && ty.claimed_duplicable()
            && !ty.claimed_zero_use_allowed()
    }));
    assert!(phases.core.canonical_text().contains("local l0 copy=true"));
    assert!(phases.mir.canonical_text().contains("Copy"));
    let bytes = phases.artifact.encode();
    let decoded = Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);
    assert_eq!(
        Vm::new(verify(decoded).unwrap())
            .run(phases.artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );

    let reordered = r#"
        main() -> { () }
        forward_box(value: Box<i64>) -> Box<i64> { move value }
        forward_tuple(value: (Token, i64)) -> (Token, i64) { move value }
        forward_envelope(value: Envelope) -> Envelope { move value }
        forward_holder(value: Holder) -> Holder { move value }
        roundtrip() -> Token { let value = make(); &value; move value }
        inline() -> Token { forward(Token { value: 2 }) }
        duplicate(value: Token) -> Pair { Pair { left: value, right: move value } }
        forward(value: Token) -> Token { move value }
        make() -> Token { Token { value: 1 } }
        impl Use<[1,infinity]> for Box<i64> {}
        impl Use<[1,infinity]> for Token {}
        enum Envelope { Empty, Full(Token) }
        struct Box<T> { value: T }
        struct Holder { token: Token }
        struct Pair { left: Token, right: Token }
        struct Token { value: i64 }
    "#;
    assert_eq!(
        compile_source_to_bytecode("relevant-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn relevant_use_rejects_underuse_projection_discard_and_involved_effects() {
    let cases = [
        "struct Token { value: i64 } impl Use<[1,infinity]> for Token {} bad(value: Token) -> { () } main() -> { () }",
        "struct Token { value: i64 } impl Use<[1,infinity]> for Token {} make() -> Token { Token { value: 1 } } bad() -> { let value = make(); () } main() -> { () }",
        "struct Token { value: i64 } impl Use<[1,infinity]> for Token {} bad(value: Token) -> i64 { value.value } main() -> { () }",
        "struct Token { value: i64 } impl Use<[1,infinity]> for Token {} make() -> Token { Token { value: 1 } } bad() -> { make(); () } main() -> { () }",
        "effect Stop { stop() -> ! } struct Token { value: i64 } impl Use<[1,infinity]> for Token {} bad(value: Token) -> { handle perform Stop::stop() { Stop::stop() => () } } main() -> { () }",
        "effect Stop { stop() -> ! } struct Token { value: i64 } impl Use<[1,infinity]> for Token {} abort() -> i64 / {Stop} { perform Stop::stop() } bad(value: Token) -> Token / {Stop} { abort(); value } main() -> { () }",
    ];
    for source in cases {
        let errors =
            compile_source_to_bytecode("invalid-relevant-use.glorious", source).unwrap_err();
        assert!(errors.iter().all(|error| error.span.is_some()));
        assert!(errors.iter().all(|error| error.code.is_some()));
    }

    let widening = r#"
        struct Affine { value: i64 }
        struct Invalid { value: Affine }
        impl Use<[0,1]> for Affine {}
        impl Use<[1,infinity]> for Invalid {}
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("relevant-widening.glorious", widening).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("widens the structurally derived"))
    );

    let unrelated = r#"
        effect Stop { stop() -> ! }
        struct Token { value: i64 }
        impl Use<[1,infinity]> for Token {}
        run() -> { handle perform Stop::stop() { Stop::stop() => () } }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("unrelated-relevant-effect.glorious", unrelated).unwrap();
    verify(artifact).unwrap();
}

#[test]
fn relevant_use_is_duplicable_but_cannot_implement_drop() {
    let accepted = r#"
        struct Resource { value: i64 }
        impl Use<[1,infinity]> for Resource {}
        forward(value: Resource) -> Resource { move value }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("relevant-transfer.glorious", accepted).unwrap();
    let ty = artifact
        .functions
        .iter()
        .find(|function| function.name == "forward")
        .unwrap()
        .params[0];
    assert!(artifact.types[ty as usize].claimed_duplicable());
    assert!(!artifact.types[ty as usize].claimed_zero_use_allowed());
    verify(artifact).unwrap();

    let drop_impl = r#"
        struct Resource { value: i64 }
        impl Use<[1,infinity]> for Resource {}
        impl Drop for Resource { drop(&mut self) -> { () } }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("relevant-drop.glorious", drop_impl).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("support `[0,0]`"))
    );
}

#[test]
fn custom_drop_rejects_partial_noncopy_moves_but_keeps_copy_and_whole_moves_legal() {
    for source in [
        r#"
            struct Owner { value: &mut i64 }
            struct Residual { owner: Owner, marker: i64 }
            impl Drop for Residual { drop(&mut self) -> { self.marker; () } }
            extract_owner(value: Residual) -> Owner { value.owner }
            main() -> { () }
        "#,
        r#"
            struct Owner { value: &mut i64 }
            struct Inner { owner: Owner }
            struct Outer { inner: Inner }
            impl Drop for Outer { drop(&mut self) -> { () } }
            extract_owner(value: Outer) -> Owner { value.inner.owner }
            main() -> { () }
        "#,
    ] {
        let error = compile_source_to_bytecode("partial-drop-move.glorious", source).unwrap_err();
        assert_eq!(error[0].code.as_deref(), Some("G1BC002"));
        assert!(
            error[0].message.contains("custom Drop hook"),
            "{}",
            error[0].message
        );
    }

    let legal = compile_source_to_phases(
        "legal-drop-access.glorious",
        r#"
            struct Owner { value: &mut i64 }
            struct Residual { owner: Owner, marker: i64 }
            impl Drop for Residual { drop(&mut self) -> { self.marker; () } }
            inspect(value: Residual) -> i64 { value.marker }
            forward(value: Residual) -> Residual { value }
            main() -> { () }
        "#,
    )
    .unwrap();
    assert!(
        legal
            .artifact
            .types
            .iter()
            .any(|ty| matches!(ty.representation(), Type::Struct { name, copy: false, .. } if name == "Residual"))
    );
    verify(legal.artifact).unwrap();
}

#[test]
fn grounded_generic_drop_rejects_only_instances_with_an_applicable_hook() {
    for source in [
        r#"
            struct Owner { value: &mut i64 }
            struct Box<T> { value: T }
            impl<T> Drop for Box<T> { drop(&mut self) -> { () } }
            extract_owner(value: Box<Owner>) -> Owner { value.value }
            main() -> { () }
        "#,
        r#"
            trait Marker {}
            struct Owner { value: &mut i64 }
            struct Box<T> { value: T }
            impl Marker for Owner {}
            impl<T> Drop for Box<T> where T: Marker { drop(&mut self) -> { () } }
            extract_owner(value: Box<Owner>) -> Owner { value.value }
            main() -> { () }
        "#,
    ] {
        let error =
            compile_source_to_bytecode("generic-partial-drop-move.glorious", source).unwrap_err();
        assert_eq!(error[0].code.as_deref(), Some("G1BC002"));
        assert!(error[0].message.contains("custom Drop hook"));
    }

    let phases = compile_source_to_phases(
        "conditional-drop-not-applicable.glorious",
        r#"
            trait Marker {}
            struct Owner { value: &mut i64 }
            struct Box<T> { value: T }
            impl<T> Drop for Box<T> where T: Marker { drop(&mut self) -> { () } }
            extract_owner(value: Box<Owner>) -> Owner { value.value }
            main() -> { () }
        "#,
    )
    .unwrap();
    assert_eq!(user_drop_glue(&phases.artifact).count(), 0);
    assert!(phases.mir.canonical_text().contains("ProjectMove"));
    verify(phases.artifact).unwrap();
}

#[test]
fn generic_drop_emits_one_hook_per_reachable_ground_instance() {
    let source = r#"
        struct Box<T> { value: T }
        struct Wrapper { item: Box<i64> }
        impl<T> Drop for Box<T> { drop(&mut self) -> { self.value; () } }
        integer(value: Box<i64>) -> { () }
        text(value: Box<Text>) -> { () }
        wrapper(value: Wrapper) -> { () }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-drop.glorious", source).unwrap();
    let reordered = r#"
        main() -> { () }
        wrapper(value: Wrapper) -> { () }
        text(value: Box<Text>) -> { () }
        integer(value: Box<i64>) -> { () }
        impl<T> Drop for Box<T> { drop(&mut self) -> { self.value; () } }
        struct Wrapper { item: Box<i64> }
        struct Box<T> { value: T }
    "#;
    let reordered =
        compile_source_to_bytecode("generic-drop-reordered.glorious", reordered).unwrap();
    verify(phases.artifact.clone()).unwrap();
    let artifact = &phases.artifact;
    assert_eq!(user_drop_glue(artifact).count(), 2);
    assert!(
        artifact
            .drop_glue
            .windows(2)
            .all(|pair| pair[0].ty < pair[1].ty)
    );
    for glue in user_drop_glue(artifact) {
        let hook = &artifact.functions[glue.function as usize];
        assert_eq!(
            hook.flags & grandiose_vm::DROP_HOOK,
            grandiose_vm::DROP_HOOK
        );
        assert_eq!(hook.return_type, grandiose_vm::UNIT);
        assert_eq!(hook.params.len(), 1);
        assert!(matches!(
            artifact.types[hook.params[0] as usize],
            Type::RefUnique { referent } if referent == glue.ty
        ));
    }
    assert_eq!(
        Artifact::decode(&artifact.encode()).unwrap().encode(),
        artifact.encode()
    );
    assert_eq!(artifact.encode(), reordered.encode());
    assert_eq!(
        phases
            .core
            .functions
            .iter()
            .filter(|function| {
                function.name.starts_with("$drop$") && function.name.contains("Box")
            })
            .count(),
        2
    );
    assert_eq!(
        phases
            .mir
            .functions
            .iter()
            .filter(|function| {
                function.name.starts_with("$drop$") && function.name.contains("Box")
            })
            .count(),
        2
    );
    assert!(
        phases
            .artifact
            .types
            .iter()
            .any(|ty| matches!(ty.representation(), Type::Struct { name, copy: true, .. } if name == "Wrapper"))
    );
}

#[test]
fn generic_drop_hook_runs_before_ground_instance_children() {
    let source = r#"
        struct Child<T> { value: T }
        struct Parent<T> { child: Child<T>, marker: i64 }
        observe(value: i64) -> { () }
        impl<T> Drop for Child<T> {
            drop(&mut self) -> { self.value; 9223372036854775807 + 1; () }
        }
        impl<T> Drop for Parent<T> {
            drop(&mut self) -> { observe(self.marker); 1 / 0; () }
        }
        make() -> Parent<i64> {
            Parent { child: Child { value: 1 }, marker: 2 }
        }
        main() -> { let value = make(); () }
    "#;
    let artifact = compile_source_to_bytecode("generic-drop-order.glorious", source).unwrap();
    assert_eq!(user_drop_glue(&artifact).count(), 2);
    let error = Vm::new(verify(artifact.clone()).unwrap())
        .run(artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");
}

#[test]
fn conditional_generic_drop_selects_only_proven_ground_instances() {
    let source = r#"
        trait Marker {}
        struct Box<T> { value: T }
        impl Marker for i64 {}
        impl<T> Drop for Box<T> where T: Marker {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        integer(value: Box<i64>) -> { () }
        text(value: Box<Text>) -> { () }
        make() -> Box<i64> { Box { value: 1 } }
        main() -> { let value = make(); () }
    "#;
    let phases = compile_source_to_phases("conditional-drop.glorious", source).unwrap();
    let artifact = &phases.artifact;
    let integer = artifact
        .functions
        .iter()
        .find(|function| function.name == "integer")
        .unwrap()
        .params[0];
    let text = artifact
        .functions
        .iter()
        .find(|function| function.name == "text")
        .unwrap()
        .params[0];
    assert!(artifact.drop_glue.iter().any(|glue| glue.ty == integer));
    assert!(artifact.drop_glue.iter().all(|glue| glue.ty != text));
    assert!(matches!(
        artifact.types[text as usize].representation(),
        Type::Struct { copy: true, .. }
    ));
    assert!(matches!(
        artifact.types[integer as usize].representation(),
        Type::Struct { copy: true, .. }
    ));
    assert!(
        phases
            .core
            .functions
            .iter()
            .any(|function| function.name.starts_with("$drop$") && function.name.contains("Box"))
    );
    assert!(
        phases
            .mir
            .functions
            .iter()
            .any(|function| function.name.starts_with("$drop$") && function.name.contains("Box"))
    );
    let bytes = artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let error = Vm::new(verify(artifact.clone()).unwrap())
        .run(artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");

    let repeated = compile_source_to_phases("drop-rooted-specialization.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(bytes, repeated.artifact.encode());

    let reordered = r#"
        main() -> { let value = make(); () }
        make() -> Box<i64> { Box { value: 1 } }
        text(value: Box<Text>) -> { () }
        integer(value: Box<i64>) -> { () }
        impl<T> Drop for Box<T> where T: Marker {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        impl Marker for i64 {}
        struct Box<T> { value: T }
        trait Marker {}
    "#;
    assert_eq!(
        bytes,
        compile_source_to_bytecode("conditional-drop-reordered.glorious", reordered)
            .unwrap()
            .encode()
    );
}

#[test]
fn conditional_generic_drop_uses_recursive_marker_evidence() {
    let source = r#"
        trait Marker {}
        struct Wrap<T> { value: T }
        struct Box<T> { value: T }
        impl Marker for i64 {}
        impl<T> Marker for Wrap<T> where T: Marker {}
        impl<T> Drop for Box<T> where T: Marker { drop(&mut self) -> { () } }
        proven(value: Box<Wrap<i64>>) -> { () }
        missing(value: Box<Wrap<Text>>) -> { () }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("recursive-conditional-drop.glorious", source).unwrap();
    let proven = artifact
        .functions
        .iter()
        .find(|function| function.name == "proven")
        .unwrap()
        .params[0];
    assert_eq!(user_drop_glue(&artifact).count(), 1);
    assert!(user_drop_glue(&artifact).any(|glue| glue.ty == proven));
}

#[test]
fn conditional_generic_drop_rejects_cyclic_goals_and_overlapping_heads() {
    let cyclic = r#"
        trait Marker {}
        struct Loop<T> { value: T }
        struct Box<T> { value: T }
        impl<T> Marker for Loop<T> where Loop<T>: Marker {}
        impl<T> Drop for Box<T> where T: Marker { drop(&mut self) -> { () } }
        reachable(value: Box<Loop<i64>>) -> { () }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("cyclic-conditional-drop.glorious", cyclic).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.message
            == "recursive implementation where-goal for `Marker` does not strictly decrease the type-constructor measure"
            && error.code.as_deref() == Some("G1TR001")
            && error.span.is_some()
    }));

    let overlap = r#"
        trait Left {}
        trait Right {}
        struct Box<T> { value: T }
        impl<T> Drop for Box<T> where T: Left { drop(&mut self) -> { () } }
        impl<U> Drop for Box<U> where U: Right { drop(&mut self) -> { () } }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("overlapping-conditional-drop.glorious", overlap).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.message.contains("overlapping")
            && error.message.contains("Drop")
            && error.span.is_some()
            && error.code.is_some()
    }));

    let nested = (0..=128).fold("i64".to_owned(), |inner, _| format!("Wrap<{inner}>"));
    let overflow = format!(
        "trait Marker {{}} struct Wrap<T> {{ value: T }} struct Box<T> {{ value: T }} \
         impl Marker for i64 {{}} impl<T> Marker for Wrap<T> where T: Marker {{}} \
         impl<T> Drop for Box<T> where T: Marker {{ drop(&mut self) -> {{ () }} }} \
         reachable(value: Box<{nested}>) -> {{ () }} main() -> {{ () }}"
    );
    let errors = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("solver-boundary-drop".into())
            .stack_size(16 * 1024 * 1024)
            .spawn_scoped(scope, || {
                compile_source_to_bytecode("overflow-conditional-drop.glorious", &overflow)
            })
            .unwrap()
            .join()
            .unwrap()
    })
    .unwrap_err();
    assert!(errors.iter().any(|error| {
        error
            .message
            .contains("nested solver frames limit 128 exceeded; trace:")
            && error.span.is_some()
            && error.code.as_deref() == Some("G1BC002")
    }));
}

#[test]
fn invalid_drop_targets_and_bodies_have_structured_diagnostics() {
    let cases = [
        "impl Drop for Missing { drop(&mut self) -> { () } } main() -> { () }",
        "struct Item { value: i64 } impl Drop for Item { drop(&mut self) -> { () } } impl Drop for Item { drop(&mut self) -> { () } } main() -> { () }",
        "struct Box<T> { value: T } impl Drop for Box<i64> { drop(&mut self) -> { () } } main() -> { () }",
        "struct Box<T> { value: T } impl<T, U> Drop for Box<T> { drop(&mut self) -> { () } } main() -> { () }",
        "struct Box<T> { value: T } impl<T> Drop for Box<U> { drop(&mut self) -> { () } } main() -> { () }",
        "struct Box<T> { value: T } impl<T> Drop for Box<T> where T: Fn<(), Output=T> { drop(&mut self) -> { () } } main() -> { () }",
        "struct Box<T> { value: T } impl<T> Drop for Box<T> { drop(&mut self) -> { () } } impl<U> Drop for Box<U> { drop(&mut self) -> { () } } main() -> { () }",
        "struct Box<T> { value: T } impl<T> Drop for &Box<T> { drop(&mut self) -> { () } } main() -> { () }",
        "struct Item { value: i64 } impl Drop for Item { drop(&mut self) -> { let moved = self; () } } main() -> { () }",
        "struct Owner { value: &mut i64 } impl Drop for Owner { drop(&mut self) -> { self.value; () } } main() -> { () }",
        "effect Ask { [1,1] ask() -> i64 } unsafe_call() -> { handle { perform Ask::ask(); () } { Ask::ask() with k => { resume(k, 1); () } } } struct Item { value: i64 } impl Drop for Item { drop(&mut self) -> { unsafe_call() } } main() -> { () }",
    ];
    for (index, source) in cases.into_iter().enumerate() {
        let errors = match compile_source_to_bytecode("bad-drop.glorious", source) {
            Err(errors) => errors,
            Ok(_) => panic!("case {index} unexpectedly compiled: {source}"),
        };
        assert!(
            errors
                .iter()
                .any(|error| error.code.is_some() && error.span.is_some()),
            "{errors:#?}"
        );
    }

    compile_source_to_bytecode(
        "nested-drop-head.glorious",
        "struct Box<T> { value: T } impl<T> Drop for Box<Box<T>> { drop(&mut self) -> { () } } main() -> { () }",
    )
    .expect("structural generic Drop heads may contain finite nested nominal patterns");
    compile_source_to_bytecode(
        "referenced-drop-goal.glorious",
        "trait Marker {} struct Box<T> { value: T } impl<T> Drop for Box<T> where &T: Marker { drop(&mut self) -> { () } } main() -> { () }",
    )
    .expect("generic Drop marker goals may use supported reference subjects");
}

#[test]
fn tuples_construct_project_call_nest_and_specialize() {
    let source = r#"
        struct Owner { value: &mut i64 }
        pair() -> (i64, Text) { (42, "tuple") }
        singleton() -> (i64,) { (42,) }
        nested() -> (i64, (Text,)) { (42, ("nested",)) }
        id<T>(value: T) -> T { value }
        specialized() -> (i64, Text) { id(pair()) }
        discard_tuple(value: (Owner,)) -> { () }
        answer() -> i64 { pair().0 }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("tuples.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified.clone()).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
    let function = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32
    };
    assert_eq!(
        Vm::new(verified.clone())
            .run(function("specialized"), vec![])
            .unwrap(),
        Vm::new(verified).run(function("pair"), vec![]).unwrap()
    );
    assert!(phases.artifact.types.iter().any(|ty| matches!(ty.representation(), Type::Tuple { fields, .. } if fields == &[grandiose_vm::I64, grandiose_vm::TEXT])));
    assert!(
        phases
            .artifact
            .types
            .iter()
            .any(|ty| matches!(ty.representation(), Type::Tuple { copy: false, .. }))
    );
    let discard = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "discard_tuple")
        .unwrap() as u32;
    assert!(
        phases
            .artifact
            .cleanups
            .iter()
            .any(|cleanup| cleanup.function == discard && !cleanup.registers.is_empty())
    );
    assert!(phases.core.canonical_text().contains("construct"));
    assert!(phases.mir.canonical_text().contains("Construct"));
}

#[test]
fn tuple_descriptors_are_structural_canonical_and_request_free() {
    let baseline = "main() -> { () }";
    let grouped = "grouped(value: (i64)) -> i64 { (value) } main() -> { () }";
    let baseline_artifact =
        compile_source_to_bytecode("tuple-baseline.glorious", baseline).unwrap();
    let grouped_artifact = compile_source_to_bytecode("tuple-grouped.glorious", grouped).unwrap();
    assert_eq!(baseline_artifact.types, grouped_artifact.types);
    assert_eq!(
        baseline_artifact
            .types
            .iter()
            .filter(|ty| matches!(ty.representation(), Type::Tuple { .. }))
            .count(),
        grouped_artifact
            .types
            .iter()
            .filter(|ty| matches!(ty.representation(), Type::Tuple { .. }))
            .count(),
        "parenthesized grouping must not request an additional tuple descriptor"
    );

    let first = r#"
        outer(value: (i64, (Text,))) -> (i64, (Text,)) { value }
        single(value: (i64,)) -> (i64,) { value }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        single(value: (i64,)) -> (i64,) { value }
        outer(value: (i64, (Text,))) -> (i64, (Text,)) { value }
    "#;
    let first = compile_source_to_bytecode("tuple-order.glorious", first).unwrap();
    let reordered =
        compile_source_to_bytecode("tuple-order-reordered.glorious", reordered).unwrap();
    assert_eq!(first.encode(), reordered.encode());
    for (parent, ty) in first.types.iter().enumerate() {
        if let Type::Tuple { fields, .. } = ty.representation() {
            for child in fields {
                if matches!(
                    first.types[*child as usize].representation(),
                    Type::Tuple { .. }
                ) {
                    assert!((*child as usize) < parent);
                }
            }
        }
    }
}

#[test]
fn tuple_field_move_retains_and_cleans_the_residual_aggregate() {
    let source = r#"
        struct Owner { value: &mut i64 }
        take_tuple(value: (Owner, i64)) -> Owner { value.0 }
        keep_copy(value: (Owner, i64)) -> i64 {
            let owner = value.0;
            value.1
        }
        main() -> { () }
    "#;
    let first = compile_source_to_phases("tuple-move.glorious", source).unwrap();
    let second = compile_source_to_phases("tuple-move.glorious", source).unwrap();
    verify(first.artifact.clone()).unwrap();
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    assert!(
        first
            .core
            .canonical_text()
            .contains("project field#0 copy=false")
    );
    assert!(first.mir.canonical_text().contains("ProjectMove"));
    assert!(
        first
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::ProjectMove { field: 0, .. }))
    );
    for name in ["take_tuple", "keep_copy"] {
        let function = first
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert!(
            first
                .artifact
                .cleanups
                .iter()
                .any(|cleanup| { cleanup.function == function && cleanup.registers.contains(&1) })
        );
    }
}

#[test]
fn tuple_field_move_rejects_overlap_whole_use_loans_and_nested_paths() {
    let cases = [
        (
            "tuple-move-twice",
            "struct Owner { value: &mut i64 } bad(value: (Owner, i64)) -> Owner { let first = value.0; value.0 } main() -> { () }",
        ),
        (
            "tuple-move-whole",
            "struct Owner { value: &mut i64 } bad(value: (Owner, i64)) -> (Owner, i64) { let first = value.0; value } main() -> { () }",
        ),
        (
            "tuple-move-borrowed",
            "struct Owner { value: &mut i64 } bad(value: (Owner, i64)) -> Owner { let borrowed = &value; let result = value.0; borrowed; result } main() -> { () }",
        ),
        (
            "tuple-move-nested",
            "struct Owner { value: &mut i64 } bad(value: ((Owner,), i64)) -> Owner { value.0.0 } main() -> { () }",
        ),
    ];
    for (name, source) in cases {
        let result = compile_source_to_bytecode(&format!("{name}.glorious"), source);
        assert!(result.is_err(), "{name} unexpectedly compiled");
        let errors = result.unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.code.is_some() && error.span.is_some()),
            "{name} did not produce a structured, spanned diagnostic: {errors:#?}"
        );
    }
}

#[test]
fn tuple_reference_field_move_is_a_valid_partial_deconstruction() {
    compile_source_to_bytecode(
        "tuple-move-reference.glorious",
        "select(value: (&mut i64, i64)) -> &mut i64 { value.0 } main() -> { () }",
    )
    .expect("moving the unique-reference field transfers it and disposes the zero-use residual");
}

#[test]
fn invalid_tuple_forms_and_ownership_have_structured_diagnostics() {
    let cases = [
        (
            "tuple-oob",
            "pair() -> (i64, i64) { (1, 2) } bad() -> i64 { pair().2 } main() -> { () }",
        ),
        (
            "tuple-named-field",
            "pair() -> (i64, i64) { (1, 2) } bad() -> i64 { pair().left } main() -> { () }",
        ),
        (
            "tuple-reference-escape",
            "pack(value: i64) -> (&i64,) { let borrowed = &value; (borrowed,) } main() -> { () }",
        ),
        (
            "tuple-malformed",
            "bad() -> (i64,) { (1,,) } main() -> { () }",
        ),
    ];
    for (name, source) in cases {
        let errors = compile_source_to_bytecode(&format!("{name}.glorious"), source).unwrap_err();
        assert!(!errors.is_empty(), "{name} unexpectedly compiled");
        assert!(
            errors.iter().any(|error| error.span.is_some()),
            "{name} lost its source span: {errors:?}"
        );
        assert!(
            errors.iter().any(|error| error.code.is_some()),
            "{name} did not produce a structured diagnostic code: {errors:?}"
        );
    }
}

#[test]
fn nested_ground_nominals_construct_project_pass_and_specialize() {
    let source = r#"
        struct Box<T> { value: T }
        struct Wrapper<T> { inner: Box<T> }
        enum Maybe<T> { None, Some(T) }
        type Nested<T> = Box<Box<T>>;
        make_inner() -> Box<i64> { Box { value: 42 } }
        make_outer() -> Box<Box<i64>> { Box { value: make_inner() } }
        make_alias() -> Nested<i64> { Box { value: make_inner() } }
        make_wrapper() -> Wrapper<i64> { Wrapper { inner: make_inner() } }
        make_maybe() -> Maybe<Box<Text>> { Maybe::Some(Box { value: "nested" }) }
        relay<T>(value: T) -> T { value }
        specialized() -> Box<Box<i64>> { relay(make_outer()) }
        answer() -> i64 { make_outer().value.value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("nested-ground.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified.clone()).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
    let function = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32
    };
    assert_eq!(
        Vm::new(verified.clone())
            .run(function("specialized"), vec![])
            .unwrap(),
        Vm::new(verified)
            .run(function("make_outer"), vec![])
            .unwrap()
    );
    let user_nominal_family = ["Box", "Wrapper", "Maybe"];
    for (parent, child) in phases
        .artifact
        .types
        .iter()
        .enumerate()
        .filter_map(|(parent, ty)| match ty.representation() {
            Type::Struct { name, fields, .. } if user_nominal_family.contains(&name.as_str()) => {
                fields.first().map(|field| (parent, field.ty))
            }
            Type::Enum { name, variants, .. } if user_nominal_family.contains(&name.as_str()) => {
                variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .next()
                    .map(|field| (parent, field.ty))
            }
            _ => None,
        })
        .filter(|(_, child)| *child as usize >= Type::predefined().len())
    {
        assert!(
            (child as usize) < parent,
            "child t{child} followed parent t{parent}"
        );
    }
}

#[test]
fn nested_ground_nominal_layouts_are_canonical_across_declaration_order() {
    let first = r#"
        struct Box<T> { value: T }
        struct Wrapper<T> { inner: Box<T> }
        enum Maybe<T> { None, Some(T) }
        outer(value: Box<Box<i64>>) -> Box<Box<i64>> { value }
        wrapped(value: Wrapper<Text>) -> Wrapper<Text> { value }
        optional(value: Maybe<Box<Text>>) -> Maybe<Box<Text>> { value }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        optional(value: Maybe<Box<Text>>) -> Maybe<Box<Text>> { value }
        wrapped(value: Wrapper<Text>) -> Wrapper<Text> { value }
        outer(value: Box<Box<i64>>) -> Box<Box<i64>> { value }
        enum Maybe<T> { None, Some(T) }
        struct Wrapper<T> { inner: Box<T> }
        struct Box<T> { value: T }
    "#;
    assert_eq!(
        compile_source_to_bytecode("nested-order.glorious", first)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("nested-order-reversed.glorious", reordered)
            .unwrap()
            .encode()
    );
}

#[test]
fn bounded_generic_tuple_fields_ground_nested_structural_layouts() {
    let source = r#"
        struct Packet { value: i64 }
        struct Wrapped<T> { value: (T, (T, i64)) }
        integer() -> Wrapped<i64> { Wrapped { value: (20, (21, 1)) } }
        packet() -> Wrapped<Packet> {
            Wrapped {
                value: (Packet { value: 22 }, (Packet { value: 23 }, 2))
            }
        }
        answer() -> i64 { integer().value.0 + packet().value.1.0.value }
        main() -> { answer(); () }
    "#;
    let reordered = r#"
        main() -> { answer(); () }
        answer() -> i64 { integer().value.0 + packet().value.1.0.value }
        packet() -> Wrapped<Packet> {
            Wrapped {
                value: (Packet { value: 22 }, (Packet { value: 23 }, 2))
            }
        }
        integer() -> Wrapped<i64> { Wrapped { value: (20, (21, 1)) } }
        struct Wrapped<T> { value: (T, (T, i64)) }
        struct Packet { value: i64 }
    "#;

    let phases = compile_source_to_phases("bounded-tuple-field.glorious", source).unwrap();
    let repeated = compile_source_to_phases("bounded-tuple-field.glorious", source).unwrap();
    let reordered =
        compile_source_to_phases("bounded-tuple-field-reordered.glorious", reordered).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(phases.artifact.encode(), reordered.artifact.encode());
    assert!(phases.core.canonical_text().contains("project"));
    assert!(phases.mir.canonical_text().contains("Project"));

    let wrapped = phases
        .artifact
        .types
        .iter()
        .filter(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Wrapped"))
        .collect::<Vec<_>>();
    assert_eq!(wrapped.len(), 2);
    for ty in wrapped {
        assert!(ty.claimed_duplicable());
        assert!(ty.claimed_zero_use_allowed());
        let Type::Struct { fields, copy, .. } = ty.representation() else {
            unreachable!()
        };
        assert!(*copy);
        let Type::Tuple { fields, copy } =
            phases.artifact.types[fields[0].ty as usize].representation()
        else {
            panic!("generic field did not lower to a tuple descriptor")
        };
        assert!(*copy);
        assert_eq!(fields.len(), 2);
        assert!(matches!(
            phases.artifact.types[fields[1] as usize].representation(),
            Type::Tuple { fields, copy: true } if fields.len() == 2
        ));
    }

    let bytes = phases.artifact.encode();
    let decoded = Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);
    let verified = verify(decoded).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(43)
    );
}

#[test]
fn bounded_generic_reference_fields_forward_with_exact_descriptors_and_use_flags() {
    let source = r#"
        struct Shared<T> { value: &T }
        struct Unique<T> { value: &mut T }
        forward_shared(value: Shared<i64>) -> Shared<i64> { value }
        forward_unique(value: Unique<i64>) -> Unique<i64> { value }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        forward_unique(value: Unique<i64>) -> Unique<i64> { value }
        forward_shared(value: Shared<i64>) -> Shared<i64> { value }
        struct Unique<T> { value: &mut T }
        struct Shared<T> { value: &T }
    "#;
    let phases = compile_source_to_phases("bounded-reference-field.glorious", source).unwrap();
    let descriptor = |name: &str| {
        phases
            .artifact
            .types
            .iter()
            .find(|ty| matches!(ty.representation(), Type::Struct { name: found, .. } if found == name))
            .unwrap()
    };
    let shared = descriptor("Shared");
    let unique = descriptor("Unique");
    let field_type = |ty: &Type| {
        let Type::Struct { fields, .. } = ty.representation() else {
            unreachable!()
        };
        &phases.artifact.types[fields[0].ty as usize]
    };
    assert!(matches!(
        field_type(shared).representation(),
        Type::RefShared {
            referent: grandiose_vm::I64
        }
    ));
    assert!(matches!(
        field_type(unique).representation(),
        Type::RefUnique {
            referent: grandiose_vm::I64
        }
    ));
    assert!(matches!(
        shared.representation(),
        Type::Struct { copy: true, .. }
    ));
    assert!(shared.claimed_duplicable());
    assert!(shared.claimed_zero_use_allowed());
    assert!(matches!(
        unique.representation(),
        Type::Struct { copy: false, .. }
    ));
    assert!(!unique.claimed_duplicable());
    assert!(unique.claimed_zero_use_allowed());

    let core = phases.core.canonical_text();
    assert!(core.contains("copy=true"));
    assert!(core.contains("copy=false"));
    let mir = phases.mir.canonical_text();
    assert!(mir.contains("Copy"));
    assert!(mir.contains("Move"));
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    assert_eq!(
        compile_source_to_bytecode("bounded-reference-field-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
    verify(phases.artifact).unwrap();
}

#[test]
fn generic_applications_nested_in_tuples_close_construct_project_and_execute() {
    let source = r#"
        struct Box<T> { value: T }
        struct Wrapped<T> { value: (Box<T>, (Box<T>,)) }
        struct Substituted<T> { value: (T,) }
        make() -> Wrapped<i64> {
            Wrapped { value: (Box { value: 20 }, (Box { value: 22 },)) }
        }
        make_substituted() -> Substituted<Box<i64>> {
            Substituted { value: (Box { value: 1 },) }
        }
        answer() -> i64 {
            let wrapped = make();
            wrapped.value.0.value
                + wrapped.value.1.0.value
                + make_substituted().value.0.value
        }
        main() -> { answer(); () }
    "#;
    let phases = compile_source_to_phases("nested-application-tuple.glorious", source).unwrap();
    let repeated = compile_source_to_phases("nested-application-tuple.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let wrapped = phases
        .artifact
        .types
        .iter()
        .find(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Wrapped"))
        .unwrap();
    let Type::Struct { fields, .. } = wrapped.representation() else {
        unreachable!()
    };
    let Type::Tuple {
        fields: tuple_fields,
        ..
    } = phases.artifact.types[fields[0].ty as usize].representation()
    else {
        panic!("nested application field did not lower to a tuple")
    };
    for boxed in [
        tuple_fields[0],
        match phases.artifact.types[tuple_fields[1] as usize].representation() {
            Type::Tuple { fields, .. } => fields[0],
            other => panic!("expected nested tuple, found {other:?}"),
        },
    ] {
        assert!(matches!(
            phases.artifact.types[boxed as usize].representation(),
            Type::Struct { name, fields, .. }
                if name == "Box" && fields.len() == 1 && fields[0].ty == grandiose_vm::I64
        ));
    }

    let bytes = phases.artifact.encode();
    let decoded = Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);
    let verified = verify(decoded).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(43)
    );

    let reordered = r#"
        main() -> { answer(); () }
        answer() -> i64 {
            let wrapped = make();
            wrapped.value.0.value
                + wrapped.value.1.0.value
                + make_substituted().value.0.value
        }
        make_substituted() -> Substituted<Box<i64>> {
            Substituted { value: (Box { value: 1 },) }
        }
        make() -> Wrapped<i64> {
            Wrapped { value: (Box { value: 20 }, (Box { value: 22 },)) }
        }
        struct Substituted<T> { value: (T,) }
        struct Wrapped<T> { value: (Box<T>, (Box<T>,)) }
        struct Box<T> { value: T }
    "#;
    assert_eq!(
        compile_source_to_bytecode("nested-application-tuple-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn generic_applications_under_references_close_exact_and_recursive_descriptors() {
    let source = r#"
        struct Box<T> { value: T }
        struct Shared<T> { value: &Box<T> }
        struct Unique<T> { value: &mut Box<T> }
        struct SharedArg<T> { value: &T }
        struct UniqueArg<T> { value: &mut T }
        struct Node<T> { value: T, next: &Node<T> }
        forward_shared(value: Shared<i64>) -> Shared<i64> { value }
        forward_unique(value: Unique<i64>) -> Unique<i64> { value }
        forward_shared_arg(value: SharedArg<Box<i64>>) -> SharedArg<Box<i64>> { value }
        forward_unique_arg(value: UniqueArg<Box<i64>>) -> UniqueArg<Box<i64>> { value }
        forward_node(value: Node<i64>) -> Node<i64> { value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("nested-application-reference.glorious", source).unwrap();
    let repeated =
        compile_source_to_phases("nested-application-reference.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let descriptor = |name: &str| {
        phases
            .artifact
            .types
            .iter()
            .position(|ty| matches!(ty.representation(), Type::Struct { name: found, .. } if found == name))
            .unwrap() as u32
    };
    let boxed = descriptor("Box");
    assert!(matches!(
        phases.artifact.types[boxed as usize].representation(),
        Type::Struct { fields, .. }
            if fields.len() == 1 && fields[0].ty == grandiose_vm::I64
    ));
    for (name, unique) in [
        ("Shared", false),
        ("Unique", true),
        ("SharedArg", false),
        ("UniqueArg", true),
    ] {
        let owner = descriptor(name);
        let Type::Struct { fields, .. } = phases.artifact.types[owner as usize].representation()
        else {
            unreachable!()
        };
        assert!(
            matches!(
                phases.artifact.types[fields[0].ty as usize].representation(),
                Type::RefUnique { referent } if unique && *referent == boxed
            ) || matches!(
                phases.artifact.types[fields[0].ty as usize].representation(),
                Type::RefShared { referent } if !unique && *referent == boxed
            )
        );
    }
    let node = descriptor("Node");
    let Type::Struct { fields, .. } = phases.artifact.types[node as usize].representation() else {
        unreachable!()
    };
    assert_eq!(fields[0].ty, grandiose_vm::I64);
    assert!(matches!(
        phases.artifact.types[fields[1].ty as usize].representation(),
        Type::RefShared { referent } if *referent == node
    ));

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    verify(phases.artifact).unwrap();
    let reordered = r#"
        main() -> { () }
        forward_node(value: Node<i64>) -> Node<i64> { value }
        forward_unique_arg(value: UniqueArg<Box<i64>>) -> UniqueArg<Box<i64>> { value }
        forward_shared_arg(value: SharedArg<Box<i64>>) -> SharedArg<Box<i64>> { value }
        forward_unique(value: Unique<i64>) -> Unique<i64> { value }
        forward_shared(value: Shared<i64>) -> Shared<i64> { value }
        struct Node<T> { value: T, next: &Node<T> }
        struct UniqueArg<T> { value: &mut T }
        struct SharedArg<T> { value: &T }
        struct Unique<T> { value: &mut Box<T> }
        struct Shared<T> { value: &Box<T> }
        struct Box<T> { value: T }
    "#;
    assert_eq!(
        compile_source_to_bytecode("nested-application-reference-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn borrowed_generic_parameter_permutation_closes_a_finite_descriptor_orbit() {
    let source = r#"
        struct Swap<A, B> { next: &Swap<B, A> }
        forward(value: Swap<i64, Text>) -> Swap<i64, Text> { value }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("borrowed-parameter-swap.glorious", source).unwrap();
    let swaps = artifact
        .types
        .iter()
        .enumerate()
        .filter_map(|(id, ty)| {
            matches!(ty.representation(), Type::Struct { name, .. } if name == "Swap")
                .then_some(id as u32)
        })
        .collect::<Vec<_>>();
    assert_eq!(swaps.len(), 2);
    for (index, owner) in swaps.iter().copied().enumerate() {
        let Type::Struct { fields, .. } = artifact.types[owner as usize].representation() else {
            unreachable!()
        };
        assert_eq!(fields.len(), 1);
        let Type::RefShared { referent } = artifact.types[fields[0].ty as usize].representation()
        else {
            panic!("Swap field did not lower to a shared reference")
        };
        assert_eq!(*referent, swaps[1 - index]);
        assert_ne!(*referent, owner);
    }

    let bytes = artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    verify(artifact).unwrap();

    let reordered = r#"
        main() -> { () }
        forward(value: Swap<i64, Text>) -> Swap<i64, Text> { value }
        struct Swap<A, B> { next: &Swap<B, A> }
    "#;
    assert_eq!(
        compile_source_to_bytecode("borrowed-parameter-swap-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn structural_generic_arguments_construct_forward_and_preserve_principal_use() {
    let source = r#"
        struct Box<T> { value: T }
        make() -> Box<(i64, Text)> { Box { value: (42, "tuple") } }
        forward_shared(value: Box<&i64>) -> Box<&i64> { value }
        forward_unique(value: Box<&mut i64>) -> Box<&mut i64> { value }
        forward_nested(value: Box<&(i64, Text)>) -> Box<&(i64, Text)> { value }
        forward_mixed(value: Box<(&i64, &mut i64)>) -> Box<(&i64, &mut i64)> { value }
        forward_unit(value: Box<Unit>) -> Box<Unit> { value }
        forward_empty(value: Box<()>) -> Box<()> { value }
        forward_never(value: Box<!>) -> Box<!> { value }
        answer() -> i64 { make().value.0 }
        main() -> { answer(); () }
    "#;
    let phases = compile_source_to_phases("structural-generic-arguments.glorious", source).unwrap();
    let repeated =
        compile_source_to_phases("structural-generic-arguments.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let boxes = phases
        .artifact
        .types
        .iter()
        .filter(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Box"))
        .collect::<Vec<_>>();
    assert_eq!(boxes.len(), 7);
    let field_type = |owner: &Type| {
        let Type::Struct { fields, .. } = owner.representation() else {
            unreachable!()
        };
        &phases.artifact.types[fields[0].ty as usize]
    };
    let shared = boxes
        .iter()
        .copied()
        .find(|owner| {
            matches!(
                field_type(owner).representation(),
                Type::RefShared {
                    referent: grandiose_vm::I64
                }
            )
        })
        .unwrap();
    let unique = boxes
        .iter()
        .copied()
        .find(|owner| {
            matches!(
                field_type(owner).representation(),
                Type::RefUnique {
                    referent: grandiose_vm::I64
                }
            )
        })
        .unwrap();
    assert!(shared.claimed_duplicable() && shared.claimed_zero_use_allowed());
    assert!(!unique.claimed_duplicable() && unique.claimed_zero_use_allowed());
    assert!(matches!(
        shared.representation(),
        Type::Struct { copy: true, .. }
    ));
    assert!(matches!(
        unique.representation(),
        Type::Struct { copy: false, .. }
    ));
    assert!(boxes.iter().any(|owner| {
        matches!(
            field_type(owner).representation(),
            Type::Tuple { fields, copy: true }
                if fields.len() == 2
                    && fields[0] == grandiose_vm::I64
                    && fields[1] == grandiose_vm::TEXT
        )
    }));
    let function_param = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    assert_eq!(
        function_param("forward_unit"),
        function_param("forward_empty")
    );
    assert!(matches!(
        field_type(&phases.artifact.types[function_param("forward_unit") as usize])
            .representation(),
        Type::Unit
    ));
    assert!(
        boxes
            .iter()
            .any(|owner| { matches!(field_type(owner).representation(), Type::Never) })
    );
    assert!(boxes.iter().any(|owner| {
        matches!(
            field_type(owner).representation(),
            Type::Tuple { fields, copy: false }
                if fields.len() == 2
                    && matches!(phases.artifact.types[fields[0] as usize].representation(), Type::RefShared { referent: grandiose_vm::I64 })
                    && matches!(phases.artifact.types[fields[1] as usize].representation(), Type::RefUnique { referent: grandiose_vm::I64 })
        )
    }));

    let bytes = phases.artifact.encode();
    let decoded = Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);
    let verified = verify(decoded).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );

    let reordered = r#"
        main() -> { answer(); () }
        answer() -> i64 { make().value.0 }
        forward_never(value: Box<!>) -> Box<!> { value }
        forward_empty(value: Box<()>) -> Box<()> { value }
        forward_unit(value: Box<Unit>) -> Box<Unit> { value }
        forward_mixed(value: Box<(&i64, &mut i64)>) -> Box<(&i64, &mut i64)> { value }
        forward_nested(value: Box<&(i64, Text)>) -> Box<&(i64, Text)> { value }
        forward_unique(value: Box<&mut i64>) -> Box<&mut i64> { value }
        forward_shared(value: Box<&i64>) -> Box<&i64> { value }
        make() -> Box<(i64, Text)> { Box { value: (42, "tuple") } }
        struct Box<T> { value: T }
    "#;
    assert_eq!(
        compile_source_to_bytecode("structural-generic-arguments-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn structural_generic_enum_arguments_construct_and_forward() {
    let source = r#"
        enum Maybe<T> { None, Some(T) }
        make() -> Maybe<(i64, Text)> { Maybe::Some((41, "enum")) }
        forward_shared(value: Maybe<&i64>) -> Maybe<&i64> { value }
        forward_unique(value: Maybe<&mut (i64, Text)>) -> Maybe<&mut (i64, Text)> { value }
        forward_never(value: Maybe<!>) -> Maybe<!> { value }
        main() -> { make(); () }
    "#;
    let phases =
        compile_source_to_phases("structural-generic-enum-arguments.glorious", source).unwrap();
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    let make = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "make")
        .unwrap() as u32;
    let maybe = phases.artifact.functions[make as usize].return_type;
    let Type::Enum { variants, .. } = phases.artifact.types[maybe as usize].representation() else {
        panic!("make did not return a grounded Maybe descriptor")
    };
    let tuple = variants[1].fields[0].ty;
    assert_eq!(
        Vm::new(verified).run(make, vec![]).unwrap(),
        Value::aggregate_with_variant(
            maybe,
            Some(1),
            [Value::aggregate(
                tuple,
                [Value::I64(41), Value::Text("enum".into())]
            )]
        )
    );
    let reordered = r#"
        main() -> { make(); () }
        forward_never(value: Maybe<!>) -> Maybe<!> { value }
        forward_unique(value: Maybe<&mut (i64, Text)>) -> Maybe<&mut (i64, Text)> { value }
        forward_shared(value: Maybe<&i64>) -> Maybe<&i64> { value }
        make() -> Maybe<(i64, Text)> { Maybe::Some((41, "enum")) }
        enum Maybe<T> { None, Some(T) }
    "#;
    assert_eq!(
        compile_source_to_bytecode(
            "structural-generic-enum-arguments-reordered.glorious",
            reordered
        )
        .unwrap()
        .encode(),
        bytes
    );
}

#[test]
fn monomorphic_enum_payload_roots_a_structural_generic_nominal_instance() {
    let source = r#"
        struct Box<T> { value: T }
        enum Envelope { Empty, Packed(Box<(i64, Text)>) }
        forward(value: Envelope) -> Envelope { value }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("enum-payload-generic-root.glorious", source).unwrap();
    let boxed = artifact
        .types
        .iter()
        .position(|ty| {
            let Type::Struct { name, fields, .. } = ty.representation() else {
                return false;
            };
            if name != "Box" || fields.len() != 1 {
                return false;
            }
            matches!(
                artifact.types[fields[0].ty as usize].representation(),
                Type::Tuple { fields, .. }
                    if fields.len() == 2
                        && fields[0] == grandiose_vm::I64
                        && fields[1] == grandiose_vm::TEXT
            )
        })
        .expect("Envelope payload did not root Box<(i64, Text)>") as u32;
    let envelope = artifact
        .types
        .iter()
        .find(|ty| matches!(ty.representation(), Type::Enum { name, .. } if name == "Envelope"))
        .unwrap();
    assert!(matches!(
        envelope.representation(),
        Type::Enum { variants, .. }
            if variants[0].fields.is_empty()
                && variants[1].fields.len() == 1
                && variants[1].fields[0].ty == boxed
    ));

    let bytes = artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    verify(artifact).unwrap();

    let reordered = r#"
        main() -> { () }
        forward(value: Envelope) -> Envelope { value }
        enum Envelope { Empty, Packed(Box<(i64, Text)>) }
        struct Box<T> { value: T }
    "#;
    assert_eq!(
        compile_source_to_bytecode("enum-payload-generic-root-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn owned_recursive_and_expanding_borrowed_generic_families_are_rejected() {
    let cases = [
        (
            "direct-owned",
            "struct Direct<T> { next: Direct<T> } main() -> { () }",
        ),
        (
            "tuple-owned",
            "struct Tupled<T> { next: (Tupled<T>,) } main() -> { () }",
        ),
        (
            "expanding-borrowed",
            "struct Box<T> { value: T } struct Node<T> { next: &Node<Box<T>> } forward(value: Node<i64>) -> Node<i64> { value } main() -> { () }",
        ),
    ];
    for (name, source) in cases {
        let errors = compile_source_to_bytecode(&format!("{name}.glorious"), source).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.code.is_some() && error.span.is_some()),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn bounded_generic_enum_payloads_ground_tuple_and_reference_wrappers() {
    let source = r#"
        enum TuplePayload<T> { Value((T, (T,))) }
        enum SharedPayload<T> { Value(&T) }
        enum UniquePayload<T> { Value(&mut T) }
        make() -> TuplePayload<i64> { TuplePayload::Value((41, (1,))) }
        forward_shared(value: SharedPayload<i64>) -> SharedPayload<i64> { value }
        forward_unique(value: UniquePayload<i64>) -> UniquePayload<i64> { value }
        main() -> { make(); () }
    "#;
    let reordered = r#"
        main() -> { make(); () }
        forward_unique(value: UniquePayload<i64>) -> UniquePayload<i64> { value }
        forward_shared(value: SharedPayload<i64>) -> SharedPayload<i64> { value }
        make() -> TuplePayload<i64> { TuplePayload::Value((41, (1,))) }
        enum UniquePayload<T> { Value(&mut T) }
        enum SharedPayload<T> { Value(&T) }
        enum TuplePayload<T> { Value((T, (T,))) }
    "#;
    let phases = compile_source_to_phases("bounded-enum-payload.glorious", source).unwrap();
    let descriptor = |name: &str| {
        phases
            .artifact
            .types
            .iter()
            .find(
                |ty| matches!(ty.representation(), Type::Enum { name: found, .. } if found == name),
            )
            .unwrap()
    };
    let payload = |name: &str| {
        let ty = descriptor(name);
        let Type::Enum { variants, .. } = ty.representation() else {
            unreachable!()
        };
        &phases.artifact.types[variants[0].fields[0].ty as usize]
    };
    assert!(matches!(
        payload("TuplePayload").representation(),
        Type::Tuple { fields, .. } if fields.len() == 2
    ));
    assert!(matches!(
        payload("SharedPayload").representation(),
        Type::RefShared {
            referent: grandiose_vm::I64
        }
    ));
    assert!(matches!(
        payload("UniquePayload").representation(),
        Type::RefUnique {
            referent: grandiose_vm::I64
        }
    ));
    let tuple = descriptor("TuplePayload");
    let shared = descriptor("SharedPayload");
    let unique = descriptor("UniquePayload");
    assert!(matches!(
        tuple.representation(),
        Type::Enum { copy: true, .. }
    ));
    assert!(tuple.claimed_duplicable() && tuple.claimed_zero_use_allowed());
    assert!(matches!(
        shared.representation(),
        Type::Enum { copy: true, .. }
    ));
    assert!(shared.claimed_duplicable() && shared.claimed_zero_use_allowed());
    assert!(matches!(
        unique.representation(),
        Type::Enum { copy: false, .. }
    ));
    assert!(!unique.claimed_duplicable() && unique.claimed_zero_use_allowed());
    let bytes = phases.artifact.encode();
    assert_eq!(
        compile_source_to_bytecode("bounded-enum-payload-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
    let verified = verify(Artifact::decode(&bytes).unwrap()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(phases.artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );
}

#[test]
fn callable_values_in_generic_aggregates_remain_structured_until_grounded() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        struct Box<T> { value: T }
        pack<F, R>(body: F) -> Box<F> where F: Fn<(), Output=R> {
            Box { value: body }
        }
        run() -> i64 {
            let left_ticket = Ticket { value: 7 };
            let right_ticket = Ticket { value: 35 };
            let left_box = pack({ => {
                let Ticket { value } = move left_ticket;
                value
            }});
            let right_box = pack({ => {
                let Ticket { value } = move right_ticket;
                value
            }});
            let Box { value: left } = left_box;
            let Box { value: right } = right_box;
            left() + right()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("callable-generic-argument.glorious", source).unwrap();
    let exact_boxes = phases
        .artifact
        .types
        .iter()
        .filter(|ty| {
            matches!(ty.representation(), Type::Struct { name, .. } if name.starts_with("Box$closure$"))
        })
        .count();
    assert_eq!(
        exact_boxes, 2,
        "same-shape closures retain distinct Box identities"
    );
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn generic_box_of_relevant_copy_closure_preserves_repeated_use_capability() {
    let source = r#"
        struct Relevant { value: i64 }
        impl Use<[1,infinity]> for Relevant {}
        struct Box<T> { value: T }
        run() -> i64 {
            let relevant = Relevant { value: 21 };
            let observe = { => relevant.value };
            let Relevant { value: _ } = move relevant;
            let boxed = Box { value: move observe };
            let Box { value: restored } = move boxed;
            restored() + move restored()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("relevant-copy-closure-box.glorious", source).unwrap();
    let descriptor = phases
        .artifact
        .types
        .iter()
        .find(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name.starts_with("Box$closure$")))
        .expect("ground Box<closure> descriptor");
    assert!(descriptor.claimed_duplicable());
    assert!(!descriptor.claimed_zero_use_allowed());
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn shared_closure_can_copy_a_whole_relevant_capture_into_a_consumer() {
    let source = r#"
        struct Relevant { value: i64 }
        impl Use<[1,infinity]> for Relevant {}
        consume(value: Relevant) -> i64 {
            let Relevant { value } = move value;
            value
        }
        run() -> i64 {
            let relevant = Relevant { value: 21 };
            let observe = { => consume(relevant) };
            let Relevant { value: _ } = move relevant;
            observe() + move observe()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("whole-relevant-copy-closure.glorious", source).unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn generic_box_of_owned_closure_preserves_exactly_one_use() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        struct Box<T> { value: T }
        run() -> i64 {
            let ticket = Ticket { value: 42 };
            let consume = { => { let Ticket { value } = move ticket; value } };
            let boxed = Box { value: consume };
            let Box { value: restored } = boxed;
            restored()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("owned-closure-box.glorious", source).unwrap();
    let descriptor = phases
        .artifact
        .types
        .iter()
        .find(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name.starts_with("Box$closure$")))
        .expect("ground Box<closure> descriptor");
    assert!(!descriptor.claimed_duplicable());
    assert!(!descriptor.claimed_zero_use_allowed());
    let run = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(run, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn generic_box_of_affine_owned_closure_may_be_abandoned() {
    let source = r#"
        struct Permit { value: i64 }
        impl Use<[0,1]> for Permit {}
        struct Box<T> { value: T }
        run() -> {
            let permit = Permit { value: 42 };
            let consume = { => { let Permit { value: _ } = move permit; () } };
            let boxed = Box { value: consume };
            ()
        }
        main() -> { run() }
    "#;
    let phases = compile_source_to_phases("zero-use-closure-box.glorious", source).unwrap();
    let descriptor = phases
        .artifact
        .types
        .iter()
        .find(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name.starts_with("Box$closure$")))
        .expect("ground Box<closure> descriptor");
    assert!(!descriptor.claimed_duplicable());
    assert!(descriptor.claimed_zero_use_allowed());
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(phases.artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );
}

#[test]
fn infinite_or_out_of_boundary_nested_nominal_layouts_are_rejected() {
    let cases = [
        (
            "direct-recursion",
            "struct Loop<T> { next: Loop<T> } main() -> { () }",
        ),
        (
            "growing-recursion",
            "struct Box<T> { value: T } struct Grow<T> { next: Grow<Box<T>> } main() -> { () }",
        ),
        (
            "mutual-recursion",
            "struct A<T> { b: B<T> } struct B<T> { a: A<T> } main() -> { () }",
        ),
        (
            "enum-recursion",
            "enum Loop<T> { Next(Loop<T>) } main() -> { () }",
        ),
        (
            "growing-borrowed-tuple-argument",
            "struct Grow<T> { next: &Grow<(T,)> } forward(value: Grow<i64>) -> Grow<i64> { value } main() -> { () }",
        ),
    ];
    for (name, source) in cases {
        let errors = compile_source_to_bytecode(&format!("{name}.glorious"), source).unwrap_err();
        assert!(!errors.is_empty(), "{name} unexpectedly compiled");
        assert!(
            errors.iter().any(|error| error.span.is_some()),
            "{name} lost its source span: {errors:?}"
        );
        assert!(
            errors.iter().any(|error| error.code.is_some()),
            "{name} did not produce a structured diagnostic code: {errors:?}"
        );
    }
}

#[test]
fn grounded_generic_aliases_are_transparent_through_calls_and_nominal_instances() {
    let source = r#"
        struct Box<T> { value: T }
        enum Maybe<T> { None, Some(T) }
        struct Holder { value: Identity<i64> }
        type Identity<T> = T;
        type Integer<T> = i64;
        type Boxed<T> = Box<T>;
        type Optional<T> = Maybe<T>;
        type Existing<T> = Holder;
        relay<T>(value: Identity<T>) -> T { value }
        scalar(value: Integer<Text>) -> i64 { value }
        make_box() -> Boxed<i64> { Box { value: 42 } }
        make_optional() -> Optional<i64> { Maybe::Some(42) }
        make_holder() -> Holder { Holder { value: 42 } }
        make_existing() -> Existing<Text> { Holder { value: 42 } }
        answer() -> i64 { scalar(relay(make_box().value)) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-alias.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified.clone()).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
    let maybe = phases
        .artifact
        .types
        .iter()
        .position(|ty| matches!(ty.representation(), Type::Enum { name, .. } if name == "Maybe"))
        .unwrap() as u32;
    let make_optional = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "make_optional")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(make_optional, vec![]).unwrap(),
        Value::aggregate_with_variant(maybe, Some(1), [Value::I64(42)])
    );
    assert_eq!(
        phases
            .artifact
            .types
            .iter()
            .filter(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Box"))
            .count(),
        1
    );
    assert_eq!(
        phases
            .artifact
            .types
            .iter()
            .filter(|ty| matches!(ty.representation(), Type::Enum { name, .. } if name == "Maybe"))
            .count(),
        1
    );
    assert!(!phases.artifact.types.iter().any(|ty| matches!(
        ty.representation(),
        Type::Struct { name, .. } | Type::Enum { name, .. }
            if matches!(name.as_str(), "Identity" | "Integer" | "Boxed" | "Optional")
    )));
}

#[test]
fn grounded_generic_alias_normalization_is_canonical_and_request_free() {
    let baseline = "main() -> { () }";
    let dead = "type Identity<T> = T; main() -> { () }";
    assert_eq!(
        compile_source_to_bytecode("alias-baseline.glorious", baseline)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("alias-dead.glorious", dead)
            .unwrap()
            .encode()
    );
    let first = r#"
        struct Box<T> { value: T }
        type Wrapped<T> = Box<T>;
        make() -> Wrapped<i64> { Box { value: 42 } }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        make() -> Wrapped<i64> { Box { value: 42 } }
        type Wrapped<T> = Box<T>;
        struct Box<T> { value: T }
    "#;
    assert_eq!(
        compile_source_to_bytecode("alias-order.glorious", first)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("alias-order-reversed.glorious", reordered)
            .unwrap()
            .encode()
    );
}

#[test]
fn generic_aliases_are_transparent_in_use_and_drop_heads() {
    let source = r#"
        struct AliasBox<T> { value: T }
        type AliasWrapped<T> = AliasBox<T>;
        impl<T> Use<[0,1]> for AliasWrapped<T> where T: Use<[0,1]> {}
        impl<T> Drop for AliasWrapped<T> {
            drop(&mut self) -> { self.value; () }
        }
        make() -> AliasWrapped<i64> { AliasBox { value: 42 } }
        main() -> { let value = make(); () }
    "#;
    let artifact = compile_raw_source("alias-use-drop-head.glorious", source)
        .unwrap_or_else(|diagnostics| panic!("{diagnostics:#?}"));
    let boxed = artifact
        .types
        .iter()
        .position(|ty| {
            matches!(ty.representation(), Type::Struct { name, fields, .. }
                if name == "AliasBox" && fields.len() == 1 && fields[0].ty == grandiose_vm::I64)
        })
        .expect("missing AliasBox<i64>") as u32;
    assert!(artifact.drop_glue.iter().any(|glue| glue.ty == boxed));
    let verified = verify(artifact).unwrap();
    let entry = verified.artifact().entry_function.unwrap();
    Vm::new(verified).run(entry, vec![]).unwrap();

    let duplicate = r#"
        struct AliasBox<T> { value: T }
        type AliasWrapped<T> = AliasBox<T>;
        impl<T> Drop for AliasBox<T> { drop(&mut self) -> { () } }
        impl<T> Drop for AliasWrapped<T> { drop(&mut self) -> { () } }
        main() -> { () }
    "#;
    let diagnostics = compile_raw_source("alias-duplicate-drop-head.glorious", duplicate)
        .expect_err("an alias installed a second Drop hook on one nominal head");
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code.as_deref() == Some("G1TR001")
                && diagnostic
                    .message
                    .contains("overlapping implementations of `Drop`")
        }),
        "{diagnostics:#?}"
    );
}

#[test]
fn unsupported_generic_alias_forms_are_rejected_with_source_spans() {
    let cases = [
        (
            "alias-bare",
            "type LocalIdentity<T> = T; read(value: LocalIdentity) -> { () } main() -> { () }",
        ),
        (
            "alias-wrong-arity",
            "type LocalIdentity<T> = T; read(value: LocalIdentity<i64, Text>) -> { () } main() -> { () }",
        ),
        (
            "alias-cycle",
            "type A<T> = B<T>; type B<T> = A<T>; main() -> { () }",
        ),
        (
            "alias-unresolved-target",
            "type Bad<T> = Missing; main() -> { () }",
        ),
        (
            "alias-reference-target",
            "type Ref<T> = &T; main() -> { () }",
        ),
    ];
    for (name, source) in cases {
        let errors = compile_source_to_bytecode(&format!("{name}.glorious"), source).unwrap_err();
        assert!(!errors.is_empty(), "{name} unexpectedly compiled");
        assert!(
            errors.iter().any(|error| error.span.is_some()),
            "{name} did not preserve a source span: {errors:?}"
        );
        assert!(
            errors.iter().any(|error| error.code.is_some()),
            "{name} did not produce a structured diagnostic code: {errors:?}"
        );
    }
    compile_source_to_bytecode(
        "alias-in-alias.glorious",
        "type LocalIdentity<T> = T; type Concrete = LocalIdentity<i64>; read(value: Concrete) -> i64 { value } main() -> { () }",
    )
    .unwrap();
}

#[test]
fn grounded_generic_struct_instances_construct_project_and_specialize() {
    let source = r#"
        struct Box<T> { value: T }
        make() -> Box<i64> { Box { value: 42 } }
        read(value: Box<i64>) -> i64 { value.value }
        generic_read<T>(value: Box<T>) -> T { value.value }
        direct() -> i64 { read(make()) }
        specialized() -> i64 { generic_read(make()) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-struct.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    for name in ["direct", "specialized"] {
        let id = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(id, vec![]).unwrap(),
            Value::I64(42)
        );
    }
    let boxes = phases
        .artifact
        .types
        .iter()
        .filter(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Box"))
        .collect::<Vec<_>>();
    assert_eq!(boxes.len(), 1);
}

#[test]
fn grounded_generic_enum_instances_construct_call_and_specialize() {
    let source = r#"
        enum Maybe<T> { None, Some(T) }
        make() -> Maybe<i64> { Maybe::Some(42) }
        empty() -> Maybe<i64> { Maybe::None }
        relay<T>(value: Maybe<T>) -> Maybe<T> { value }
        id<T>(value: T) -> T { value }
        inferred() -> Maybe<i64> { id(Maybe::Some(42)) }
        specialized() -> Maybe<i64> { relay(make()) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-enum.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let maybe = phases
        .artifact
        .types
        .iter()
        .position(|ty| matches!(ty.representation(), Type::Enum { name, .. } if name == "Maybe"))
        .unwrap() as u32;
    let run = |name: &str| {
        let id = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        Vm::new(verified.clone()).run(id, vec![]).unwrap()
    };
    assert_eq!(
        run("empty"),
        Value::aggregate_with_variant(maybe, Some(0), [])
    );
    assert_eq!(
        run("specialized"),
        Value::aggregate_with_variant(maybe, Some(1), [Value::I64(42)])
    );
    assert_eq!(
        run("inferred"),
        Value::aggregate_with_variant(maybe, Some(1), [Value::I64(42)])
    );
}

#[test]
fn grounded_generic_enum_instances_are_deterministic_and_preserve_monomorphic_ids() {
    let baseline = r#"
        enum Existing { Empty, Value(i64) }
        make() -> Existing { Existing::Value(42) }
        main() -> { () }
    "#;
    let dead = r#"
        enum Maybe<T> { None, Some(T) }
        enum Existing { Empty, Value(i64) }
        make() -> Existing { Existing::Value(42) }
        main() -> { () }
    "#;
    assert_eq!(
        compile_source_to_bytecode("enum-baseline.glorious", baseline)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("enum-dead.glorious", dead)
            .unwrap()
            .encode()
    );
    let first = r#"
        struct Packet { value: i64 }
        enum Maybe<T> { None, Some(T) }
        integer(value: Maybe<i64>) -> Maybe<i64> { value }
        text(value: Maybe<Text>) -> Maybe<Text> { value }
        packet(value: Maybe<Packet>) -> Maybe<Packet> { value }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        packet(value: Maybe<Packet>) -> Maybe<Packet> { value }
        text(value: Maybe<Text>) -> Maybe<Text> { value }
        integer(value: Maybe<i64>) -> Maybe<i64> { value }
        enum Maybe<T> { None, Some(T) }
        struct Packet { value: i64 }
    "#;
    let first = compile_source_to_bytecode("enum-instances.glorious", first).unwrap();
    let reordered =
        compile_source_to_bytecode("enum-instances-reordered.glorious", reordered).unwrap();
    assert_eq!(first.encode(), reordered.encode());
    let packet = nominal_type_id(&first, "Packet");
    let maybe_instances = first
        .types
        .iter()
        .enumerate()
        .filter_map(|(id, ty)| {
            matches!(ty.representation(), Type::Enum { name, .. } if name == "Maybe")
                .then_some(id as u32)
        })
        .collect::<Vec<_>>();
    assert!(
        maybe_instances.iter().all(|instance| packet < *instance),
        "ground generic instances {maybe_instances:?} must not renumber monomorphic Packet r{packet}"
    );
    assert_eq!(
        first
            .types
            .iter()
            .filter(|ty| matches!(ty.representation(), Type::Enum { name, .. } if name == "Maybe"))
            .count(),
        3
    );
}

#[test]
fn expected_context_infers_generic_nominal_construction_across_calls_and_nesting() {
    let source = r#"
        struct Box<T> { value: T }
        enum Maybe<T> { None, Some(T) }
        enum Phantom<T> { Value(i64) }
        id<T>(value: T) -> T { value }
        accept_box(value: Box<i64>) -> Box<i64> { value }
        accept_maybe(value: Maybe<i64>) -> Maybe<i64> { value }
        accept_phantom(value: Phantom<i64>) -> Phantom<i64> { value }
        return_box() -> Box<i64> { Box { value: 42 } }
        pass_box() -> Box<i64> { accept_box(Box { value: 42 }) }
        id_box() -> Box<i64> { id(Box { value: 42 }) }
        let_box_answer() -> i64 {
            let value = Box { value: 42 };
            value.value
        }
        return_none() -> Maybe<i64> { Maybe::None }
        pass_none() -> Maybe<i64> { accept_maybe(Maybe::None) }
        id_none() -> Maybe<i64> { id(Maybe::None) }
        return_phantom() -> Phantom<i64> { Phantom::Value(42) }
        pass_phantom() -> Phantom<i64> { accept_phantom(Phantom::Value(42)) }
        id_phantom() -> Phantom<i64> { id(Phantom::Value(42)) }
        nested_box() -> Box<Box<i64>> {
            Box { value: Box { value: 42 } }
        }
        nested_none() -> Box<Maybe<i64>> {
            Box { value: Maybe::None }
        }
        main() -> {
            return_box(); pass_box(); id_box(); let_box_answer();
            return_none(); pass_none(); id_none();
            return_phantom(); pass_phantom(); id_phantom();
            nested_box(); nested_none(); ()
        }
    "#;
    let phases =
        compile_source_to_phases("expected-generic-construction.glorious", source).unwrap();
    let repeated =
        compile_source_to_phases("expected-generic-construction.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let maybe = phases
        .artifact
        .types
        .iter()
        .position(|ty| matches!(ty.representation(), Type::Enum { name, .. } if name == "Maybe"))
        .unwrap() as u32;
    let phantom = phases
        .artifact
        .types
        .iter()
        .position(|ty| matches!(ty.representation(), Type::Enum { name, .. } if name == "Phantom"))
        .unwrap() as u32;
    let boxes = phases
        .artifact
        .types
        .iter()
        .enumerate()
        .filter_map(|(id, ty)| {
            matches!(ty.representation(), Type::Struct { name, .. } if name == "Box")
                .then_some(id as u32)
        })
        .collect::<Vec<_>>();
    assert_eq!(boxes.len(), 3);
    let box_with = |field_type| {
        boxes
            .iter()
            .copied()
            .find(|id| {
                matches!(
                    phases.artifact.types[*id as usize].representation(),
                    Type::Struct { fields, .. }
                        if fields.len() == 1 && fields[0].ty == field_type
                )
            })
            .unwrap()
    };
    let boxed_i64 = box_with(grandiose_vm::I64);
    let boxed_box = box_with(boxed_i64);
    let boxed_maybe = box_with(maybe);

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    let run = |name: &str| {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        Vm::new(verified.clone()).run(function, vec![]).unwrap()
    };
    let boxed_value = Value::aggregate(boxed_i64, [Value::I64(42)]);
    for name in ["return_box", "pass_box", "id_box"] {
        assert_eq!(run(name), boxed_value, "{name}");
    }
    assert_eq!(run("let_box_answer"), Value::I64(42));
    let none = Value::aggregate_with_variant(maybe, Some(0), []);
    for name in ["return_none", "pass_none", "id_none"] {
        assert_eq!(run(name), none, "{name}");
    }
    let phantom_value = Value::aggregate_with_variant(phantom, Some(0), [Value::I64(42)]);
    for name in ["return_phantom", "pass_phantom", "id_phantom"] {
        assert_eq!(run(name), phantom_value, "{name}");
    }
    assert_eq!(
        run("nested_box"),
        Value::aggregate(boxed_box, [boxed_value])
    );
    assert_eq!(run("nested_none"), Value::aggregate(boxed_maybe, [none]));

    let reordered = r#"
        main() -> {
            return_box(); pass_box(); id_box(); let_box_answer();
            return_none(); pass_none(); id_none();
            return_phantom(); pass_phantom(); id_phantom();
            nested_box(); nested_none(); ()
        }
        nested_none() -> Box<Maybe<i64>> { Box { value: Maybe::None } }
        nested_box() -> Box<Box<i64>> { Box { value: Box { value: 42 } } }
        id_phantom() -> Phantom<i64> { id(Phantom::Value(42)) }
        pass_phantom() -> Phantom<i64> { accept_phantom(Phantom::Value(42)) }
        return_phantom() -> Phantom<i64> { Phantom::Value(42) }
        id_none() -> Maybe<i64> { id(Maybe::None) }
        pass_none() -> Maybe<i64> { accept_maybe(Maybe::None) }
        return_none() -> Maybe<i64> { Maybe::None }
        let_box_answer() -> i64 { let value = Box { value: 42 }; value.value }
        id_box() -> Box<i64> { id(Box { value: 42 }) }
        pass_box() -> Box<i64> { accept_box(Box { value: 42 }) }
        return_box() -> Box<i64> { Box { value: 42 } }
        accept_phantom(value: Phantom<i64>) -> Phantom<i64> { value }
        accept_maybe(value: Maybe<i64>) -> Maybe<i64> { value }
        accept_box(value: Box<i64>) -> Box<i64> { value }
        id<T>(value: T) -> T { value }
        enum Phantom<T> { Value(i64) }
        enum Maybe<T> { None, Some(T) }
        struct Box<T> { value: T }
    "#;
    assert_eq!(
        compile_source_to_bytecode(
            "expected-generic-construction-reordered.glorious",
            reordered
        )
        .unwrap()
        .encode(),
        bytes
    );
}

#[test]
fn later_call_arguments_infer_earlier_context_dependent_generic_constructors() {
    let source = r#"
        enum Phantom<T> { None }
        select<T>(shape: Phantom<T>, value: T) -> T { value }
        select_reversed<T>(value: T, shape: Phantom<T>) -> T { value }
        same<T>(left: T, right: T) -> T { left }
        first() -> i64 {
            let inferred = select(Phantom::None, 42);
            inferred
        }
        second() -> i64 {
            let inferred = select_reversed(42, Phantom::None);
            inferred
        }
        concrete_beats_default(value: u32) -> u32 {
            let inferred = same(1, value);
            inferred
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("argument-order-inference.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    for name in ["first", "second"] {
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(42)
        );
    }
    assert!(artifact.functions.iter().any(|function| {
        function.name.starts_with("$specialization$same#")
            && function.params == [grandiose_vm::U32, grandiose_vm::U32]
            && function.return_type == grandiose_vm::U32
    }));

    let ambiguous = r#"
        enum Phantom<T> { None }
        choose<T, U>(left: Phantom<T>, right: Phantom<U>) -> i64 { 0 }
        bad() -> i64 { let value = choose(Phantom::None, Phantom::None); value }
        main() -> { () }
    "#;
    let diagnostics =
        compile_source_to_bytecode("argument-order-ambiguous.glorious", ambiguous).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code.is_some()
                && diagnostic.span.is_some()
                && diagnostic.message.contains("ambiguous")
        }),
        "{diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.as_deref() != Some("G1BC999"))
    );
}

#[test]
fn ordinary_generic_call_islands_propagate_symbolic_constraints_deterministically() {
    let source = r#"
        pick<T, U>(first: T, middle: U, last: T) -> T { first }
        relay<A, B>(first: A, middle: B) -> A {
            pick(first, middle, first)
        }
        relay_reordered<A, B>(middle: B, first: A) -> A {
            pick(first, middle, first)
        }
        first() -> i64 { relay(42, "marker") }
        second() -> i64 { relay_reordered("marker", 42) }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("symbolic-call-island.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    for name in ["first", "second"] {
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(42),
            "{name}"
        );
    }

    let conflicting = r#"
        pick<T, U>(first: T, middle: U, last: T) -> T { first }
        bad<A, B>(first: A, middle: B) -> A {
            pick(first, middle, middle)
        }
        main() -> { bad(42, "marker"); () }
    "#;
    let diagnostics =
        compile_source_to_bytecode("symbolic-call-island-conflict.glorious", conflicting)
            .unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code.is_some()
                && diagnostic.span.is_some()
                && diagnostic.message.contains("ambiguous")
        }),
        "{diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.as_deref() != Some("G1BC999"))
    );
}

#[test]
fn unsupported_generic_enum_shapes_are_rejected_with_source_spans() {
    let cases = [
        (
            "enum-bare",
            "enum Maybe<T> { None, Some(T) }\nread(value: Maybe) -> { () }\nmain() -> { () }",
        ),
        (
            "enum-wrong-arity",
            "enum Maybe<T> { None, Some(T) }\nread(value: Maybe<i64, Text>) -> { () }\nmain() -> { () }",
        ),
        (
            "enum-recursive",
            "enum Loop<T> { Next(Loop<T>) }\nmain() -> { () }",
        ),
        (
            "enum-no-context-payloadless",
            "enum Maybe<T> { None, Some(T) }\nvalue() -> { let x = Maybe::None; () }\nmain() -> { () }",
        ),
        (
            "enum-unresolved-phantom",
            "enum Phantom<T> { Value(i64) }\nid<T>(value: T) -> T { value }\nvalue() -> { let x = id(Phantom::Value(42)); () }\nmain() -> { () }",
        ),
    ];
    for (name, source) in cases {
        let errors = compile_source_to_bytecode(&format!("{name}.glorious"), source).unwrap_err();
        assert!(!errors.is_empty(), "{name} unexpectedly compiled");
        assert!(
            errors.iter().any(|error| error.span.is_some()),
            "{name} did not preserve a source span: {errors:?}"
        );
        assert!(
            errors.iter().any(|error| error.code.is_some()),
            "{name} did not produce a structured diagnostic code: {errors:?}"
        );
    }
}

#[test]
fn grounded_generic_struct_instances_are_deterministic_and_do_not_renumber_monomorphic_types() {
    let baseline = r#"
        struct Packet { value: i64 }
        packet() -> Packet { Packet { value: 42 } }
        main() -> { () }
    "#;
    let with_dead_template = r#"
        struct Box<T> { value: T }
        struct Packet { value: i64 }
        packet() -> Packet { Packet { value: 42 } }
        main() -> { () }
    "#;
    assert_eq!(
        compile_source_to_bytecode("baseline.glorious", baseline)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("dead-template.glorious", with_dead_template)
            .unwrap()
            .encode()
    );

    let first = r#"
        struct Packet { value: i64 }
        struct Box<T> { value: T }
        integer(value: Box<i64>) -> i64 { value.value }
        text(value: Box<Text>) -> Text { value.value }
        packet(value: Box<Packet>) -> Packet { value.value }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        packet(value: Box<Packet>) -> Packet { value.value }
        text(value: Box<Text>) -> Text { value.value }
        integer(value: Box<i64>) -> i64 { value.value }
        struct Box<T> { value: T }
        struct Packet { value: i64 }
    "#;
    let first = compile_source_to_bytecode("instances.glorious", first).unwrap();
    let reordered = compile_source_to_bytecode("instances-reordered.glorious", reordered).unwrap();
    assert_eq!(first.encode(), reordered.encode());
    let packet = nominal_type_id(&first, "Packet");
    let box_instances = first
        .types
        .iter()
        .enumerate()
        .filter_map(|(id, ty)| {
            matches!(ty.representation(), Type::Struct { name, .. } if name == "Box")
                .then_some(id as u32)
        })
        .collect::<Vec<_>>();
    assert!(
        box_instances.iter().all(|instance| packet < *instance),
        "ground generic instances {box_instances:?} must not renumber monomorphic Packet r{packet}"
    );
    assert_eq!(
        first
            .types
            .iter()
            .filter(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Box"))
            .count(),
        3
    );
}

#[test]
fn unsupported_generic_struct_shapes_are_rejected_with_source_spans() {
    let cases = [
        (
            "bare",
            "struct Box<T> { value: T }\nread(value: Box) -> { () }\nmain() -> { () }",
        ),
        (
            "wrong-arity",
            "struct Box<T> { value: T }\nread(value: Box<i64, Text>) -> { () }\nmain() -> { () }",
        ),
        (
            "recursive",
            "struct Loop<T> { next: Loop<T> }\nmain() -> { () }",
        ),
    ];
    for (name, source) in cases {
        let errors = compile_source_to_bytecode(&format!("{name}.glorious"), source).unwrap_err();
        assert!(!errors.is_empty(), "{name} unexpectedly compiled");
        assert!(
            errors.iter().any(|error| error.span.is_some()),
            "{name} did not preserve a source span: {errors:?}"
        );
        assert!(
            errors.iter().any(|error| error.code.is_some()),
            "{name} did not produce a structured diagnostic code: {errors:?}"
        );
    }
}

#[test]
fn grounded_generic_identity_emits_one_direct_specialization() {
    let source = r#"
        id<T>(value: T) -> T { value }
        answer() -> i64 { let first = id(1); id(42) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-id.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
    let clones = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$specialization$id#"))
        .collect::<Vec<_>>();
    assert_eq!(clones.len(), 1);
    assert_eq!(clones[0].params, [grandiose_vm::I64]);
    assert_eq!(clones[0].return_type, grandiose_vm::I64);
}

#[test]
fn reference_bearing_generic_specializations_forward_and_end_lexical_loans() {
    let source = r#"
        forward_shared<T>(value: &T) -> &T { value }
        forward_unique<T>(value: &mut T) -> &mut T { value }
        id<T>(value: T) -> T { value }
        consume_shared<T>(value: &T) -> { value; () }
        consume_unique<T>(value: &mut T) -> { value; () }
        external_shared(value: &i64) -> &i64 { forward_shared(value) }
        external_unique(value: &mut i64) -> &mut i64 { forward_unique(value) }
        id_shared(value: &i64) -> &i64 { id(value) }
        id_unique(value: &mut i64) -> &mut i64 { id(value) }
        lexical() -> i64 {
            let value = 42;
            { let alias = forward_shared(&value); consume_shared(alias); };
            { let alias = forward_unique(&mut value); consume_unique(alias); };
            value
        }
        main() -> { lexical(); () }
    "#;
    let phases = compile_source_to_phases("generic-reference-forward.glorious", source).unwrap();
    let repeated = compile_source_to_phases("generic-reference-forward.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    for (prefix, reference) in [
        ("$specialization$forward_shared#", false),
        ("$specialization$forward_unique#", true),
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name.starts_with(prefix))
            .unwrap();
        assert_eq!(function.params.len(), 1);
        assert_eq!(function.params[0], function.return_type);
        assert!(
            matches!(
                phases.artifact.types[function.params[0] as usize].representation(),
                Type::RefUnique { referent: grandiose_vm::I64 } if reference
            ) || matches!(
                phases.artifact.types[function.params[0] as usize].representation(),
                Type::RefShared { referent: grandiose_vm::I64 } if !reference
            )
        );
    }
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$id#"))
            .count(),
        2
    );

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    let lexical = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "lexical")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(lexical, vec![]).unwrap(),
        Value::I64(42)
    );

    let reordered = r#"
        main() -> { lexical(); () }
        lexical() -> i64 {
            let value = 42;
            { let alias = forward_shared(&value); consume_shared(alias); };
            { let alias = forward_unique(&mut value); consume_unique(alias); };
            value
        }
        id_unique(value: &mut i64) -> &mut i64 { id(value) }
        id_shared(value: &i64) -> &i64 { id(value) }
        external_unique(value: &mut i64) -> &mut i64 { forward_unique(value) }
        external_shared(value: &i64) -> &i64 { forward_shared(value) }
        consume_unique<T>(value: &mut T) -> { value; () }
        consume_shared<T>(value: &T) -> { value; () }
        id<T>(value: T) -> T { value }
        forward_unique<T>(value: &mut T) -> &mut T { value }
        forward_shared<T>(value: &T) -> &T { value }
    "#;
    assert_eq!(
        compile_source_to_bytecode("generic-reference-forward-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn named_generic_specialization_preserves_explicit_reference_regions() {
    let source = r#"
        first<'a, 'b, T>(left: &'a T, right: &'b T) -> &'a T { left }
        external(left: &i64, right: &i64) -> &i64 { first(left, right) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-explicit-regions.glorious", source).unwrap();
    let selected = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$specialization$first#"))
        .expect("the grounded call must emit one named specialization");
    assert_eq!(selected.params.len(), 2);
    assert_eq!(selected.return_type, selected.params[0]);
    verify(phases.artifact).unwrap();
}

#[test]
fn projected_reborrows_allow_disjoint_siblings_through_shared_and_unique_parents() {
    let positive = r#"
        struct Pair { left: i64, right: i64 }
        read_shared(value: &Pair) -> () {
            let left = &value.left;
            let right = &value.right;
            left;
            right;
            ()
        }
        read_split(value: &mut Pair) -> () {
            let left = &value.left;
            let right = &mut value.right;
            left;
            right;
            ()
        }
        main() -> {
            let pair = Pair { left: 40, right: 2 };
            read_shared(&pair);
            read_split(&mut pair)
        }
    "#;
    let artifact =
        compile_source_to_bytecode("shared-projected-siblings.glorious", positive).unwrap();
    verify(artifact).unwrap();

    for (name, conflict) in [
        (
            "overlapping-parent-projected-conflict.glorious",
            r#"
                struct Pair { left: i64, right: i64 }
                bad(value: &mut Pair) -> () {
                    let shared = &value.left;
                    let unique = &mut value.left;
                    shared;
                    unique;
                    ()
                }
                main() -> { () }
            "#,
        ),
        (
            "whole-parent-projected-conflict.glorious",
            r#"
                struct Pair { left: i64, right: i64 }
                write(value: &mut Pair) -> () { value; () }
                bad(value: &mut Pair) -> () {
                    let shared = &value.left;
                    write(&mut *value);
                    shared;
                    ()
                }
                main() -> { () }
            "#,
        ),
    ] {
        let errors = compile_source_to_bytecode(name, conflict).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.message.contains("suspended")
                    || error.message.contains("live loan")
                    || error.message.contains("incompatible")
            }),
            "an overlapping child or whole-parent use must remain rejected: {errors:#?}"
        );
    }
}

#[test]
fn releasing_one_projected_child_keeps_its_live_sibling_registered() {
    let conflict = r#"
        struct Pair { left: i64, right: i64 }
        consume_shared(value: &i64) -> () { value; () }
        bad(value: &mut Pair) -> () {
            let left = &value.left;
            let right = &mut value.right;
            consume_shared(left);
            let overlap = &value.right;
            right;
            overlap;
            ()
        }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("projected-sibling-release-conflict.glorious", conflict)
            .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("live loan") || error.message.contains("incompatible")
        }),
        "releasing one child must not retire a live sibling loan: {errors:#?}"
    );

    let released = r#"
        struct Pair { left: i64, right: i64 }
        consume_shared(value: &i64) -> () { value; () }
        consume_unique(value: &mut i64) -> () { value; () }
        accepted(value: &mut Pair) -> () {
            let left = &value.left;
            let right = &mut value.right;
            consume_shared(left);
            consume_unique(right);
            let next = &mut value.left;
            consume_unique(next)
        }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("projected-sibling-release-complete.glorious", released)
            .unwrap();
    verify(artifact).unwrap();
}

#[test]
fn shared_call_result_downgrades_a_transferred_unique_loan() {
    let source = r#"
        downgrade<'a>(value: &'a mut i64) -> &'a i64 { &*value }
        exercise() -> i64 {
            let value = 21;
            let first = downgrade(&mut value);
            let second = &value;
            *first + *second
        }
        main() -> { exercise(); () }
    "#;
    let artifact = compile_source_to_bytecode("shared-call-downgrade.glorious", source).unwrap();
    let exercise = artifact
        .functions
        .iter()
        .position(|function| function.name == "exercise")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(exercise, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn generic_reference_result_tracks_the_exact_selected_argument() {
    let source = r#"
        choose<T>(left: &T, right: &T) -> &T { left }
        bad(left: &i64, right: &i64) -> &i64 { choose(left, right) }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("generic-reference-selection.glorious", source).unwrap();
    verify(artifact).unwrap();
}

#[test]
fn recursive_generic_reference_relays_infer_one_stable_parameter_origin() {
    let source = r#"
        relay_left<T>(value: &T) -> &T { relay_right(value) }
        relay_right<T>(value: &T) -> &T { relay_left(value) }
        external(value: &i64) -> &i64 { relay_left(value) }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("recursive-reference-relay.glorious", source).unwrap();
    let specializations = artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$specialization$relay_"))
        .collect::<Vec<_>>();
    assert_eq!(specializations.len(), 2);
    for specialization in specializations {
        assert_eq!(specialization.params, [specialization.return_type]);
        assert!(matches!(
            artifact.types[specialization.return_type as usize].representation(),
            Type::RefShared {
                referent: grandiose_vm::I64
            }
        ));
    }
    verify(artifact).unwrap();
}

#[test]
fn captureless_reference_callbacks_forward_shared_and_unique_loans() {
    let source = r#"
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        consume_shared(value: &i64) -> { value; () }
        consume_unique(value: &mut i64) -> { value; () }
        forward_shared(value: &i64) -> &i64 {
            apply(value, { item => item })
        }
        forward_unique(value: &mut i64) -> &mut i64 {
            apply(value, { item => item })
        }
        lexical() -> i64 {
            let value = 42;
            { let alias = forward_shared(&value); consume_shared(alias); };
            { let alias = forward_unique(&mut value); consume_unique(alias); };
            value
        }
        main() -> { lexical(); () }
    "#;
    let phases = compile_source_to_phases("reference-callback-forward.glorious", source).unwrap();
    let repeated = compile_source_to_phases("reference-callback-forward.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let closures = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$closure$"))
        .collect::<Vec<_>>();
    assert_eq!(closures.len(), 2);
    for unique in [false, true] {
        let function = closures
            .iter()
            .find(|function| {
                function.params.len() == 1
                    && function.params[0] == function.return_type
                    && matches!(
                        phases.artifact.types[function.return_type as usize].representation(),
                        Type::RefUnique {
                            referent: grandiose_vm::I64
                        } if unique
                    )
                    || function.params.len() == 1
                        && function.params[0] == function.return_type
                        && matches!(
                            phases.artifact.types[function.return_type as usize].representation(),
                            Type::RefShared {
                                referent: grandiose_vm::I64
                            } if !unique
                        )
            })
            .unwrap();
        assert_eq!(function.params, [function.return_type]);
    }

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    let lexical = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "lexical")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(lexical, vec![]).unwrap(),
        Value::I64(42)
    );

    let reordered = r#"
        main() -> { lexical(); () }
        lexical() -> i64 {
            let value = 42;
            { let alias = forward_shared(&value); consume_shared(alias); };
            { let alias = forward_unique(&mut value); consume_unique(alias); };
            value
        }
        forward_unique(value: &mut i64) -> &mut i64 {
            apply(value, { item => item })
        }
        forward_shared(value: &i64) -> &i64 {
            apply(value, { item => item })
        }
        consume_unique(value: &mut i64) -> { value; () }
        consume_shared(value: &i64) -> { value; () }
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
    "#;
    assert_eq!(
        compile_source_to_bytecode("reference-callback-forward-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn captureless_reference_callback_direct_parameter_selection_is_structured() {
    let source = r#"
        apply2<F, T, R>(left: T, right: T, body: F) -> R
            where F: Fn<(T, T), Output=R> { body(left, right) }
        choose(left: &i64, right: &i64) -> &i64 {
            apply2(left, right, { first, second => first })
        }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("reference-callback-selection.glorious", source).unwrap();
    verify(artifact).unwrap();
}

#[test]
fn captureless_callback_tuple_reference_signatures_transport_aggregate_origins() {
    let source = r#"
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        bad(value: (&i64, i64)) -> (&i64, i64) {
            apply(value, { item => item })
        }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("tuple-reference-closure-signature.glorious", source).unwrap();
    verify(artifact).unwrap();
}

#[test]
fn captureless_reference_callback_projects_a_nominal_reference_origin() {
    let source = r#"
        struct Holder { value: &i64 }
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        bad(holder: Holder) -> &i64 {
            apply(holder, { item => item.value })
        }
        answer() -> i64 {
            let value = 42;
            let holder = Holder { value: &value };
            *bad(move holder)
        }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("nominal-reference-closure-origin.glorious", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert!(
        artifact.reference_return_contracts.iter().any(|contract| {
            artifact.functions[contract.function as usize].name == "bad"
                && contract.routes.iter().any(|route| matches!(
                    route.origin,
                    grandiose_vm::bytecode::ReferenceReturnOrigin::Parameter {
                        parameter: 0,
                        ref path,
                    }
                        if path == &[0]
                ))
        }),
        "missing projected parameter origin: {:#?}",
        artifact.reference_return_contracts
    );
    assert_eq!(
        Vm::new(verify(artifact).unwrap()).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn generic_callback_bodies_create_nonescaping_loans_and_read_copy_referents() {
    let borrows = r#"
        borrow_inside<T>(value: T) -> T { let loan = &value; value }
        bad() -> i64 { borrow_inside(42) }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("generic-body-borrow.glorious", borrows).unwrap();
    let bad = artifact
        .functions
        .iter()
        .position(|function| function.name == "bad")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap()).run(bad, vec![]).unwrap(),
        Value::I64(42)
    );

    let dereference = r#"
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        bad(value: &i64) -> i64 { apply(value, { item => *item }) }
        answer() -> i64 { let value = 42; bad(&value) }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("reference-closure-body-dereference.glorious", dereference)
            .unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn captureless_callbacks_are_erased_to_direct_wrapper_calls() {
    let source = r#"
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        call2<F, A, B, R>(left: A, right: B, body: F) -> R
            where F: Fn<(A, B), Output=R> { body(left, right) }
        id<T>(value: T) -> T { value }
        explicit() -> i64 { call0({ => 42 }) }
        contextual() -> i64 { call0({ 40 + 2 }) }
        multi() -> i64 { call2(40, 2, { x, y => x + y }) }
        nested() -> i64 { call0({ id(42) }) }
        main() -> {
            let a = explicit();
            let b = contextual();
            let c = multi();
            let d = nested();
            ()
        }
    "#;
    let phases = compile_source_to_phases("callbacks.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    for name in ["explicit", "contextual", "multi", "nested"] {
        let id = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(id, vec![]).unwrap(),
            Value::I64(42)
        );
    }
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$closure$"))
            .count(),
        4
    );
    assert_direct_only_functions(&phases.artifact, |name| {
        matches!(name, "explicit" | "contextual" | "multi" | "nested")
            || name.starts_with("$closure$")
            || name.starts_with("$specialization$call0#")
            || name.starts_with("$specialization$call2#")
            || name.starts_with("$specialization$id#")
    });
    let specialized = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$specialization$"))
        .collect::<Vec<_>>();
    assert!(
        specialized
            .iter()
            .any(|function| function.params.is_empty())
    );
    assert!(
        specialized
            .iter()
            .any(|function| function.params == [grandiose_vm::I64, grandiose_vm::I64])
    );
    assert!(
        phases
            .core
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$call0#"))
            .all(|function| function.params.is_empty())
    );
    assert!(
        phases
            .mir
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$call0#"))
            .all(|function| function.params.is_empty())
    );

    struct NoHost;
    impl grandiose::eval::Host for NoHost {
        fn perform(
            &mut self,
            _effect: &str,
            _operation: &str,
            _args: Vec<grandiose::eval::Value>,
            span: grandiose::span::Span,
        ) -> Result<grandiose::eval::Value, grandiose::diagnostic::Diagnostic> {
            Err(grandiose::diagnostic::Diagnostic::error(
                "unexpected effect",
                "pure callback differential performed an effect",
                span,
            ))
        }
    }
    assert_eq!(
        grandiose::run_source("callbacks.glorious", source, vec![], &mut NoHost).unwrap(),
        grandiose::eval::Value::Unit
    );
    assert_eq!(
        Vm::new(verified)
            .run(phases.artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );

    let reordered = r#"
        main() -> {
            let a = explicit();
            let b = contextual();
            let c = multi();
            let d = nested();
            ()
        }
        nested() -> i64 { call0({ id(42) }) }
        multi() -> i64 { call2(40, 2, { x, y => x + y }) }
        contextual() -> i64 { call0({ 40 + 2 }) }
        explicit() -> i64 { call0({ => 42 }) }
        call2<F, A, B, R>(left: A, right: B, body: F) -> R
            where F: Fn<(A, B), Output=R> { body(left, right) }
        id<T>(value: T) -> T { value }
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
    "#;
    let same = compile_source_to_phases("callbacks.glorious", source).unwrap();
    let repeated = compile_source_to_phases("callbacks-reordered.glorious", reordered).unwrap();
    assert_eq!(phases.core_fingerprint(), same.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), same.mir_fingerprint());
    assert_eq!(phases.artifact.encode(), repeated.artifact.encode());
}

#[test]
fn copy_capture_callbacks_lift_lexical_scalars_once_and_execute() {
    let source = r#"
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        id<T>(value: T) -> T { value }
        one_explicit() -> i64 {
            let base = 40;
            call0({ => base + 2 })
        }
        one_contextual() -> i64 {
            let base = 40;
            call0({ base + 2 })
        }
        multiple() -> i64 {
            let left = 20;
            let right = 22;
            call0({ => left + right })
        }
        duplicate() -> i64 {
            let part = 14;
            call0({ => part + part + part })
        }
        binder_shadow() -> i64 {
            let item = 100;
            apply(40, { item => item + 2 })
        }
        local_shadow() -> i64 {
            let item = 100;
            call0({ => { let item = 40; item + 2 } })
        }
        nested_generic() -> i64 {
            let answer = 42;
            call0({ => id(answer) })
        }
        main() -> {
            one_explicit(); one_contextual(); multiple(); duplicate();
            binder_shadow(); local_shadow(); nested_generic(); ()
        }
    "#;
    let phases = compile_source_to_phases("copy-capture-callbacks.glorious", source).unwrap();
    let repeated = compile_source_to_phases("copy-capture-callbacks.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let closures = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$closure$"))
        .collect::<Vec<_>>();
    assert_eq!(closures.len(), 7);
    assert_eq!(
        closures
            .iter()
            .filter(|function| function.params.is_empty())
            .count(),
        1,
        "a local binder must shadow its outer lexical name"
    );
    assert_eq!(
        closures
            .iter()
            .filter(|function| function.params.len() == 1)
            .count(),
        5,
        "duplicate lexical uses must lift one capture and parameter binders must not capture"
    );
    assert_eq!(
        closures
            .iter()
            .filter(|function| function.params.len() == 2)
            .count(),
        1
    );
    assert!(closures.iter().all(|function| {
        function.params.iter().all(|ty| *ty == grandiose_vm::I64)
            && function.return_type == grandiose_vm::I64
    }));

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    for name in [
        "one_explicit",
        "one_contextual",
        "multiple",
        "duplicate",
        "binder_shadow",
        "local_shadow",
        "nested_generic",
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(42),
            "{name}"
        );
    }

    let reordered = r#"
        main() -> {
            one_explicit(); one_contextual(); multiple(); duplicate();
            binder_shadow(); local_shadow(); nested_generic(); ()
        }
        nested_generic() -> i64 {
            let answer = 42;
            call0({ => id(answer) })
        }
        local_shadow() -> i64 {
            let item = 100;
            call0({ => { let item = 40; item + 2 } })
        }
        binder_shadow() -> i64 {
            let item = 100;
            apply(40, { item => item + 2 })
        }
        duplicate() -> i64 {
            let part = 14;
            call0({ => part + part + part })
        }
        multiple() -> i64 {
            let left = 20;
            let right = 22;
            call0({ => left + right })
        }
        one_contextual() -> i64 {
            let base = 40;
            call0({ base + 2 })
        }
        one_explicit() -> i64 {
            let base = 40;
            call0({ => base + 2 })
        }
        id<T>(value: T) -> T { value }
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
    "#;
    assert_eq!(
        compile_source_to_bytecode("copy-capture-callbacks-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn copy_capture_callbacks_lift_structurally_copyable_aggregates() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        tuple_capture() -> i64 {
            let pair = (40, 2);
            call0({ => pair.0 + pair.1 })
        }
        struct_capture() -> i64 {
            let pair = Pair { left: 20, right: 22 };
            call0({ => pair.left + pair.right })
        }
        main() -> { tuple_capture(); struct_capture(); () }
    "#;
    let phases = compile_source_to_phases("aggregate-copy-captures.glorious", source).unwrap();
    let closures = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$closure$"))
        .collect::<Vec<_>>();
    assert_eq!(closures.len(), 2);
    assert!(closures.iter().all(|function| {
        function.params.len() == 1 && function.return_type == grandiose_vm::I64
    }));
    assert!(closures.iter().any(|function| matches!(
        phases.artifact.types[function.params[0] as usize].representation(),
        Type::Tuple { fields, .. }
            if fields.as_slice() == [grandiose_vm::I64, grandiose_vm::I64]
    )));
    assert!(closures.iter().any(|function| matches!(
        phases.artifact.types[function.params[0] as usize].representation(),
        Type::Struct { name, copy: true, .. } if name == "Pair"
    )));

    let bytes = phases.artifact.encode();
    let verified = verify(Artifact::decode(&bytes).unwrap()).unwrap();
    for name in ["tuple_capture", "struct_capture"] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(42)
        );
    }
}

#[test]
fn copy_capture_callbacks_reject_unsafe_capture_and_body_shapes() {
    let cases = [(
        "unique-owner",
        r#"
                struct Owner { value: &mut i64 }
                call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
                bad(value: Owner) -> i64 { call0({ => { value; 42 } }) }
                main() -> { () }
            "#,
        &["reference", "noncopy"] as &[&str],
    )];
    for (name, source, categories) in cases {
        let errors = compile_source_to_bytecode(&format!("copy-capture-{name}.glorious"), source)
            .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.is_some()
                    && error.span.is_some()
                    && error.message.contains("closure")
                    && categories
                        .iter()
                        .any(|category| error.message.contains(category))
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn mutate_capture_uses_a_nonescaping_unique_environment_borrow() {
    let source = r#"
        touch<F>(body: F) -> Unit where F: Fn<(), Output=Unit> { body() }
        answer() -> i64 {
            let value = 42;
            touch({ => { let loan = &mut value; () } });
            value
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("mutate-capture.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn nonescaping_shared_reference_capture_is_forwarded_without_copying_the_referent() {
    let source = r#"
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        answer() -> i64 {
            let value = 42;
            let reference = &value;
            call0({ => { reference; 42 } })
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("shared-reference-capture.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn observe_capture_of_affine_owner_borrows_the_environment_instead_of_copying_it() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[0,1]> for Ticket {}
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        answer() -> i64 {
            let ticket = Ticket { value: 1 };
            call0({ => ticket.value + 41 })
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("affine-observe-capture.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn callable_aliases_and_transitive_forwarding_remain_direct_and_execute() {
    let source = r#"
        alias_once<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            let saved = body;
            saved()
        }
        alias_chain<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            let first = body;
            let second = first;
            second()
        }
        forward_once<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            alias_once(body)
        }
        forward_twice<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            forward_once(body)
        }
        shadow_forward<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            let base = 100;
            alias_once(body)
        }
        id<T>(value: T) -> T { value }
        direct_alias() -> i64 { alias_once({ => 42 }) }
        captured_alias_chain() -> i64 {
            let base = 40;
            alias_chain({ => base + 2 })
        }
        forwarded_once() -> i64 { forward_once({ 42 }) }
        captured_forwarded_twice() -> i64 {
            let base = 40;
            forward_twice({ => base + 2 })
        }
        stable_capture_identity() -> i64 {
            let base = 40;
            shadow_forward({ => base + 2 })
        }
        nested_generic_forwarding() -> i64 {
            let answer = 42;
            forward_twice({ => id(answer) })
        }
        main() -> {
            direct_alias(); captured_alias_chain(); forwarded_once();
            captured_forwarded_twice(); stable_capture_identity();
            nested_generic_forwarding(); ()
        }
    "#;
    let phases = compile_source_to_phases("callable-alias-forward.glorious", source).unwrap();
    let repeated = compile_source_to_phases("callable-alias-forward.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let closures = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$closure$"))
        .collect::<Vec<_>>();
    assert_eq!(closures.len(), 6);
    assert_eq!(
        closures
            .iter()
            .filter(|function| function.params.is_empty())
            .count(),
        2
    );
    assert_eq!(
        closures
            .iter()
            .filter(|function| function.params == [grandiose_vm::I64])
            .count(),
        4
    );
    assert!(
        closures
            .iter()
            .all(|function| function.return_type == grandiose_vm::I64)
    );
    assert_direct_only_functions(&phases.artifact, |name| {
        name.starts_with("$closure$")
            || name.starts_with("$specialization$alias_once#")
            || name.starts_with("$specialization$alias_chain#")
            || name.starts_with("$specialization$forward_once#")
            || name.starts_with("$specialization$forward_twice#")
            || name.starts_with("$specialization$shadow_forward#")
            || matches!(
                name,
                "direct_alias"
                    | "captured_alias_chain"
                    | "forwarded_once"
                    | "captured_forwarded_twice"
                    | "stable_capture_identity"
                    | "nested_generic_forwarding"
            )
    });
    for prefix in [
        "$specialization$alias_once#",
        "$specialization$alias_chain#",
        "$specialization$forward_once#",
        "$specialization$forward_twice#",
        "$specialization$shadow_forward#",
    ] {
        assert!(phases.artifact.functions.iter().any(|function| {
            function.name.starts_with(prefix)
                && function.params.iter().all(|ty| *ty == grandiose_vm::I64)
        }));
    }

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    for name in [
        "direct_alias",
        "captured_alias_chain",
        "forwarded_once",
        "captured_forwarded_twice",
        "stable_capture_identity",
        "nested_generic_forwarding",
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(42),
            "{name}"
        );
    }

    let reordered = r#"
        main() -> {
            direct_alias(); captured_alias_chain(); forwarded_once();
            captured_forwarded_twice(); stable_capture_identity();
            nested_generic_forwarding(); ()
        }
        nested_generic_forwarding() -> i64 {
            let answer = 42;
            forward_twice({ => id(answer) })
        }
        captured_forwarded_twice() -> i64 {
            let base = 40;
            forward_twice({ => base + 2 })
        }
        stable_capture_identity() -> i64 {
            let base = 40;
            shadow_forward({ => base + 2 })
        }
        forwarded_once() -> i64 { forward_once({ 42 }) }
        captured_alias_chain() -> i64 {
            let base = 40;
            alias_chain({ => base + 2 })
        }
        direct_alias() -> i64 { alias_once({ => 42 }) }
        id<T>(value: T) -> T { value }
        shadow_forward<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            let base = 100;
            alias_once(body)
        }
        forward_twice<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            forward_once(body)
        }
        forward_once<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            alias_once(body)
        }
        alias_chain<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            let first = body;
            let second = first;
            second()
        }
        alias_once<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            let saved = body;
            saved()
        }
    "#;
    assert_eq!(
        compile_source_to_bytecode("callable-alias-forward-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn forwarding_one_callable_to_distinct_binders_deduplicates_hidden_capture_abi() {
    let source = r#"
        invoke_both<F, G>(first: F, second: G) -> i64
            where F: Fn<(), Output=i64>, G: Fn<(), Output=i64> {
            first() + second()
        }
        forward_twice<F>(body: F) -> i64 where F: Fn<(), Output=i64> {
            invoke_both(body, body)
        }
        answer() -> i64 {
            let half = 21;
            forward_twice({ => half })
        }
        main() -> { answer(); () }
    "#;
    let phases = compile_source_to_phases("deduped-forwarded-capture.glorious", source).unwrap();
    let inner = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$specialization$invoke_both#"))
        .unwrap();
    assert_eq!(
        inner.params,
        [grandiose_vm::I64],
        "the same lifted capture must occupy one hidden ABI slot across distinct callable binders"
    );
    let outer = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$specialization$forward_twice#"))
        .unwrap();
    assert_eq!(outer.params, [grandiose_vm::I64]);
    let closure = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$closure$"))
        .unwrap();
    assert_eq!(closure.params, [grandiose_vm::I64]);
    assert_eq!(closure.return_type, grandiose_vm::I64);
    assert_direct_only_functions(&phases.artifact, |name| {
        name == "answer"
            || name.starts_with("$closure$")
            || name.starts_with("$specialization$invoke_both#")
            || name.starts_with("$specialization$forward_twice#")
    });

    let bytes = phases.artifact.encode();
    let verified = verify(Artifact::decode(&bytes).unwrap()).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn callable_forwarding_rejects_ambiguous_binders_and_closes_finite_cycles() {
    let ambiguous = r#"
        choose<F, R>(first: F, second: F) -> R where F: Fn<(), Output=R> {
            first()
        }
        bad() -> i64 { choose({ => 1 }, { => 2 }) }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("ambiguous-callable-binder.glorious", ambiguous).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error.message.contains("callable")
                && error.message.contains("ambiguous")
        }),
        "{errors:#?}"
    );

    let cycle = r#"
        forward_a<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            forward_b(body)
        }
        forward_b<F, R>(body: F) -> R where F: Fn<(), Output=R> {
            forward_a(body)
        }
        bad() -> i64 { forward_a({ => 42 }) }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("cyclic-callable-forward.glorious", cycle).unwrap();
    for prefix in [
        "$specialization$forward_a#",
        "$specialization$forward_b#",
        "$closure$",
    ] {
        assert_eq!(
            artifact
                .functions
                .iter()
                .filter(|function| function.name.starts_with(prefix))
                .count(),
            1,
            "finite callable forwarding cycle did not deduplicate {prefix}"
        );
    }
    let bytes = artifact.encode();
    assert_eq!(
        compile_source_to_bytecode("cyclic-callable-forward.glorious", cycle)
            .unwrap()
            .encode(),
        bytes
    );
    verify(Artifact::decode(&bytes).unwrap()).unwrap();
}

#[test]
fn nested_specializations_and_owned_retained_callback_arguments_execute() {
    let source = r#"
        struct Packet { value: Text }
        id<T>(value: T) -> T { value }
        relay<T>(value: T) -> T { id(value) }
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        integer() -> i64 { relay(42) }
        text() -> Text { apply("hello", { value => value }) }
        packet() -> Packet { apply(Packet { value: "owned" }, { value => value }) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("nested-generics.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let run = |name: &str| {
        let id = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        Vm::new(verified.clone()).run(id, vec![]).unwrap()
    };
    assert_eq!(run("integer"), Value::I64(42));
    assert_eq!(run("text"), Value::Text("hello".into()));
    let packet = phases
        .artifact
        .types
        .iter()
        .position(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Packet"))
        .unwrap() as u32;
    assert_eq!(
        run("packet"),
        Value::aggregate(packet, [Value::Text("owned".into())])
    );
    assert!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$apply#"))
            .all(|function| function.params.len() == 1)
    );
}

#[test]
fn specialization_ids_do_not_collide_with_handler_synthetics() {
    let source = r#"
        effect Stop { stop(value: i64) -> ! }
        id<T>(value: T) -> T { value }
        generic_answer() -> i64 { id(42) }
        handled_answer() -> i64 {
            handle perform Stop::stop(42) {
                Stop::stop(value) => value
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-handler-ids.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();

    for name in ["generic_answer", "handled_answer"] {
        let id = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(id, vec![]).unwrap(),
            Value::I64(42)
        );
    }

    let specialization = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name.starts_with("$specialization$id#"))
        .unwrap();
    let first_handler_synthetic = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name.starts_with("$handler$"))
        .unwrap();
    assert!(specialization < first_handler_synthetic);
}

#[test]
fn unsupported_generic_and_callable_shapes_never_produce_an_artifact() {
    let cases = [
        r#"
            apply<F,T,R>(value:T,body:F)->R where F: Fn<(T),Output=R>{body(value)}
            bad()->i64 { apply(1, { 2 }) }
            main()->{()}
        "#,
        r#"
            bad_apply<F,R>(body:F)->R where F: Fn<i64,Output=R>{body()}
            bad()->i64 { bad_apply({ 1 }) }
            main()->{()}
        "#,
    ];
    for (index, source) in cases.into_iter().enumerate() {
        let errors =
            match compile_source_to_phases(&format!("generic-reject-{index}.glorious"), source) {
                Err(errors) => errors,
                Ok(_) => panic!("unsupported generic case {index} emitted an artifact"),
            };
        assert!(!errors.is_empty());
        assert!(errors.iter().all(|error| error.span.is_some()));
        assert!(
            errors.iter().any(|error| error.code.is_some()),
            "case {index}: {errors:#?}"
        );
    }
}

#[test]
fn compilation_is_byte_for_byte_deterministic_and_canonical() {
    let source = r#"
        add(left: i64, right: i64) -> i64 { left + right }
        main() -> { () }
    "#;
    let first = compile_source_to_bytecode("stable.glorious", source).unwrap();
    let second = compile_source_to_bytecode("stable.glorious", source).unwrap();
    let first_bytes = first.encode();
    assert_eq!(first_bytes, second.encode());
    assert_eq!(
        Artifact::decode(&first_bytes).unwrap().encode(),
        first_bytes
    );
}

#[test]
fn shared_and_unique_reference_forwarding_emit_verified_ownership_modes() {
    let source = r#"
        shared_id(value: &i64) -> &i64 { value }
        shared_relay(value: &i64) -> &i64 { shared_id(value) }
        unique_id(value: &mut i64) -> &mut i64 { value }
        unique_relay(value: &mut i64) -> &mut i64 { unique_id(value) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("reference-forward.glorious", source).unwrap();
    let repeated = compile_source_to_phases("reference-forward.glorious", source).unwrap();
    verify(phases.artifact.clone()).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(phases.core.canonical_text(), repeated.core.canonical_text());
    assert_eq!(phases.mir.canonical_text(), repeated.mir.canonical_text());
    assert_eq!(phases.artifact.encode(), repeated.artifact.encode());

    let shared = phases
        .artifact
        .types
        .iter()
        .position(|ty| matches!(ty, Type::RefShared { referent } if *referent == grandiose_vm::I64))
        .unwrap() as u32;
    let unique = phases
        .artifact
        .types
        .iter()
        .position(|ty| matches!(ty, Type::RefUnique { referent } if *referent == grandiose_vm::I64))
        .unwrap() as u32;
    assert_eq!(phases.artifact.required_features & 3, 3);

    let shared_id = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "shared_id")
        .unwrap();
    assert_eq!(shared_id.params, [shared]);
    assert_eq!(shared_id.return_type, shared);
    assert!(matches!(
        phases.artifact.code[shared_id.code_start as usize],
        Instruction::Move { src: 1, .. }
    ));

    let unique_id = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "unique_id")
        .unwrap();
    assert_eq!(unique_id.params, [unique]);
    assert_eq!(unique_id.return_type, unique);
    assert!(matches!(
        phases.artifact.code[unique_id.code_start as usize],
        Instruction::Move { src: 1, .. }
    ));
    assert!(
        phases
            .mir
            .canonical_text()
            .contains("Move { dst: 2, src: Operand { register: 1, mode: Move } }")
    );
}

#[test]
fn reference_aliases_and_recursive_nominal_fields_are_structurally_interned() {
    let source = r#"
        type Outer = &Inner;
        type Inner = &mut i64;
        struct Link { next: &Link }
        struct UniqueCell { value: Inner }
        forward(value: Outer) -> Outer { value }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("reference-layout.glorious", source).unwrap();
    verify(artifact.clone()).unwrap();

    let link = artifact
        .types
        .iter()
        .position(|ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Link"))
        .unwrap() as u32;
    let unique_cell = artifact
        .types
        .iter()
        .position(
            |ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "UniqueCell"),
        )
        .unwrap();
    let link_ref = artifact
        .types
        .iter()
        .position(|ty| matches!(ty, Type::RefShared { referent } if *referent == link))
        .unwrap() as u32;
    assert!(matches!(
        artifact.types[link as usize].representation(),
        Type::Struct { fields, copy: true, .. } if fields[0].ty == link_ref
    ));
    assert!(matches!(
        artifact.types[unique_cell].representation(),
        Type::Struct { copy: false, .. }
    ));

    let unique_i64 = artifact
        .types
        .iter()
        .position(|ty| matches!(ty, Type::RefUnique { referent } if *referent == grandiose_vm::I64))
        .unwrap() as u32;
    assert!(
        artifact
            .types
            .iter()
            .any(|ty| matches!(ty, Type::RefShared { referent } if *referent == unique_i64))
    );
}

#[test]
fn reference_descriptor_and_artifact_order_is_declaration_independent() {
    let left = r#"
        type A = &mut i64;
        type B = &A;
        struct Zed { field: B }
        struct Alpha { field: &Zed }
        forward(value: B) -> B { value }
        main() -> { () }
    "#;
    let right = r#"
        struct Alpha { field: &Zed }
        type B = &A;
        struct Zed { field: B }
        type A = &mut i64;
        main() -> { () }
        forward(value: B) -> B { value }
    "#;
    let left = compile_raw_source("left.glorious", left).unwrap();
    let right = compile_raw_source("right.glorious", right).unwrap();
    assert_eq!(left.encode(), right.encode());
    assert_eq!(
        Artifact::decode(&left.encode()).unwrap().encode(),
        left.encode()
    );
}

#[test]
fn whole_value_dereference_copies_a_duplicable_referent() {
    let source = r#"
        read(value: &i64) -> i64 { *value }
        answer() -> i64 { let value = 42; read(&value) }
        main() -> { () }
    "#;
    let artifact = compile_raw_source("deref-copy.glorious", source).unwrap();
    assert!(
        artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::DerefCopy { .. }))
    );
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn whole_value_dereference_rejects_a_nonduplicable_referent() {
    let errors = compile_raw_source(
        "deref-linear.glorious",
        r#"
            struct Ticket { serial: i64 }
            impl Use<[1,1]> for Ticket {}
            bad(value: &Ticket) -> Ticket { *value }
            main() -> { () }
        "#,
    )
    .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("cannot copy")
                && error
                    .message
                    .contains("principal Use interval is not duplicable")
        }),
        "{errors:#?}"
    );
}

#[test]
fn straight_line_local_borrows_calls_and_reborrows_emit_verified_mir() {
    let source = r#"
        take_shared(value: &i64) -> { () }
        take_unique(value: &mut i64) -> { () }
        immediate() -> i64 {
            let value = 40;
            take_shared(&value);
            take_unique(&mut value);
            value + 2
        }
        lexical() -> i64 {
            let value = 7;
            { let shared = &value; take_shared(shared); };
            let unique = &mut value;
            take_unique(unique);
            value
        }
        reborrow(parent: &mut i64) -> {
            { let shared = &*parent; take_shared(shared); };
            let unique = &mut *parent;
            take_unique(unique);
            ()
        }
        cleanup_after_outer_move(parent: &mut i64) -> i64 {
            let value = 9;
            { take_unique(parent); let shared = &value; take_shared(shared); };
            take_unique(&mut value);
            value
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("borrow-local.glorious", source).unwrap();
    verify(phases.artifact.clone()).unwrap();
    let immediate = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "immediate")
        .unwrap() as u32;
    let lexical = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "lexical")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(immediate, vec![])
            .unwrap(),
        Value::I64(42)
    );
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(lexical, vec![])
            .unwrap(),
        Value::I64(7)
    );
    let mir = phases.mir.canonical_text();
    assert!(mir.contains("Borrow {"));
    assert!(mir.contains("Reborrow {"));
    assert!(mir.contains("EndBorrow"));
    assert!(phases.core.canonical_text().contains("borrow l"));
    assert!(phases.core.canonical_text().contains("reborrow l"));
}

#[test]
fn point_set_nll_ends_named_loans_after_their_last_alias_use() {
    let source = r#"
        take_shared(value: &i64) -> { () }
        take_unique(value: &mut i64) -> { () }
        answer() -> i64 {
            let value = 42;
            let shared = &value;
            let alias = shared;
            take_shared(alias);
            let unique = &mut value;
            take_unique(unique);
            value
        }
        main() -> { answer(); () }
    "#;
    let phases = compile_source_to_phases("point-set-nll.glorious", source).unwrap();
    let repeated = compile_source_to_phases("point-set-nll.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(phases.artifact.encode(), repeated.artifact.encode());
    let core = phases.core.canonical_text();
    assert!(core.contains("region r"));
    assert!(core.contains("live=["));
    assert!(core.contains("end-borrow"));
    let mir = phases.mir.canonical_text();
    let end = mir.find("EndBorrow").unwrap();
    let unique = mir[end..].find("unique: true").unwrap() + end;
    assert!(
        end < unique,
        "the shared region must end before the unique loan"
    );
    let verified = verify(phases.artifact.clone()).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn point_set_nll_handles_reborrows_projected_places_and_drop_liveness() {
    let source = r#"
        take_shared(value: &i64) -> { () }
        take_unique(value: &mut i64) -> { () }
        reuse_parent(parent: &mut i64) -> {
            let child = &*parent;
            take_shared(child);
            take_unique(parent);
            ()
        }
        projected() -> i64 {
            let pair = (40, 2);
            let shared = &pair.0;
            take_shared(shared);
            let unique = &mut pair.0;
            take_unique(unique);
            pair.0 + pair.1
        }
        struct Guard { value: i64 }
        impl Drop for Guard { drop(&mut self) -> { self.value; () } }
        observe(value: &Guard) -> { value.value; () }
        consume(value: Guard) -> { () }
        drop_after_last_use() -> i64 {
            let guard = Guard { value: 42 };
            let loan = &guard;
            observe(loan);
            consume(move guard);
            42
        }
        main() -> { projected(); drop_after_last_use(); () }
    "#;
    let phases = compile_source_to_phases("point-set-nll-places.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    for name in ["projected", "drop_after_last_use"] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(42)
        );
    }
    let core = phases.core.canonical_text();
    assert!(core.matches("end-borrow").count() >= 3);
    assert!(core.contains("outlives=["));
    verify(phases.artifact).unwrap();
}

#[test]
fn point_set_nll_keeps_future_aliases_live_and_still_rejects_escape() {
    let future_use = r#"
        take_shared(value: &i64) -> { () }
        bad() -> {
            let value = 42;
            let shared = &value;
            let alias = shared;
            take_shared(alias);
            let unique = &mut value;
            take_shared(shared);
            ()
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("nll-future-alias.glorious", future_use).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error.message.contains("incompatible live loan")
        }),
        "{errors:#?}"
    );

    let escape = r#"
        bad() -> &i64 {
            let value = 42;
            let loan = &value;
            loan
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("nll-local-escape.glorious", escape).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.is_some() && error.span.is_some() && error.message.contains("cannot escape")
        }),
        "{errors:#?}"
    );
}

#[test]
fn point_set_nll_joins_handler_branches_before_a_later_unique_borrow() {
    let source = r#"
        effect Select { left() -> ! right() -> ! }
        take_shared(value: &i64) -> { () }
        take_unique(value: &mut i64) -> { () }
        take_unit(value: ()) -> { () }
        answer() -> i64 {
            let value = 42;
            let shared = &value;
            let alias = shared;
            take_unit(handle perform Select::left() {
                Select::left() => { take_shared(shared); () },
                Select::right() => { take_shared(alias); () }
            });
            let unique = &mut value;
            take_unique(unique);
            value
        }
        main() -> { answer(); () }
    "#;
    let phases = compile_source_to_phases("point-set-handler-join.glorious", source).unwrap();
    let repeated = compile_source_to_phases("point-set-handler-join.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(phases.artifact.encode(), repeated.artifact.encode());
    let core = phases.core.canonical_text();
    let handler = core.find("handle h").unwrap();
    let end = core[handler..].find("end-borrow").unwrap() + handler;
    let unique = core[end..].find("unique=true").unwrap() + end;
    assert!(handler < end && end < unique);
    let verified = verify(phases.artifact.clone()).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn point_set_nll_handler_join_preserves_a_future_alias_conflict() {
    let source = r#"
        effect Stop { stop() -> ! }
        take_shared(value: &i64) -> { () }
        take_unit(value: ()) -> { () }
        bad() -> {
            let value = 42;
            let shared = &value;
            take_unit(handle perform Stop::stop() { Stop::stop() => { take_shared(shared); () } });
            let unique = &mut value;
            take_shared(shared);
            ()
        }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("point-set-handler-future.glorious", source).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error.message.contains("incompatible live loan")
        }),
        "{errors:#?}"
    );
}

#[test]
fn projected_tuple_borrows_are_field_disjoint_verified_and_deterministic() {
    use grandiose::{diagnostic::Diagnostic, eval::Host, span::Span};

    struct NoHost;
    impl Host for NoHost {
        fn perform(
            &mut self,
            _effect: &str,
            _operation: &str,
            _args: Vec<grandiose::eval::Value>,
            span: Span,
        ) -> Result<grandiose::eval::Value, Diagnostic> {
            Err(Diagnostic::error(
                "unexpected effect",
                "unexpected effect",
                span,
            ))
        }
    }
    let source = r#"
        take_shared(value: &i64) -> { () }
        take_unique(value: &mut i64) -> { () }
        answer() -> i64 {
            let pair = (40, 2);
            take_shared(&pair.0);
            take_unique(&mut pair.1);
            { let first = &pair.0; let second = &pair.0; () };
            {
                let left = &mut pair.0;
                let copied = pair.1;
                let right = &mut pair.1;
                ()
            };
            pair.0 + pair.1
        }
        main() -> { answer(); () }
    "#;
    let first = compile_source_to_phases("projected-borrow.glorious", source).unwrap();
    let second = compile_source_to_phases("projected-borrow.glorious", source).unwrap();
    let verified = verify(first.artifact.clone()).unwrap();
    let answer = first
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        grandiose::run_source("projected-borrow.glorious", source, vec![], &mut NoHost).unwrap(),
        grandiose::eval::Value::Unit
    );
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    assert!(first.core.canonical_text().contains("project-borrow"));
    assert!(first.mir.canonical_text().contains("ProjectBorrow"));
    let answer_code = function_code(&first.artifact, &first.artifact.functions[answer as usize]);
    assert!(answer_code.iter().any(|instruction| matches!(
        instruction,
        Instruction::ProjectBorrowShared { field: 0, .. }
    )));
    assert!(answer_code.iter().any(|instruction| matches!(
        instruction,
        Instruction::ProjectBorrowUnique { field: 1, .. }
    )));
    // References consumed by calls need no explicit end, and the remaining
    // lexical-only borrow proofs are erased by mandatory O0 lowering.
    assert!(
        !answer_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::EndBorrow { .. }))
    );
}

#[test]
fn projected_tuple_borrow_conflicts_and_unsupported_places_are_diagnosed() {
    let cases = [
        "bad() -> { let pair = (1, 2); let first = &mut pair.0; let second = &pair.0; first; () } main() -> { () }",
        "bad() -> i64 { let pair = (1, 2); let first = &mut pair.0; let result = pair.0; first; result } main() -> { () }",
        "bad() -> (i64, i64) { let pair = (1, 2); let first = &pair.0; let result = pair; first; result } main() -> { () }",
        "bad() -> (&i64,) { let pair = (1, 2); let field = &pair.0; (field,) } main() -> { () }",
        "bad() -> &i64 { let pair = (1, 2); &pair.0 } main() -> { () }",
    ];
    for source in cases {
        let errors =
            compile_source_to_bytecode("bad-projected-borrow.glorious", source).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.code.is_some() && error.span.is_some()),
            "{errors:#?}"
        );
    }
}

#[test]
fn projected_struct_borrows_and_moves_reuse_numeric_field_places() {
    use grandiose::{diagnostic::Diagnostic, eval::Host, span::Span};

    struct NoHost;
    impl Host for NoHost {
        fn perform(
            &mut self,
            _effect: &str,
            _operation: &str,
            _args: Vec<grandiose::eval::Value>,
            span: Span,
        ) -> Result<grandiose::eval::Value, Diagnostic> {
            Err(Diagnostic::error(
                "unexpected effect",
                "unexpected effect",
                span,
            ))
        }
    }
    let source = r#"
        struct Pair { left: i64, right: i64 }
        struct Owner { value: &mut i64 }
        struct Vessel { owner: Owner, count: i64 }
        take_shared(value: &i64) -> { () }
        take_unique(value: &mut i64) -> { () }
        answer() -> i64 {
            let pair = Pair { left: 40, right: 2 };
            take_shared(&pair.left);
            take_unique(&mut pair.right);
            {
                let left = &mut pair.left;
                let copied = pair.right;
                let right = &mut pair.right;
                ()
            };
            pair.left + pair.right
        }
        take_vessel(value: Vessel) -> Owner { value.owner }
        keep_copy(value: Vessel) -> i64 {
            let owner = value.owner;
            value.count
        }
        main() -> { answer(); () }
    "#;
    let first = compile_source_to_phases("projected-struct.glorious", source).unwrap();
    let second = compile_source_to_phases("projected-struct.glorious", source).unwrap();
    let verified = verify(first.artifact.clone()).unwrap();
    let answer = first
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
    let interpreted =
        grandiose::run_source("projected-struct.glorious", source, vec![], &mut NoHost).unwrap();
    let executed = Vm::new(verify(first.artifact.clone()).unwrap())
        .run(first.artifact.entry_function.unwrap(), vec![])
        .unwrap();
    assert_eq!(interpreted, grandiose::eval::Value::Unit);
    assert_eq!(executed, Value::Unit);
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    assert!(first.core.canonical_text().contains("project-borrow"));
    assert!(
        first
            .core
            .canonical_text()
            .contains("project field#0 copy=false")
    );
    assert!(first.mir.canonical_text().contains("ProjectBorrow"));
    assert!(first.mir.canonical_text().contains("ProjectMove"));
    assert!(first.artifact.code.iter().any(|instruction| matches!(
        instruction,
        Instruction::ProjectBorrowShared { field: 0, .. }
    )));
    assert!(first.artifact.code.iter().any(|instruction| matches!(
        instruction,
        Instruction::ProjectBorrowUnique { field: 1, .. }
    )));
    assert!(
        first
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::ProjectMove { field: 0, .. }))
    );
    for name in ["take_vessel", "keep_copy"] {
        let function = first
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert!(
            first
                .artifact
                .cleanups
                .iter()
                .any(|cleanup| { cleanup.function == function && cleanup.registers.contains(&1) })
        );
    }
}

#[test]
fn projected_struct_place_conflicts_generics_and_nested_paths_reject() {
    let cases = [
        "struct Pair { left: i64, right: i64 } bad(value: Pair) -> { let first = &mut value.left; let second = &value.left; first; () } main() -> { () }",
        "struct Pair { left: i64, right: i64 } bad(value: Pair) -> Pair { let first = &value.left; let result = value; first; result } main() -> { () }",
        "struct Box<T> { value: T } bad(value: Box<i64>) -> { let field = &value.value; () } main() -> { () }",
        "struct Owner { value: &mut i64 } struct Vessel { owner: Owner, count: i64 } bad(value: Vessel) -> Vessel { let owner = value.owner; value } main() -> { () }",
        "struct Pair { left: i64, right: i64 } bad(value: Pair) -> (&i64,) { let field = &value.left; (field,) } main() -> { () }",
    ];
    for source in cases {
        let errors =
            compile_source_to_bytecode("bad-projected-struct.glorious", source).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.code.is_some() && error.span.is_some()),
            "{errors:#?}"
        );
    }
}

#[test]
fn nested_projected_places_lower_as_explicit_verified_steps() {
    let source = r#"
        struct Inner { pair: (i64, i64) }
        struct Outer { left: Inner, right: Inner }
        take_shared(value: &i64) -> { () }
        answer() -> i64 {
            let value = Outer {
                left: Inner { pair: (20, 1) },
                right: Inner { pair: (2, 22) }
            };
            take_shared(&value.left.pair.0);
            {
                let left = &value.left.pair.0;
                let right = &value.right.pair.1;
                ()
            };
            value.left.pair.0 + value.right.pair.1
        }
        main() -> { answer(); () }
    "#;
    let first = compile_source_to_phases("nested-place.glorious", source).unwrap();
    let second = compile_source_to_phases("nested-place.glorious", source).unwrap();
    let verified = verify(first.artifact.clone()).unwrap();
    let answer = first
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    let core = first.core.canonical_text();
    assert!(core.contains("project-borrow"));
    assert!(core.matches("field#").count() >= 3);
    assert!(first.artifact.code.windows(3).any(|window| matches!(
        window[0],
        Instruction::ProjectBorrowShared { .. }
    ) && matches!(
        window[1],
        Instruction::ProjectBorrowShared { .. }
    ) && matches!(
        window[2],
        Instruction::ProjectBorrowShared { .. }
    )));
    // The final projected reference is consumed by the call. Only its two
    // runtime-observed ancestor references require explicit loan endings.
    assert!(first.artifact.code.windows(2).any(|window| matches!(
        window[0],
        Instruction::EndBorrow { .. }
    ) && matches!(
        window[1],
        Instruction::EndBorrow { .. }
    )));
}

#[test]
fn nested_disjoint_unique_borrows_share_one_atomic_prefix() {
    let source = r#"
        struct Inner { pair: (i64, i64) }
        struct Outer { inner: Inner }
        take_unique(value: &mut i64) -> { () }
        answer() -> i64 {
            let value = Outer { inner: Inner { pair: (40, 2) } };
            {
                let left = &mut value.inner.pair.0;
                let right = &mut value.inner.pair.1;
                take_unique(left);
                take_unique(right);
                ()
            };
            value.inner.pair.0 + value.inner.pair.1
        }
        main() -> { answer(); () }
    "#;
    let phases = compile_source_to_phases("nested-split-borrow.glorious", source).unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );

    let answer_code = function_code(
        &phases.artifact,
        &phases.artifact.functions[answer as usize],
    );
    // `inner` and `pair` are projected once each; both unique leaf loans are
    // then derived from the same pair carrier.
    assert_eq!(
        answer_code
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::ProjectBorrowUnique { .. }))
            .count(),
        4
    );
}

#[test]
fn implicit_noncopy_field_moves_finish_an_exhausted_owner() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        struct Pair { left: Ticket, right: Ticket }

        drain(pair: Pair) -> i64 {
            let left = pair.left;
            let right = pair.right;
            let Ticket { value: left_value } = left;
            let Ticket { value: right_value } = right;
            left_value + right_value
        }

        main() -> () {
            drain(Pair {
                left: Ticket { value: 40 },
                right: Ticket { value: 2 }
            });
            ()
        }
    "#;

    let phases =
        compile_source_to_phases("implicit-exhaustive-projection.glorious", source).unwrap();
    let drain = phases
        .core
        .functions
        .iter()
        .find(|function| function.name == "drain")
        .unwrap();
    assert_eq!(format!("{:?}", drain.body).matches("Project {").count(), 2);
}

#[test]
fn nested_projected_place_overlap_and_move_boundaries_are_structured() {
    let cases = [
        "struct Inner { pair: (i64, i64) } struct Outer { inner: Inner } bad(value: Outer) -> { let ancestor = &value.inner; let child = &mut value.inner.pair.0; ancestor; () } main() -> { () }",
        "struct Inner { pair: (i64, i64) } struct Outer { inner: Inner } bad(value: Outer) -> Outer { let child = &value.inner.pair.0; let result = value; child; result } main() -> { () }",
        "struct Owner { value: &mut i64 } bad(value: ((Owner, i64), i64)) -> Owner { value.0.0 } main() -> { () }",
        "struct Box<T> { value: T } struct Outer { boxed: Box<i64> } bad(value: Outer) -> { let field = &value.boxed.value; () } main() -> { () }",
    ];
    for source in cases {
        let Err(errors) = compile_source_to_bytecode("bad-nested-place.glorious", source) else {
            panic!("expected nested-place rejection for {source}");
        };
        assert!(
            errors
                .iter()
                .any(|error| error.code.is_some() && error.span.is_some()),
            "{errors:#?}"
        );
    }
}

#[test]
fn invalid_straight_line_loans_report_source_errors_before_artifact_verification() {
    for (index, (source, needle)) in [
        (
            "bad() -> { let value = 1; let shared = &value; let unique = &mut value; shared; () } main() -> { () }",
            "incompatible live loan",
        ),
        (
            "id(value: &i64) -> &i64 { value } bad() -> { let value = 1; let shared = &value; { let alias = id(shared); }; let unique = &mut value; shared; () } main() -> { () }",
            "incompatible live loan",
        ),
        (
            "bad() -> i64 { let value = 1; let unique = &mut value; let result = value; unique; result } main() -> { () }",
            "during its unique loan",
        ),
        (
            "bad() -> { let value = 1; let unique = &mut value; let moved = unique; let again = unique; () } main() -> { () }",
            "already moved",
        ),
        (
            "bad() -> &i64 { let value = 1; &value } main() -> { () }",
            "cannot escape",
        ),
        (
            "struct Holder { value: &i64 } bad() -> Holder { let value = 1; Holder { value: &value } } main() -> { () }",
            "cannot escape",
        ),
        (
            "struct Holder { value: &i64 } wrap(value: &i64) -> Holder { Holder { value: value } } bad() -> Holder { let value = 1; wrap(&value) } main() -> { () }",
            "cannot escape",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let errors = match compile_source_to_bytecode("bad-loan.glorious", source) {
            Err(errors) => errors,
            Ok(_) => panic!("invalid loan case {index} emitted an artifact"),
        };
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G1BC002") && error.message.contains(needle)
            }),
            "{errors:#?}"
        );
        assert!(
            !errors
                .iter()
                .any(|error| error.code.as_deref() == Some("G1BC999"))
        );
    }
}

#[test]
fn cleanup_maps_follow_encoded_enum_arms_after_semantic_refinement() {
    let source = r#"
        enum Target {
            Missing,
            Parameter(u32),
            Local(u32),
            Function(u32),
            Struct(u32),
            Variant(u32)
        }

        impl Use<[0, *]> for Target {}

        kind(target: Target) -> u32 {
            handle target {
                Target::Missing => 0,
                Target::Parameter(_) => 1,
                Target::Local(_) => 2,
                Target::Function(_) => 3,
                Target::Struct(_) => 4,
                Target::Variant(_) => 5
            }
        }

        select(target: Target) -> u32 {
            handle target {
                Target::Function(shell) => shell,
                Target::Variant(variant) => variant,
                remaining => kind(remaining)
            }
        }

        main() -> { select(Target::Function(1)); () }
    "#;
    let artifact = compile_source_to_bytecode("structural-enum-cleanup.glorious", source).unwrap();
    verify(artifact).unwrap();
}

#[test]
fn stored_reference_can_escape_an_owned_carrier() {
    let source = r#"
        struct Holder { value: &i64 }
        unpack(value: Holder) -> &i64 {
            let projected = value.value;
            projected
        }
        read() -> i64 {
            let value = 42;
            let result = unpack(Holder { value: &value });
            *result
        }
        main() -> { () }
    "#;
    let artifact = compile_raw_source("owned-reference-carrier.glorious", source).unwrap();
    verify(artifact.clone()).unwrap();

    let unpack = artifact
        .functions
        .iter()
        .position(|function| function.name == "unpack")
        .unwrap() as u32;
    let contract = artifact
        .reference_return_contracts
        .iter()
        .find(|contract| contract.function == unpack)
        .unwrap();
    assert_eq!(contract.routes.len(), 1);
    assert_eq!(contract.routes[0].result_path, Vec::<u32>::new());
    assert!(matches!(
        &contract.routes[0].origin,
        grandiose_vm::bytecode::ReferenceReturnOrigin::Parameter { parameter: 0, path }
            if path == &[0]
    ));
}

#[test]
fn stored_reference_in_a_local_owned_carrier_cannot_escape() {
    let source = r#"
        struct Holder { value: &i64 }
        bad() -> &i64 {
            let value = 42;
            let holder = Holder { value: &value };
            let projected = holder.value;
            projected
        }
        main() -> { () }
    "#;
    let errors = compile_raw_source("local-reference-carrier.glorious", source)
        .expect_err("a locally rooted stored reference must not escape");
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1BC002") && error.message.contains("cannot escape")
        }),
        "{errors:#?}"
    );
}

#[test]
fn constants_are_deduplicated_and_sorted_by_frozen_wire_key() {
    let source = r#"
        infixl 30 +;
        zed() -> i64 { 2 }
        alpha() -> i64 { 1 + 2 + 1 }
        main() -> { () }
    "#;
    let artifact = compile_raw_source("constants.glorious", source).unwrap();
    assert_eq!(
        artifact.constants,
        vec![
            grandiose_vm::Constant::I64(2),
            grandiose_vm::Constant::I64(4)
        ]
    );
    assert!(Artifact::decode(&artifact.encode()).is_ok());
}

#[test]
fn emitted_direct_calls_locals_and_checked_arithmetic_execute_in_the_vm() {
    let source = r#"
        compute(value: i64) -> i64 {
            let doubled = value * 2;
            add(doubled, 6) / 2 - 1
        }
        add(left: i64, right: i64) -> i64 { left + right }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("execute.glorious", source).unwrap();
    let compute = artifact
        .functions
        .iter()
        .position(|function| function.name == "compute")
        .unwrap() as u32;
    let vm = Vm::new(verify(artifact).unwrap());
    assert_eq!(
        vm.run(compute, vec![Value::I64(10)]).unwrap(),
        Value::I64(12)
    );
}

#[test]
fn unit_return_uses_the_none32_operand_form() {
    let artifact = compile_source_to_bytecode("unit.glorious", "main() -> { () }").unwrap();
    let main = artifact.entry_function.unwrap();
    let function = &artifact.functions[main as usize];
    let code = &artifact.code
        [function.code_start as usize..(function.code_start + function.code_len) as usize];
    assert_eq!(code.last(), Some(&Instruction::Return { src: None }));

    let decoded = Artifact::decode(&artifact.encode()).unwrap();
    let function = &decoded.functions[decoded.entry_function.unwrap() as usize];
    assert_eq!(
        decoded.code[(function.code_start + function.code_len - 1) as usize],
        Instruction::Return { src: None }
    );
}

#[test]
fn o1_partially_evaluates_direct_callee_literals_at_constant_callers() {
    let phases = compile_source_to_phases_with_options(
        "direct-callee-literal.glorious",
        r#"
            add_one(value: i64) -> i64 { value + 1 }
            run() -> i64 { add_one(40) }
            main() -> { () }
        "#,
        CompileOptions {
            optimization_level: OptimizationLevel::O1,
        },
    )
    .unwrap();
    let run = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "run")
        .unwrap();
    let code = function_code(&phases.artifact, run);
    assert!(
        !code.iter().any(|instruction| matches!(
            instruction,
            Instruction::Call { .. } | Instruction::Primitive { .. }
        )),
        "constant direct call should lower to a constant result: {code:?}"
    );
    let run_id = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap()).run(run_id, vec![]).unwrap(),
        Value::I64(41)
    );
}

#[test]
fn direct_calls_resolve_forward_declarations() {
    let source = "main() -> { finish() } finish() -> { () }";
    let artifact = compile_source_to_bytecode("forward.glorious", source).unwrap();
    let vm = Vm::new(verify(artifact.clone()).unwrap());
    assert_eq!(
        vm.run(artifact.entry_function.unwrap(), vec![]).unwrap(),
        Value::Unit
    );
}

#[test]
fn shadowed_locals_and_parameters_are_all_destroyed_before_return() {
    let source = r#"
        shadow(value: i64) -> i64 {
            let value = value + 1;
            let value = value + 1;
            value
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("shadow.glorious", source).unwrap();
    let shadow = artifact
        .functions
        .iter()
        .position(|f| f.name == "shadow")
        .unwrap() as u32;
    let vm = Vm::new(verify(artifact).unwrap());
    assert_eq!(
        vm.run(shadow, vec![Value::I64(40)]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn unsupported_features_have_stable_structured_diagnostics() {
    let errors =
        compile_source_to_bytecode("unsupported.glorious", r#"main() -> { [1, 2] }"#).unwrap_err();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].source_name, "unsupported.glorious");
    assert_eq!(errors[0].code.as_deref(), Some("G1BC001"));
    assert!(errors[0].message.contains("list"));
}

#[test]
fn bundle_compilation_preserves_global_diagnostic_spans() {
    let bundle = SourceBundle::new(
        Segment::new("std.glorious", ""),
        Segment::new("main.glorious", r#"main() -> { "no" }"#),
        [],
    );
    let errors = compile_bundle_to_bytecode(&bundle).unwrap_err();
    assert!(bundle.map_diagnostic(&errors[0]).span.is_some());
}

#[test]
fn nested_nominal_structs_construct_project_and_cross_direct_calls() {
    let source = r#"
        compute(input: i64) -> i64 { read(outer_identity(make(input))) }
        read(value: Outer) -> i64 { value.inner.value }
        outer_identity(value: Outer) -> Outer { value }
        make(input: i64) -> Outer {
            Outer { right: 9, inner: Inner { value: input } }
        }
        struct Outer { inner: Inner, right: i64 }
        struct Inner { value: i64 }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("structs.glorious", source).unwrap();
    verify(artifact.clone()).unwrap();

    let inner = nominal_type_id(&artifact, "Inner");
    let outer = nominal_type_id(&artifact, "Outer");

    assert!(matches!(
        artifact.types[inner as usize].representation(),
        Type::Struct { name, fields, copy: true }
            if name == "Inner"
                && fields.iter().map(|field| field.name.as_str()).collect::<Vec<_>>() == ["value"]
    ));
    assert!(matches!(
        artifact.types[outer as usize].representation(),
        Type::Struct { name, fields, copy: true }
            if name == "Outer"
                && fields.iter().map(|field| field.name.as_str()).collect::<Vec<_>>() == ["inner", "right"]
                && fields[0].ty == inner
    ));
    assert!(artifact.code.iter().any(|instruction| matches!(
        instruction,
        Instruction::Construct { ty, fields, .. } if *ty == outer && fields.len() == 2
    )));
    let read = artifact
        .functions
        .iter()
        .find(|function| function.name == "read")
        .unwrap();
    assert_eq!(
        function_code(&artifact, read)
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::ProjectCopy { .. }))
            .count(),
        2
    );

    let compute = artifact
        .functions
        .iter()
        .position(|function| function.name == "compute")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(compute, vec![Value::I64(33)])
            .unwrap(),
        Value::I64(33)
    );
}

#[test]
fn struct_artifacts_are_canonical_across_declaration_order() {
    let first = r#"
        struct Zed { value: Alpha }
        struct Alpha { number: i64 }
        main() -> { let value = Zed { value: Alpha { number: 1 } }; () }
    "#;
    let second = r#"
        struct Alpha { number: i64 }
        struct Zed { value: Alpha }
        main() -> { let value = Zed { value: Alpha { number: 1 } }; () }
    "#;
    let first = compile_source_to_bytecode("first.glorious", first).unwrap();
    let second = compile_source_to_bytecode("second.glorious", second).unwrap();
    assert_eq!(first.encode(), second.encode());
    assert_eq!(
        Artifact::decode(&first.encode()).unwrap().encode(),
        first.encode()
    );
}

#[test]
fn bad_struct_fields_and_recursive_layouts_are_diagnosed() {
    for (source, needle) in [
        (
            "struct Pair { left: i64, right: i64 } main() -> { Pair { left: 1 } }",
            "missing field `right`",
        ),
        (
            "struct Pair { left: i64 } main() -> { Pair { left: 1, left: 2 } }",
            "initialized more than once",
        ),
        (
            "struct Pair { left: i64 } main() -> { Pair { left: 1, nope: 2 } }",
            "has no field `nope`",
        ),
        (
            "struct A { b: B } struct B { a: A } main() -> { () }",
            "recursive struct layout",
        ),
    ] {
        let errors = compile_source_to_bytecode("bad.glorious", source).unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains(needle)),
            "{errors:#?}"
        );
        assert!(errors.iter().all(|error| error.code.is_some()));
    }
}

#[test]
fn unresolved_complex_struct_field_types_are_explicitly_unsupported() {
    let source = "struct Box { value: List<i64> } main() -> { () }";
    let errors = compile_source_to_bytecode("complex.glorious", source).unwrap_err();
    assert!(errors.iter().any(|error| {
        error
            .code
            .as_deref()
            .is_some_and(|code| code.starts_with("G1BC"))
            && error.message.contains("unknown or unsupported")
    }));
}

#[test]
fn nominal_enums_construct_payloadless_and_nested_payload_variants_in_the_vm() {
    let source = r#"
        make(value: i64) -> Choice { pass(Choice::Number(value)) }
        empty() -> Choice { Choice::None }
        pass(value: Choice) -> Choice { relay(value) }
        relay(value: Choice) -> Choice { value }
        wrap(value: i64) -> Envelope {
            Envelope::Wrapped(Wrapper { choice: Choice::Number(value) })
        }
        enum Envelope { Wrapped(Wrapper) }
        struct Wrapper { choice: Choice }
        enum Choice { None, Number(i64) }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("enums.glorious", source).unwrap();
    let bytes = artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let choice = nominal_type_id(&artifact, "Choice");
    let envelope = nominal_type_id(&artifact, "Envelope");
    let wrapper = nominal_type_id(&artifact, "Wrapper");
    assert!(matches!(
        artifact.types[choice as usize].representation(),
        Type::Enum { name, variants, copy: true }
            if name == "Choice"
                && variants.iter().map(|variant| variant.name.as_str()).collect::<Vec<_>>() == ["None", "Number"]
                && variants[1].fields[0].ty == grandiose_vm::I64
    ));

    let verified = verify(artifact.clone()).unwrap();
    let run = |name: &str, args| {
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        Vm::new(verified.clone()).run(function, args).unwrap()
    };
    assert_eq!(
        run("empty", vec![]),
        Value::aggregate_with_variant(choice, Some(0), [])
    );
    assert_eq!(
        run("make", vec![Value::I64(42)]),
        Value::aggregate_with_variant(choice, Some(1), [Value::I64(42)])
    );
    assert_eq!(
        run("wrap", vec![Value::I64(7)]),
        Value::aggregate_with_variant(
            envelope,
            Some(0),
            [Value::aggregate(
                wrapper,
                [Value::aggregate_with_variant(
                    choice,
                    Some(1),
                    [Value::I64(7)]
                )]
            )]
        )
    );
}

#[test]
fn enum_artifacts_are_canonical_across_nominal_declaration_order() {
    let first = r#"
        struct Boxed { value: Maybe }
        enum Maybe { Empty, Full(i64) }
        main() -> { let value = Boxed { value: Maybe::Full(3) }; () }
    "#;
    let second = r#"
        enum Maybe { Empty, Full(i64) }
        struct Boxed { value: Maybe }
        main() -> { let value = Boxed { value: Maybe::Full(3) }; () }
    "#;
    assert_eq!(
        compile_source_to_bytecode("first.glorious", first)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("second.glorious", second)
            .unwrap()
            .encode()
    );
}

#[test]
fn invalid_enum_shapes_and_uses_have_structured_diagnostics() {
    for (source, needle) in [
        (
            "enum E { A, A } main() -> { () }",
            "declares variant `A` more than once",
        ),
        (
            "enum E { A(i64) } main() -> { E::A() }",
            "expects 1 payload value",
        ),
        (
            "enum E { A(i64) } main() -> { E::A(()) }",
            "expected i64, found Unit",
        ),
        (
            "enum E { A } main() -> { E::Missing }",
            "has no variant `Missing`",
        ),
        (
            "enum E { A } inspect(value: E) -> i64 { value.payload } main() -> { () }",
            "dominating active-variant proof",
        ),
        (
            "struct S { value: E } enum E { S(S) } main() -> { () }",
            "recursive owned nominal layout",
        ),
    ] {
        let errors = compile_source_to_bytecode("bad-enum.glorious", source).unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains(needle)),
            "{errors:#?}"
        );
        assert!(errors.iter().all(|error| error.code.is_some()));
    }
}

#[test]
fn unresolved_complex_enum_payloads_are_explicitly_unsupported() {
    let source = "enum E { A(List<i64>) } main() -> { () }";
    let errors = compile_source_to_bytecode("complex-enum.glorious", source).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error
                .code
                .as_deref()
                .is_some_and(|code| code.starts_with("G1BC"))
                && error.message.contains("unknown or unsupported")
        }),
        "{errors:#?}"
    );
}

#[test]
fn every_unsigned_width_emits_and_executes_boundary_constants() {
    let source = r#"
        a() -> u8 { 255 }
        b() -> u16 { 65535 }
        c() -> u32 { 4294967295 }
        d() -> u64 { 9223372036854775807 }
        e() -> u128 { 9223372036854775807 }
        f() -> usize { 9223372036854775807 }
        signed_min() -> i8 { -128 }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("unsigned.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    for (name, expected) in [
        ("a", Value::U64(255)),
        ("b", Value::U64(65_535)),
        ("c", Value::U64(4_294_967_295)),
        ("d", Value::U64(i64::MAX as u64)),
        ("e", Value::U128(i64::MAX as u128)),
        ("f", Value::U64(i64::MAX as u64)),
        ("signed_min", Value::I64(-128)),
    ] {
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            expected
        );
    }
}

#[test]
fn unsigned_checked_arithmetic_uses_the_frozen_integer_primitives() {
    let source = r#"
        calculate(value: u16) -> u16 { (value + 2) * 3 - 1 }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("unsigned-arithmetic.glorious", source).unwrap();
    let calculate = artifact
        .functions
        .iter()
        .position(|function| function.name == "calculate")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(calculate, vec![Value::U64(10)])
            .unwrap(),
        Value::U64(35)
    );
}

#[test]
fn text_literals_cross_calls_and_nested_nominals_as_copy_values() {
    let source = r#"
        echo(value: Text) -> Text { value }
        make() -> Message { Message::Named(Label { text: echo("grandiose") }) }
        struct Label { text: Text }
        enum Message { Empty, Named(Label) }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("text.glorious", source).unwrap();
    let label = nominal_type_id(&artifact, "Label");
    let message = nominal_type_id(&artifact, "Message");
    assert!(matches!(
        artifact.types[label as usize].representation(),
        Type::Struct { name, fields, copy: true }
            if name == "Label" && fields.len() == 1 && fields[0].ty == grandiose_vm::TEXT
    ));
    assert!(matches!(
        artifact.types[message as usize].representation(),
        Type::Enum { name, variants, copy: true }
            if name == "Message" && variants.len() == 2 && variants[1].fields[0].ty == label
    ));
    let make = artifact
        .functions
        .iter()
        .position(|function| function.name == "make")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(make, vec![])
            .unwrap(),
        Value::aggregate_with_variant(
            message,
            Some(1),
            [Value::aggregate(label, [Value::Text("grandiose".into())])]
        )
    );
}

#[test]
fn unsigned_and_text_constants_are_deduplicated_and_canonical() {
    let source = r#"
        small() -> u8 { 1 }
        large() -> u64 { 1 }
        first() -> Text { "zeta" }
        second() -> Text { "alpha" }
        repeat() -> Text { "zeta" }
        main() -> { () }
    "#;
    let artifact = compile_raw_source("leaf-constants.glorious", source).unwrap();
    assert_eq!(
        artifact.constants,
        vec![
            grandiose_vm::Constant::U8(1),
            grandiose_vm::Constant::U64(1),
            grandiose_vm::Constant::Text("alpha".into()),
            grandiose_vm::Constant::Text("zeta".into()),
        ]
    );
    let bytes = artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
}

#[test]
fn invalid_unsigned_literals_and_unknown_leaves_surface_honest_diagnostics() {
    for (source, needle) in [
        (
            "bad() -> u8 { -1 } main() -> { () }",
            "negative integer literal",
        ),
        (
            "bad() -> u8 { 256 } main() -> { () }",
            "out of range for u8",
        ),
        (
            "bad(value: UnknownLeaf) -> UnknownLeaf { value } main() -> { () }",
            "explicit supported monomorphic type",
        ),
    ] {
        let errors = compile_source_to_bytecode("invalid-leaf.glorious", source).unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains(needle)),
            "{errors:#?}"
        );
        assert!(errors.iter().all(|error| error.code.is_some()));
    }
}

#[test]
fn ordinary_string_alias_resolves_to_text_through_calls_and_nominals() {
    let source = r#"
        type String = Text;
        echo(value: String) -> String { value }
        make() -> Message { Message::Named(Label { text: echo("alias") }) }
        struct Label { text: String }
        enum Message { Empty, Named(Label) }
        main() -> { () }
    "#;
    let artifact = compile_raw_source("aliases.glorious", source).unwrap();
    let nominal_names = artifact
        .types
        .iter()
        .filter_map(|ty| match ty.representation() {
            Type::Struct { name, .. } | Type::Enum { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        nominal_names
            .iter()
            .filter(|name| **name == "Label")
            .count(),
        1
    );
    assert_eq!(
        nominal_names
            .iter()
            .filter(|name| **name == "Message")
            .count(),
        1
    );
    assert!(!nominal_names.contains(&"String"));
    let make = artifact
        .functions
        .iter()
        .position(|function| function.name == "make")
        .unwrap() as u32;
    let message_type = artifact.functions[make as usize].return_type;
    let Type::Restricted { base, .. } = &artifact.types[message_type as usize] else {
        panic!("Message must be a nominal enum")
    };
    let Type::Enum { variants, .. } = base.as_ref() else {
        panic!("Message must be an enum")
    };
    let label_type = variants[1].fields[0].ty;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(make, vec![])
            .unwrap(),
        Value::aggregate_with_variant(
            message_type,
            Some(1),
            [Value::aggregate(label_type, [Value::Text("alias".into())])]
        )
    );
}

#[test]
fn aliases_resolve_forward_chains_and_nominal_targets_without_descriptors() {
    let source = r#"
        infixl 30 +;
        type Count = Later;
        type Later = u16;
        type Wrapped = Boxed;
        increment(value: Count) -> Later { value + 1 }
        late_identity(value: Wrapped) -> Boxed { value }
        struct Boxed { value: Count }
        main() -> { () }
    "#;
    let artifact = compile_raw_source("alias-chain.glorious", source).unwrap();
    let nominal_names = artifact
        .types
        .iter()
        .filter_map(|ty| match ty.representation() {
            Type::Struct { name, .. } | Type::Enum { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        nominal_names
            .iter()
            .filter(|name| **name == "Boxed")
            .count(),
        1
    );
    for alias in ["Count", "Later", "Wrapped"] {
        assert!(
            !nominal_names.contains(&alias),
            "aliases have no runtime identity"
        );
    }
    let increment = artifact
        .functions
        .iter()
        .position(|function| function.name == "increment")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(increment, vec![Value::U64(40)])
            .unwrap(),
        Value::U64(41)
    );
}

#[test]
fn qualified_constructor_aliases_are_identity_preserving_and_name_agnostic() {
    let option = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        type Option<T> = Result<T, ()>;
        let Option::Some = Result::Ok;
        answer() -> Option<i64> { Option::Some(42) }
        main() -> { () }
    "#;
    let renamed = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        type Maybe<T> = Result<T, ()>;
        let Maybe::Present = Result::Ok;
        answer() -> Maybe<i64> { Maybe::Present(42) }
        main() -> { () }
    "#;
    let artifact = compile_raw_source("option-constructor-alias.glorious", option).unwrap();
    let renamed_artifact =
        compile_raw_source("renamed-constructor-alias.glorious", renamed).unwrap();
    assert_eq!(artifact.encode(), renamed_artifact.encode());
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::aggregate_with_variant(19, Some(0), [Value::I64(42)])
    );
}

#[test]
fn qualified_callable_aliases_rewrite_to_generic_ordinary_function_identities() {
    let source = r#"
        struct Box<T> { private value: T }
        alias_identity<T>(value: T) -> T { value }
        let Box::identity = alias_identity;
        let Box::again = Box::identity;
        answer() -> i64 { Box::again(42) }
        main() -> { () }
    "#;
    let artifact = compile_raw_source("associated-callable-alias.glorious", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact.clone()).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
    assert!(
        artifact
            .functions
            .iter()
            .all(|function| !function.name.contains("Box::")),
        "associated aliases must not acquire runtime callable identities"
    );
}

#[test]
fn qualified_callable_aliases_reject_invalid_owners_targets_and_cycles() {
    let cases = [
        (
            "invalid-associated-owner.glorious",
            "missing_owner_target<T>(value:T)->T{value} let Missing::identity = missing_owner_target; main()->{()}",
            "`Missing` is not a declared type alias, nominal type, or predefined type",
        ),
        (
            "invalid-associated-target.glorious",
            "struct Box<T>{value:T} let Box::identity = missing; main()->{()}",
            "associated callable alias target `missing` is not an ordinary function",
        ),
        (
            "associated-callable-cycle.glorious",
            "struct Box<T>{value:T} let Box::first = Box::second; let Box::second = Box::first; main()->{()}",
            "alias cycle contains `Box::",
        ),
    ];
    for (name, source, expected) in cases {
        let diagnostics = compile_raw_source(name, source).unwrap_err();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains(expected)),
            "{name}: {diagnostics:#?}"
        );
    }
}

#[test]
fn qualified_constructor_alias_chains_rewrite_construction_and_handler_patterns() {
    let source = r#"
        enum Outcome { Good(i64), Bad }
        type Maybe = Outcome;
        type Optional = Maybe;
        let Optional::Present = Maybe::Some;
        let Optional::Absent = Outcome::Bad;
        let Maybe::Some = Outcome::Good;
        Some() -> i64 { 2 }
        effect Inspect { inspect(value: Outcome) -> ! }
        selected() -> i64 {
            handle perform Inspect::inspect(Optional::Present(40)) {
                Inspect::inspect(Optional::Present(value)) => value + Some(),
                Inspect::inspect(Optional::Absent) => 0
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("constructor-alias-chain.glorious", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn qualified_constructor_alias_cycles_are_rejected_deterministically() {
    let source = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        type Option<T> = Result<T, ()>;
        let Option::First = Option::Second;
        let Option::Second = Option::First;
        main() -> { () }
    "#;
    let diagnostics = compile_raw_source("constructor-alias-cycle.glorious", source).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("constructor alias cycle contains `Option::")),
        "{diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.as_deref() == Some("G1BC002")),
        "{diagnostics:#?}"
    );
}

#[test]
fn constructor_alias_declaration_order_does_not_change_artifact_bytes() {
    let first = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        type Option<T> = Result<T, ()>;
        let Option::Some = Result::Ok;
        let Option::Failure = Result::Err;
        answer() -> Option<i64> { Option::Some(42) }
        main() -> { () }
    "#;
    let second = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        type Option<T> = Result<T, ()>;
        let Option::Failure = Result::Err;
        let Option::Some = Result::Ok;
        answer() -> Option<i64> { Option::Some(42) }
        main() -> { () }
    "#;
    assert_eq!(
        compile_raw_source("first-constructor-order.glorious", first)
            .unwrap()
            .encode(),
        compile_raw_source("second-constructor-order.glorious", second)
            .unwrap()
            .encode()
    );
}

#[test]
fn qualified_constructor_aliases_reject_wrong_owner_target_arity_and_duplicates() {
    let cases = [
        (
            "wrong-owner.glorious",
            "enum Result<T, E> { Ok(T), Err(E) } enum Other<T> { Item(T) } type Wrong<T> = Other<T>; let Wrong::Some = Result::Ok; main() -> { () }",
            "belongs to `Other`, but its target belongs to `Result`",
        ),
        (
            "wrong-target.glorious",
            "enum Result<T, E> { Ok(T), Err(E) } type Option<T> = Result<T, ()>; let Option::Some = Result::Missing; main() -> { () }",
            "has no constructor `Missing`",
        ),
        (
            "wrong-arity.glorious",
            "enum Result<T, E> { Ok(T), Err(E) } type Option<T> = Result<T, ()>; let Option::Some = Result::Ok; answer() -> Option<i64> { Option::Some() } main() -> { () }",
            "expects 1 payload value(s), got 0",
        ),
        (
            "duplicate-constructor-alias.glorious",
            "enum Result<T, E> { Ok(T), Err(E) } type Option<T> = Result<T, ()>; let Option::Some = Result::Ok; let Option::Some = Result::Ok; main() -> { () }",
            "value declared more than once",
        ),
    ];
    for (name, source, needle) in cases {
        let errors = compile_raw_source(name, source).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains(needle) || error.title.contains(needle)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn alias_declaration_order_does_not_change_canonical_artifact_bytes() {
    let first = r#"
        type SourceString = Text;
        type Name = SourceString;
        value() -> Name { "stable" }
        main() -> { () }
    "#;
    let second = r#"
        type Name = SourceString;
        type SourceString = Text;
        value() -> Name { "stable" }
        main() -> { () }
    "#;
    assert_eq!(
        compile_source_to_bytecode("first.glorious", first)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("second.glorious", second)
            .unwrap()
            .encode()
    );
}

#[test]
fn invalid_aliases_and_bare_string_have_stable_diagnostics() {
    for (source, needle, code) in [
        (
            "type A = B; type B = A; main() -> { () }",
            "type alias cycle",
            "G1BC002",
        ),
        (
            "type A = Missing; main() -> { () }",
            "unknown target `Missing`",
            "G1BC002",
        ),
        (
            "type A = List<i64>; main() -> { () }",
            "complex type alias target",
            "G1BC001",
        ),
        (
            "value() -> BareString { \"no intrinsic alias\" } main() -> { () }",
            "supported monomorphic type",
            "G1BC002",
        ),
    ] {
        let errors = compile_source_to_bytecode("bad-alias.glorious", source).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains(needle) && error.code.as_deref() == Some(code)),
            "{errors:#?}"
        );
    }
}

#[test]
fn bytes_is_a_signature_and_alias_type_without_inventing_a_literal() {
    compile_source_to_bytecode(
        "bytes-types.glorious",
        "type Blob = Bytes; echo(value: Blob) -> Bytes { value } main() -> () { () }",
    )
    .unwrap();
}

#[test]
fn preserved_invalid_generic_goals_reject_before_type_resolution() {
    let (source, needle, marked) = (
        "run(body: i64) -> i64 where i64: Use<[0, 0]> { body } main() -> { () }",
        "where-clause goal",
        "i64: Use<[0, 0]>",
    );
    let errors = compile_source_to_bytecode("structured-reject.glorious", source).unwrap_err();
    let error = errors
        .iter()
        .find(|error| error.message.contains(needle))
        .unwrap_or_else(|| panic!("missing {needle}: {errors:#?}"));
    assert_eq!(&source[error.span.unwrap().range()], marked);
    assert_eq!(error.code.as_deref(), Some("G1BC001"));
}

#[test]
fn instantiated_effect_aliases_and_callable_rows_resolve_exactly() {
    let source = r#"
        effect Ask<E> { [1,1] ask(value: E) -> E }
        cases Common = {Ask<i64>};
        run() -> i64 / {Common} { perform Ask<i64>::ask(42) }
        selected() -> i64 {
            handle { run() } {
                Ask<i64>::ask(value) with continuation => resume(continuation, value)
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("instantiated-effect-alias.glorious", source).unwrap();
    let repeated = compile_source_to_phases("instantiated-effect-alias.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(phases.artifact.encode(), repeated.artifact.encode());
    let ask = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| {
            protocol.display_name == "Ask" && protocol.type_arguments == [grandiose_vm::I64]
        })
        .unwrap() as u32;
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == "run")
            .unwrap()
            .outward_protocols,
        [ask]
    );
    assert!(
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == "selected")
            .unwrap()
            .outward_protocols
            .is_empty()
    );
}

#[test]
fn immutable_globals_support_source_string_aliases_and_callable_uses() {
    let source = r#"
        let greeting = "hello";
        read() -> String { greeting }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("global-string.glorious", source).unwrap();
    let read = artifact
        .functions
        .iter()
        .position(|function| function.name == "read")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact.clone()).unwrap())
            .run(read, vec![])
            .unwrap(),
        Value::Text("hello".into())
    );
    assert!(artifact.functions.iter().any(|function| {
        function.name.starts_with("$global$")
            && function.params.is_empty()
            && function.return_type == grandiose_vm::TEXT
    }));
}

#[test]
fn nominal_global_factories_return_fresh_independent_aggregates() {
    let source = r#"
        struct Point { x: i64, y: i64 }
        let origin = Point { y: 2, x: 1 };
        get() -> Point { origin }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("global-nominal.glorious", source).unwrap();
    let get = artifact
        .functions
        .iter()
        .position(|function| function.name == "get")
        .unwrap() as u32;
    let vm = Vm::new(verify(artifact).unwrap());
    let first = vm.run(get, vec![]).unwrap();
    let second = vm.run(get, vec![]).unwrap();
    let (Value::Aggregate(first), Value::Aggregate(second)) = (&first, &second) else {
        panic!("expected aggregates")
    };
    assert!(!grandiose_vm::value::ArenaObject::ptr_eq(first, second));
    assert_eq!(first.borrow().fields, second.borrow().fields);
}

#[test]
fn globals_resolve_forward_and_chained_dependencies() {
    let source = r#"
        let first = second;
        let second = third;
        let third = Choice::Value(9);
        enum Choice { Empty, Value(i64) }
        read() -> Choice { first }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("global-forward.glorious", source).unwrap();
    let read = artifact
        .functions
        .iter()
        .position(|function| function.name == "read")
        .unwrap() as u32;
    let choice = artifact.functions[read as usize].return_type;
    assert!(matches!(
        artifact.types[choice as usize].representation(),
        Type::Enum { name, .. } if name == "Choice"
    ));
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(read, vec![])
            .unwrap(),
        Value::aggregate_with_variant(choice, Some(1), [Value::I64(9)])
    );
}

#[test]
fn global_declaration_order_does_not_change_canonical_bytes() {
    let first = r#"
        let alpha = "a";
        let beta = alpha;
        read() -> Text { beta }
        main() -> { () }
    "#;
    let second = r#"
        let beta = alpha;
        let alpha = "a";
        read() -> Text { beta }
        main() -> { () }
    "#;
    assert_eq!(
        compile_source_to_bytecode("first.glorious", first)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("second.glorious", second)
            .unwrap()
            .encode()
    );
}

#[test]
fn invalid_globals_report_duplicates_cycles_runtime_calls_and_polymorphism() {
    let duplicate = compile_source_to_bytecode(
        "duplicate-global.glorious",
        "let value = 1; let value = 2; main() -> { () }",
    )
    .unwrap_err();
    assert!(
        duplicate
            .iter()
            .any(|error| error.code.as_deref() == Some("G0006"))
    );

    for (source, needle) in [
        (
            "let first = second; let second = first; main() -> { () }",
            "global dependency cycle",
        ),
        (
            "let value = local_identity(1); local_identity<T>(value: T) -> T { value } main() -> { () }",
            "monomorphic",
        ),
        (
            "let values = []; main() -> { () }",
            "closed monomorphic literal",
        ),
    ] {
        let errors = compile_source_to_bytecode("bad-global.glorious", source).unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains(needle)
                && error.code.as_deref() == Some("G1BC001")
                || error.message.contains(needle) && error.code.as_deref() == Some("G1BC002")),
            "{errors:#?}"
        );
    }
}

#[test]
fn typed_core_and_mir_text_and_fingerprints_are_deterministic() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        make(value: i64) -> Pair { Pair { right: value + 1, left: value } }
        read(value: Pair) -> i64 { value.right }
        main() -> { () }
    "#;
    let first = compile_source_to_phases("phases.glorious", source).unwrap();
    let second = compile_source_to_phases("phases.glorious", source).unwrap();
    assert_eq!(first.core.canonical_text(), second.core.canonical_text());
    assert_eq!(first.mir.canonical_text(), second.mir.canonical_text());
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
}

#[test]
fn provisional_typing_text_and_fingerprint_are_canonical_across_reordering() {
    let first = compile_source_to_phases(
        "first.glorious",
        "id(value: &i64) -> &i64 { value } main() -> { let n = 4; let r = &n; id(r); () }",
    )
    .unwrap();
    let reordered = compile_source_to_phases(
        "second.glorious",
        "main() -> { let n = 4; let r = &n; id(r); () } id(value: &i64) -> &i64 { value }",
    )
    .unwrap();

    assert_eq!(first.provisional_text(), reordered.provisional_text());
    assert_eq!(
        first.provisional_fingerprint(),
        reordered.provisional_fingerprint()
    );
    assert!(first.provisional_text().contains("body Function(\"id\")"));
    assert!(first.provisional_text().contains("borrow#0"));
}

#[test]
fn provisional_typing_preserves_alias_reference_nesting_and_shadow_keys() {
    let phases = compile_source_to_phases(
        "provisional.glorious",
        r#"
            type Shared = &i64;
            type Nested = &mut Shared;
            forward(value: Nested) -> Nested { value }
            shadow(value: i64) -> i64 {
                let value = value + 1;
                { let value = value + 1; value }
            }
            main() -> { () }
        "#,
    )
    .unwrap();

    let text = phases.provisional_text();
    assert!(text.contains("&mut &i64"));
    assert!(text.contains("local#1"));
    assert!(text.contains("local#2"));
    // Successful compilation exercises the provisional-to-Core structural
    // equality guard for every supported ordinary expression in these bodies.
}

#[test]
fn core_carries_exact_types_and_resolved_nominal_member_ids() {
    use grandiose::compiler_core::ExprKind;

    let phases = compile_source_to_phases(
        "core-evidence.glorious",
        r#"
            enum Choice { Empty, Number(i64) }
            struct Boxed { choice: Choice }
            make() -> Boxed { Boxed { choice: Choice::Number(4) } }
            project(value: Boxed) -> Choice { value.choice }
            main() -> { () }
        "#,
    )
    .unwrap();
    let artifact_boxed = nominal_type_id(&phases.artifact, "Boxed");
    let artifact_choice = nominal_type_id(&phases.artifact, "Choice");
    assert!(matches!(
        phases.artifact.types[artifact_boxed as usize].representation(),
        Type::Struct { fields, .. } if fields.len() == 1 && fields[0].ty == artifact_choice
    ));
    let make = phases
        .core
        .functions
        .iter()
        .find(|function| function.name == "make")
        .unwrap();
    let ExprKind::Block { tail, .. } = &make.body.kind else {
        panic!("body is normalized as a block")
    };
    let ExprKind::Construct {
        nominal, fields, ..
    } = &tail.kind
    else {
        panic!("expected struct construction")
    };
    let core_boxed = *nominal;
    assert_eq!(*nominal, tail.ty);
    assert_eq!(fields[0].field, 0);
    let ExprKind::Construct {
        nominal, variant, ..
    } = &fields[0].value.kind
    else {
        panic!("expected enum construction")
    };
    let core_choice = *nominal;
    assert_ne!(core_boxed, core_choice);
    assert_eq!(*nominal, fields[0].value.ty);
    assert_eq!(*variant, Some(1));

    let project = phases
        .core
        .functions
        .iter()
        .find(|function| function.name == "project")
        .unwrap();
    let ExprKind::Block { tail, .. } = &project.body.kind else {
        panic!()
    };
    let ExprKind::Project { field, copy, .. } = tail.kind else {
        panic!("expected resolved projection")
    };
    assert_eq!((field, copy, tail.ty), (0, true, core_choice));
}

#[test]
fn mir_owns_final_use_transfer_and_explicit_operand_modes() {
    let phases = compile_source_to_phases_with_options(
        "mir-cleanup.glorious",
        r#"
            shadow(value: i64) -> i64 {
                let first = value + 1;
                let second = first + 1;
                second
            }
            main() -> { () }
        "#,
        CompileOptions {
            optimization_level: OptimizationLevel::O0,
        },
    )
    .unwrap();
    let function = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "shadow")
        .unwrap();
    assert!(
        function.return_cleanup.is_empty(),
        "every scalar owner is discharged by its inferred final transfer"
    );
    assert!(function.blocks.iter().any(|block| matches!(
        block.terminator,
        grandiose::compiler_mir::Terminator::Return {
            value: Some(grandiose::compiler_mir::Operand {
                mode: grandiose::compiler_mir::UseMode::Move,
                ..
            })
        }
    )));
}

#[test]
fn accepted_pure_program_has_matching_interpreter_and_vm_outcome() {
    use grandiose::{diagnostic::Diagnostic, eval::Host, span::Span};

    struct NoHost;
    impl Host for NoHost {
        fn perform(
            &mut self,
            _effect: &str,
            _operation: &str,
            _args: Vec<grandiose::eval::Value>,
            span: Span,
        ) -> Result<grandiose::eval::Value, Diagnostic> {
            Err(Diagnostic::error(
                "unexpected effect",
                "pure program performed an effect",
                span,
            ))
        }
    }

    let source = r#"
        let base = 20;
        twice(value: i64) -> i64 { value * 2 }
        consume(value: i64) -> { () }
        main() -> { consume(twice(base) + 2) }
    "#;
    let interpreted =
        grandiose::run_source("differential.glorious", source, vec![], &mut NoHost).unwrap();
    let artifact = compile_source_to_bytecode("differential.glorious", source).unwrap();
    let executed = Vm::new(verify(artifact.clone()).unwrap())
        .run(artifact.entry_function.unwrap(), vec![])
        .unwrap();
    assert_eq!(interpreted, grandiose::eval::Value::Unit);
    assert_eq!(executed, Value::Unit);
}

#[test]
fn marker_constraints_gate_generic_specialization_and_recursive_constructor_evidence() {
    let source = r#"
        trait Marker {}
        struct Box<T> { value: T }
        impl Marker for i64 {}
        impl<T> Marker for Box<T> where T: Marker {}
        marker_identity<T>(value: T) -> T where T: Marker { value }
        boxed() -> Box<i64> { Box { value: 42 } }
        main() -> {
            marker_identity(42);
            marker_identity(boxed());
            ()
        }
    "#;
    let artifact = compile_source_to_bytecode("marker.glorious", source).unwrap();
    let result = Vm::new(verify(artifact.clone()).unwrap())
        .run(artifact.entry_function.unwrap(), vec![])
        .unwrap();
    assert_eq!(result, Value::Unit);

    let missing = r#"
        trait Marker {}
        impl Marker for i64 {}
        marker_identity<T>(value: T) -> T where T: Marker { value }
        main() -> { marker_identity("not marked"); () }
    "#;
    let errors = compile_source_to_bytecode("marker-missing.glorious", missing).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.span.is_some()
            && error.code.is_some()
            && (error.message.contains("marker") || error.message.contains("specialization"))
    }));
}

#[test]
fn parameterized_trait_relations_gate_specialization_use_and_drop() {
    let source = r#"
        trait Rel<To> {}
        struct Flag { marker: i64 }
        struct Wrap<T> { value: T }
        struct Ticket<T> { marker: i64 }
        struct Bomb<T> { value: T }
        impl Rel<i64> for Text {}
        impl Rel<Text> for i64 {}
        impl Rel<i64> for Flag {}
        impl Rel<Text> for Flag {}
        impl<T, U> Rel<Wrap<U>> for Wrap<T> where T: Rel<U> {}
        impl<T> Use<[0,1]> for Ticket<T> where T: Rel<i64> {}
        impl<T> Drop for Bomb<T> where T: Rel<i64> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        relay<T>(value: T) -> T where T: Rel<i64> { value }
        relay_wrapped<T>(value: Wrap<T>) -> Wrap<T>
            where Wrap<T>: Rel<Wrap<i64>> { value }
        text_answer() -> Text { relay("relation") }
        wrapped_answer() -> Wrap<Text> {
            relay_wrapped(Wrap { value: "wrapped" })
        }
        ticket_yes(value: Ticket<Text>) -> Ticket<Text> { value }
        ticket_no(value: Ticket<i64>) -> Ticket<i64> { value }
        bomb_yes(value: Bomb<Text>) -> Bomb<Text> { value }
        bomb_no(value: Bomb<i64>) -> Bomb<i64> { value }
        make_bomb() -> Bomb<Text> { Bomb { value: "boom" } }
        main() -> { let bomb = make_bomb(); () }
    "#;
    let phases = compile_source_to_phases("parameterized-relations.glorious", source).unwrap();
    let repeated = compile_source_to_phases("parameterized-relations.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let parameter = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    let ticket_yes = parameter("ticket_yes");
    let ticket_no = parameter("ticket_no");
    assert!(!phases.artifact.types[ticket_yes as usize].claimed_duplicable());
    assert!(phases.artifact.types[ticket_yes as usize].claimed_zero_use_allowed());
    assert!(phases.artifact.types[ticket_no as usize].claimed_duplicable());
    assert!(phases.artifact.types[ticket_no as usize].claimed_zero_use_allowed());
    let bomb_yes = parameter("bomb_yes");
    let bomb_no = parameter("bomb_no");
    assert!(
        phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == bomb_yes)
    );
    assert!(
        !phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == bomb_no)
    );
    for prefix in ["$specialization$relay#", "$specialization$relay_wrapped#"] {
        assert_eq!(
            phases
                .artifact
                .functions
                .iter()
                .filter(|function| function.name.starts_with(prefix))
                .count(),
            1
        );
    }

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    let text_answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "text_answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified.clone()).run(text_answer, vec![]).unwrap(),
        Value::Text("relation".into())
    );
    let wrapped_answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "wrapped_answer")
        .unwrap() as u32;
    let wrapped = phases.artifact.functions[wrapped_answer as usize].return_type;
    assert_eq!(
        Vm::new(verified.clone())
            .run(wrapped_answer, vec![])
            .unwrap(),
        Value::aggregate(wrapped, [Value::Text("wrapped".into())])
    );
    let error = Vm::new(verified)
        .run(phases.artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");

    let reordered = r#"
        main() -> { let bomb = make_bomb(); () }
        make_bomb() -> Bomb<Text> { Bomb { value: "boom" } }
        bomb_no(value: Bomb<i64>) -> Bomb<i64> { value }
        bomb_yes(value: Bomb<Text>) -> Bomb<Text> { value }
        ticket_no(value: Ticket<i64>) -> Ticket<i64> { value }
        ticket_yes(value: Ticket<Text>) -> Ticket<Text> { value }
        wrapped_answer() -> Wrap<Text> {
            relay_wrapped(Wrap { value: "wrapped" })
        }
        text_answer() -> Text { relay("relation") }
        relay_wrapped<T>(value: Wrap<T>) -> Wrap<T>
            where Wrap<T>: Rel<Wrap<i64>> { value }
        relay<T>(value: T) -> T where T: Rel<i64> { value }
        impl<T> Drop for Bomb<T> where T: Rel<i64> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        impl<T> Use<[0,1]> for Ticket<T> where T: Rel<i64> {}
        impl<T, U> Rel<Wrap<U>> for Wrap<T> where T: Rel<U> {}
        impl Rel<Text> for Flag {}
        impl Rel<i64> for Flag {}
        impl Rel<Text> for i64 {}
        impl Rel<i64> for Text {}
        struct Bomb<T> { value: T }
        struct Ticket<T> { marker: i64 }
        struct Wrap<T> { value: T }
        struct Flag { marker: i64 }
        trait Rel<To> {}
    "#;
    assert_eq!(
        compile_source_to_bytecode("parameterized-relations-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn parameterized_trait_relations_reject_missing_and_incoherent_evidence() {
    let missing = r#"
        trait Rel<To> {}
        require_evidence<T>(value: T) -> T where T: Rel<i64> { value }
        bad() -> Text { require_evidence("missing") }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("missing-parameterized-relation.glorious", missing).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && (error.message.contains("Rel")
                    || error.message.contains("marker")
                    || error.message.contains("specialization"))
        }),
        "{errors:#?}"
    );

    let cases = [
        (
            "overlap",
            "trait Rel<To> {} struct Box<T> { value: T } impl<T> Rel<T> for Box<T> {} impl Rel<i64> for Box<i64> {} main() -> { () }",
            "overlap",
        ),
        (
            "wrong-impl-arity",
            "trait Rel<To> {} impl Rel<i64, Text> for i64 {} main() -> { () }",
            "arity",
        ),
        (
            "wrong-goal-arity",
            "trait Rel<To> {} require_evidence<T>(value: T) -> T where T: Rel { value } main() -> { () }",
            "arity",
        ),
        (
            "unconstrained-binder",
            "trait Rel<To> {} struct Box<T> { value: T } impl<T, U> Rel<i64> for Box<T> {} main() -> { () }",
            "constrained",
        ),
    ];
    for (name, source, needle) in cases {
        let errors =
            compile_source_to_bytecode(&format!("bad-parameterized-{name}.glorious"), source)
                .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.is_some() && error.span.is_some() && error.message.contains(needle)
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn explicit_negative_evidence_gates_specialization_use_and_drop() {
    let source = r#"
        trait Rel<To> {}
        trait Seed {}
        struct Flag { marker: i64 }
        struct Wrap<T> { value: T }
        struct Ticket<T> { marker: i64 }
        struct Bomb<T> { value: T }
        impl Seed for Text {}
        impl !Rel<i64> for Text {}
        impl Rel<i64> for i64 {}
        impl !Rel<Text> for i64 {}
        impl !Rel<Text> for i64 {}
        impl<T> !Rel<Flag> for Wrap<T> where T: Seed {}
        impl<T> !Rel<Wrap<i64>> for Wrap<T> where T: !Rel<i64> {}
        impl<T> Use<[0,1]> for Ticket<T> where T: !Rel<i64> {}
        impl<T> Drop for Bomb<T> where T: !Rel<i64> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        deny_i64<T>(value: T) -> T where T: !Rel<i64> { value }
        deny_text<T>(value: T) -> T where T: !Rel<Text> { value }
        deny_flag<T>(value: T) -> T where T: !Rel<Flag> { value }
        deny_wrapped<T>(value: T) -> T where T: !Rel<Wrap<i64>> { value }
        text_answer() -> Text { deny_i64("negative") }
        integer_answer() -> i64 { deny_text(42) }
        conditional_answer() -> Wrap<Text> {
            deny_flag(Wrap { value: "conditional" })
        }
        nested_negative_answer() -> Wrap<Text> {
            deny_wrapped(Wrap { value: "nested" })
        }
        ticket_negative(value: Ticket<Text>) -> Ticket<Text> { value }
        ticket_refuted(value: Ticket<i64>) -> Ticket<i64> { value }
        ticket_missing(value: Ticket<Flag>) -> Ticket<Flag> { value }
        bomb_negative(value: Bomb<Text>) -> Bomb<Text> { value }
        bomb_refuted(value: Bomb<i64>) -> Bomb<i64> { value }
        bomb_missing(value: Bomb<Flag>) -> Bomb<Flag> { value }
        make_bomb() -> Bomb<Text> { Bomb { value: "boom" } }
        main() -> { let bomb = make_bomb(); () }
    "#;
    let phases = compile_source_to_phases("negative-evidence.glorious", source).unwrap();
    let repeated = compile_source_to_phases("negative-evidence.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let parameter = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    let ticket_negative = parameter("ticket_negative");
    let ticket_refuted = parameter("ticket_refuted");
    let ticket_missing = parameter("ticket_missing");
    assert!(!phases.artifact.types[ticket_negative as usize].claimed_duplicable());
    assert!(phases.artifact.types[ticket_negative as usize].claimed_zero_use_allowed());
    for ty in [ticket_refuted, ticket_missing] {
        assert!(phases.artifact.types[ty as usize].claimed_duplicable());
        assert!(phases.artifact.types[ty as usize].claimed_zero_use_allowed());
    }

    let bomb_negative = parameter("bomb_negative");
    let bomb_refuted = parameter("bomb_refuted");
    let bomb_missing = parameter("bomb_missing");
    assert!(
        phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == bomb_negative)
    );
    for ty in [bomb_refuted, bomb_missing] {
        assert!(!phases.artifact.drop_glue.iter().any(|glue| glue.ty == ty));
    }
    for prefix in [
        "$specialization$deny_i64#",
        "$specialization$deny_text#",
        "$specialization$deny_flag#",
        "$specialization$deny_wrapped#",
    ] {
        assert_eq!(
            phases
                .artifact
                .functions
                .iter()
                .filter(|function| function.name.starts_with(prefix))
                .count(),
            1
        );
    }

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    for (name, expected) in [
        ("text_answer", Value::Text("negative".into())),
        ("integer_answer", Value::I64(42)),
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            expected
        );
    }
    for (name, expected) in [
        ("conditional_answer", "conditional"),
        ("nested_negative_answer", "nested"),
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        let result_type = phases.artifact.functions[function as usize].return_type;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::aggregate(result_type, [Value::Text(expected.into())])
        );
    }
    let error = Vm::new(verified)
        .run(phases.artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");

    let reordered = r#"
        main() -> { let bomb = make_bomb(); () }
        make_bomb() -> Bomb<Text> { Bomb { value: "boom" } }
        bomb_missing(value: Bomb<Flag>) -> Bomb<Flag> { value }
        bomb_refuted(value: Bomb<i64>) -> Bomb<i64> { value }
        bomb_negative(value: Bomb<Text>) -> Bomb<Text> { value }
        ticket_missing(value: Ticket<Flag>) -> Ticket<Flag> { value }
        ticket_refuted(value: Ticket<i64>) -> Ticket<i64> { value }
        ticket_negative(value: Ticket<Text>) -> Ticket<Text> { value }
        nested_negative_answer() -> Wrap<Text> {
            deny_wrapped(Wrap { value: "nested" })
        }
        conditional_answer() -> Wrap<Text> {
            deny_flag(Wrap { value: "conditional" })
        }
        integer_answer() -> i64 { deny_text(42) }
        text_answer() -> Text { deny_i64("negative") }
        deny_wrapped<T>(value: T) -> T where T: !Rel<Wrap<i64>> { value }
        deny_flag<T>(value: T) -> T where T: !Rel<Flag> { value }
        deny_text<T>(value: T) -> T where T: !Rel<Text> { value }
        deny_i64<T>(value: T) -> T where T: !Rel<i64> { value }
        impl<T> Drop for Bomb<T> where T: !Rel<i64> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        impl<T> Use<[0,1]> for Ticket<T> where T: !Rel<i64> {}
        impl<T> !Rel<Wrap<i64>> for Wrap<T> where T: !Rel<i64> {}
        impl<T> !Rel<Flag> for Wrap<T> where T: Seed {}
        impl !Rel<Text> for i64 {}
        impl !Rel<Text> for i64 {}
        impl Rel<i64> for i64 {}
        impl !Rel<i64> for Text {}
        impl Seed for Text {}
        struct Bomb<T> { value: T }
        struct Ticket<T> { marker: i64 }
        struct Wrap<T> { value: T }
        struct Flag { marker: i64 }
        trait Seed {}
        trait Rel<To> {}
    "#;
    assert_eq!(
        compile_source_to_bytecode("negative-evidence-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn negative_evidence_rejects_missing_refuted_and_incoherent_proofs() {
    let missing = r#"
        trait Rel<To> {}
        deny<T>(value: T) -> T where T: !Rel<i64> { value }
        bad() -> Text { deny("missing") }
        main() -> { () }
    "#;
    let missing_errors =
        compile_source_to_bytecode("missing-negative-evidence.glorious", missing).unwrap_err();
    assert!(
        missing_errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error.message.contains("negative")
                && (error.message.contains("evidence") || error.message.contains("specialization"))
        }),
        "{missing_errors:#?}"
    );

    let refuted = r#"
        trait Rel<To> {}
        impl Rel<i64> for Text {}
        deny<T>(value: T) -> T where T: !Rel<i64> { value }
        bad() -> Text { deny("refuted") }
        main() -> { () }
    "#;
    let refuted_errors =
        compile_source_to_bytecode("refuted-negative-evidence.glorious", refuted).unwrap_err();
    assert!(
        refuted_errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error.message.to_ascii_lowercase().contains("refut")
        }),
        "{refuted_errors:#?}"
    );
    assert_ne!(
        missing_errors
            .iter()
            .map(|error| error.message.as_str())
            .collect::<Vec<_>>(),
        refuted_errors
            .iter()
            .map(|error| error.message.as_str())
            .collect::<Vec<_>>()
    );

    let cases = [
        (
            "positive-negative-overlap",
            "trait Rel<To> {} impl Rel<i64> for Text {} impl !Rel<i64> for Text {} main() -> { () }",
            "overlap",
        ),
        (
            "joint-argument-overlap",
            "trait Rel<To> {} struct Box<T> { value: T } impl<T> Rel<T> for Box<T> {} impl !Rel<i64> for Box<i64> {} main() -> { () }",
            "overlap",
        ),
        (
            "unconstrained-binder",
            "trait Rel<To> {} struct Box<T> { value: T } impl<T, U> !Rel<i64> for Box<T> {} main() -> { () }",
            "constrained",
        ),
        (
            "negative-body",
            "trait Rel<To> {} impl !Rel<i64> for Text { item() -> { () } } main() -> { () }",
            "method bodies",
        ),
        (
            "negative-drop",
            "struct Box { value: i64 } impl !Drop for Box {} main() -> { () }",
            "intrinsic",
        ),
        (
            "negative-use",
            "struct Box { value: i64 } impl !Use for Box {} main() -> { () }",
            "intrinsic",
        ),
    ];
    for (name, source, needle) in cases {
        let errors = compile_source_to_bytecode(&format!("bad-negative-{name}.glorious"), source)
            .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.is_some()
                    && error.span.is_some()
                    && error.message.to_ascii_lowercase().contains(needle)
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn associated_types_normalize_ground_layouts_and_gate_equality_evidence() {
    let source = r#"
        trait Value { type Item; }
        struct Box<T> { value: T }
        struct Wrap<T> { value: T }
        struct Projected { item: <Box<Text> as Value>::Item }
        struct Good { marker: i64 }
        struct Bad { marker: i64 }
        struct Missing { marker: i64 }
        struct Ticket<T> { marker: i64 }
        struct Bomb<T> { value: T }
        impl<T> Value for Box<T> { type Item = Wrap<T>; }
        impl Value for Good { type Item = Text; }
        impl Value for Bad { type Item = i64; }
        impl<T> Use<[0,1]> for Ticket<T> where T: Value<Item=Text> {}
        impl<T> Drop for Bomb<T> where T: Value<Item=Text> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        make_item() -> <Box<Text> as Value>::Item {
            Wrap { value: "projected" }
        }
        read_item(value: <Box<Text> as Value>::Item) -> Text { value.value }
        projection_answer() -> Text {
            let projected = Projected { item: make_item() };
            read_item(projected.item)
        }
        relay<T>(value: T) -> T where Box<T>: Value<Item=Wrap<T>> { value }
        equality_answer() -> Text { relay("equal") }
        ticket_good(value: Ticket<Good>) -> Ticket<Good> { value }
        ticket_bad(value: Ticket<Bad>) -> Ticket<Bad> { value }
        ticket_missing(value: Ticket<Missing>) -> Ticket<Missing> { value }
        bomb_good(value: Bomb<Good>) -> Bomb<Good> { value }
        bomb_bad(value: Bomb<Bad>) -> Bomb<Bad> { value }
        bomb_missing(value: Bomb<Missing>) -> Bomb<Missing> { value }
        make_bomb() -> Bomb<Good> { Bomb { value: Good { marker: 1 } } }
        main() -> { let bomb = make_bomb(); () }
    "#;
    let phases = compile_source_to_phases("associated-types.glorious", source).unwrap();
    let repeated = compile_source_to_phases("associated-types.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let wrap_text = phases
        .artifact
        .types
        .iter()
        .position(|ty| {
            matches!(ty.representation(), Type::Struct { name, fields, .. }
                if name == "Wrap"
                    && fields.len() == 1
                    && fields[0].ty == grandiose_vm::TEXT)
        })
        .expect("the ground associated projection must normalize to Wrap<Text>")
        as u32;
    assert!(phases.artifact.types.iter().any(|ty| {
        matches!(ty.representation(), Type::Struct { name, fields, .. }
            if name == "Projected" && fields.len() == 1 && fields[0].ty == wrap_text)
    }));

    let parameter = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    let ticket_good = parameter("ticket_good");
    let ticket_bad = parameter("ticket_bad");
    let ticket_missing = parameter("ticket_missing");
    assert!(!phases.artifact.types[ticket_good as usize].claimed_duplicable());
    assert!(phases.artifact.types[ticket_good as usize].claimed_zero_use_allowed());
    for ty in [ticket_bad, ticket_missing] {
        assert!(phases.artifact.types[ty as usize].claimed_duplicable());
        assert!(phases.artifact.types[ty as usize].claimed_zero_use_allowed());
    }

    let bomb_good = parameter("bomb_good");
    let bomb_bad = parameter("bomb_bad");
    let bomb_missing = parameter("bomb_missing");
    assert!(
        phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == bomb_good)
    );
    for ty in [bomb_bad, bomb_missing] {
        assert!(!phases.artifact.drop_glue.iter().any(|glue| glue.ty == ty));
    }
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$relay#"))
            .count(),
        1
    );

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    for (name, expected) in [
        ("projection_answer", "projected"),
        ("equality_answer", "equal"),
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::Text(expected.into())
        );
    }
    let error = Vm::new(verified)
        .run(phases.artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");

    let reordered = r#"
        main() -> { let bomb = make_bomb(); () }
        make_bomb() -> Bomb<Good> { Bomb { value: Good { marker: 1 } } }
        bomb_missing(value: Bomb<Missing>) -> Bomb<Missing> { value }
        bomb_bad(value: Bomb<Bad>) -> Bomb<Bad> { value }
        bomb_good(value: Bomb<Good>) -> Bomb<Good> { value }
        ticket_missing(value: Ticket<Missing>) -> Ticket<Missing> { value }
        ticket_bad(value: Ticket<Bad>) -> Ticket<Bad> { value }
        ticket_good(value: Ticket<Good>) -> Ticket<Good> { value }
        equality_answer() -> Text { relay("equal") }
        relay<T>(value: T) -> T where Box<T>: Value<Item=Wrap<T>> { value }
        projection_answer() -> Text {
            let projected = Projected { item: make_item() };
            read_item(projected.item)
        }
        read_item(value: <Box<Text> as Value>::Item) -> Text { value.value }
        make_item() -> <Box<Text> as Value>::Item {
            Wrap { value: "projected" }
        }
        impl<T> Drop for Bomb<T> where T: Value<Item=Text> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        impl<T> Use<[0,1]> for Ticket<T> where T: Value<Item=Text> {}
        impl Value for Bad { type Item = i64; }
        impl Value for Good { type Item = Text; }
        impl<T> Value for Box<T> { type Item = Wrap<T>; }
        struct Bomb<T> { value: T }
        struct Ticket<T> { marker: i64 }
        struct Missing { marker: i64 }
        struct Bad { marker: i64 }
        struct Good { marker: i64 }
        struct Projected { item: <Box<Text> as Value>::Item }
        struct Wrap<T> { value: T }
        struct Box<T> { value: T }
        trait Value { type Item; }
    "#;
    assert_eq!(
        compile_source_to_bytecode("associated-types-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn associated_types_reject_invalid_definitions_equalities_and_projections() {
    let equality_mismatch = r#"
        trait Value { type Item; }
        struct Box<T> { value: T }
        struct Wrap<T> { value: T }
        impl<T> Value for Box<T> { type Item = Wrap<T>; }
        require_evidence<T>(value: T) -> T where Box<T>: Value<Item=Text> { value }
        bad() -> Text { require_evidence("mismatch") }
        main() -> { () }
    "#;
    let mismatch_errors =
        compile_source_to_bytecode("associated-equality-mismatch.glorious", equality_mismatch)
            .unwrap_err();
    assert!(
        mismatch_errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && (error.message.contains("associated")
                    || error.message.contains("equality")
                    || error.message.contains("evidence")
                    || error.message.contains("matching implementation"))
        }),
        "{mismatch_errors:#?}"
    );

    let cases = [
        (
            "missing-definition",
            "trait Value { type Item; } impl Value for Text {} main() -> { () }",
            "missing",
        ),
        (
            "duplicate-declaration",
            "trait Value { type Item; type Item; } main() -> { () }",
            "more than once",
        ),
        (
            "duplicate-definition",
            "trait Value { type Item; } impl Value for Text { type Item=Text; type Item=i64; } main() -> { () }",
            "more than once",
        ),
        (
            "unknown-definition",
            "trait Value { type Item; } impl Value for Text { type Other=Text; } main() -> { () }",
            "extra",
        ),
        (
            "unknown-binding",
            "trait Value { type Item; } require_evidence<T>(value:T)->T where T: Value<Other=Text> { value } main() -> { () }",
            "unknown",
        ),
        (
            "duplicate-binding",
            "trait Value { type Item; } require_evidence<T>(value:T)->T where T: Value<Item=Text, Item=i64> { value } main() -> { () }",
            "more than once",
        ),
        (
            "negative-definition",
            "trait Value { type Item; } impl !Value for Text { type Item=Text; } main() -> { () }",
            "negative",
        ),
        (
            "overlap-different-definitions",
            "trait Value { type Item; } struct Box<T>{value:T} impl<T> Value for Box<T>{type Item=T;} impl Value for Box<Text>{type Item=i64;} main() -> { () }",
            "overlap",
        ),
        (
            "projection-without-impl",
            "trait Value { type Item; } bad(value:<Text as Value>::Item)->{()} main()->{()}",
            "projection",
        ),
        (
            "unresolved-generic-projection",
            "trait Value { type Item; } bad<T>(value:<T as Value>::Item)->Text where T: Value {\"unresolved\"} main()->{()}",
            "projection",
        ),
        (
            "recursive-projection",
            "trait Value { type Item; } impl Value for Text { type Item=<Text as Value>::Item; } bad(value:<Text as Value>::Item)->{()} main()->{()}",
            "projection",
        ),
        (
            "expanding-projection",
            "trait Value { type Item; } struct Box<T>{value:T} impl<T> Value for Box<T>{type Item=<Box<Box<T>> as Value>::Item;} bad(value:<Box<Text> as Value>::Item)->{()} main()->{()}",
            "limit",
        ),
        (
            "associated-default",
            "trait Value { type Item=Text; } main() -> { () }",
            "default",
        ),
    ];
    for (name, source, needle) in cases {
        let errors = compile_source_to_bytecode(&format!("bad-associated-{name}.glorious"), source)
            .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.span.is_some()
                    && (error.code.is_some()
                        || matches!(name, "duplicate-declaration" | "duplicate-definition"))
                    && error.message.to_ascii_lowercase().contains(needle)
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn gat_projections_substitute_every_binder_and_gate_equality_evidence() {
    let source = r#"
        trait Family<C> { type Member<T>; }
        trait Layered { type Out<T>; }
        trait Keyed { type At<K>; }
        struct Box<S> { value: S }
        struct Layer<S, C> {}
        struct Triple<S, C, T> { source: S, context: C, item: T }
        struct Holder { value: <Box<i64> as Family<Text>>::Member<u16> }
        struct Good { marker: i64 }
        struct Bad { marker: i64 }
        struct Missing { marker: i64 }
        struct Ticket<T> { marker: i64 }
        struct Bomb<T> { value: T }
        impl<S, C> Layered for Layer<S, C> {
            type Out<T> = Triple<S, C, T>;
        }
        impl<S, C> Family<C> for Box<S> {
            type Member<T> = <Layer<S, C> as Layered>::Out<T>;
        }
        impl Keyed for Good { type At<K> = K; }
        impl Keyed for Bad { type At<K> = i64; }
        impl<T> Use<[0,1]> for Ticket<T> where T: Keyed<At<Text> = Text> {}
        impl<T> Drop for Bomb<T> where T: Keyed<At<Text> = Text> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        make_member() -> <Box<i64> as Family<Text>>::Member<u16> {
            Triple { source: 41, context: "context", item: 7 }
        }
        read_member(value: <Box<i64> as Family<Text>>::Member<u16>) -> Text {
            value.context
        }
        projection_answer() -> Text {
            let holder = Holder { value: make_member() };
            read_member(holder.value)
        }
        equality_inner<T>(value: T) -> T
            where Box<i64>: Family<Text, Member<T> = Triple<i64, Text, T>> {
            value
        }
        equality_outer<T>(value: T) -> T
            where Box<i64>: Family<Text, Member<T> = Triple<i64, Text, T>> {
            equality_inner(value)
        }
        equality_answer() -> u16 { equality_outer(42) }
        ticket_good(value: Ticket<Good>) -> Ticket<Good> { value }
        ticket_bad(value: Ticket<Bad>) -> Ticket<Bad> { value }
        ticket_missing(value: Ticket<Missing>) -> Ticket<Missing> { value }
        bomb_good(value: Bomb<Good>) -> Bomb<Good> { value }
        bomb_bad(value: Bomb<Bad>) -> Bomb<Bad> { value }
        bomb_missing(value: Bomb<Missing>) -> Bomb<Missing> { value }
        make_bomb() -> Bomb<Good> { Bomb { value: Good { marker: 1 } } }
        main() -> { let bomb = make_bomb(); () }
    "#;
    let phases = compile_source_to_phases("gat-projections.glorious", source).unwrap();
    let repeated = compile_source_to_phases("gat-projections.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let triple = phases
        .artifact
        .types
        .iter()
        .position(|ty| {
            matches!(ty.representation(), Type::Struct { name, fields, .. }
                if name == "Triple"
                    && fields.len() == 3
                    && fields[0].ty == grandiose_vm::I64
                    && fields[1].ty == grandiose_vm::TEXT
                    && fields[2].ty == grandiose_vm::U16)
        })
        .expect("S, C, and T must independently normalize to i64, Text, and u16")
        as u32;
    assert!(phases.artifact.types.iter().any(|ty| {
        matches!(ty.representation(), Type::Struct { name, fields, .. }
            if name == "Holder" && fields.len() == 1 && fields[0].ty == triple)
    }));
    assert_eq!(
        phases
            .artifact
            .types
            .iter()
            .filter(
                |ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Triple")
            )
            .count(),
        1
    );

    let parameter = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    let ticket_good = parameter("ticket_good");
    let ticket_bad = parameter("ticket_bad");
    let ticket_missing = parameter("ticket_missing");
    assert!(!phases.artifact.types[ticket_good as usize].claimed_duplicable());
    assert!(phases.artifact.types[ticket_good as usize].claimed_zero_use_allowed());
    for ty in [ticket_bad, ticket_missing] {
        assert!(phases.artifact.types[ty as usize].claimed_duplicable());
        assert!(phases.artifact.types[ty as usize].claimed_zero_use_allowed());
    }
    let bomb_good = parameter("bomb_good");
    let bomb_bad = parameter("bomb_bad");
    let bomb_missing = parameter("bomb_missing");
    assert!(
        phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == bomb_good)
    );
    for ty in [bomb_bad, bomb_missing] {
        assert!(!phases.artifact.drop_glue.iter().any(|glue| glue.ty == ty));
    }
    for prefix in [
        "$specialization$equality_inner#",
        "$specialization$equality_outer#",
    ] {
        assert_eq!(
            phases
                .artifact
                .functions
                .iter()
                .filter(|function| function.name.starts_with(prefix))
                .count(),
            1
        );
    }

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    let projection_answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "projection_answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified.clone())
            .run(projection_answer, vec![])
            .unwrap(),
        Value::Text("context".into())
    );
    let equality_answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "equality_answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified.clone())
            .run(equality_answer, vec![])
            .unwrap(),
        Value::U64(42)
    );
    let error = Vm::new(verified)
        .run(phases.artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");

    let reordered = r#"
        main() -> { let bomb = make_bomb(); () }
        make_bomb() -> Bomb<Good> { Bomb { value: Good { marker: 1 } } }
        bomb_missing(value: Bomb<Missing>) -> Bomb<Missing> { value }
        bomb_bad(value: Bomb<Bad>) -> Bomb<Bad> { value }
        bomb_good(value: Bomb<Good>) -> Bomb<Good> { value }
        ticket_missing(value: Ticket<Missing>) -> Ticket<Missing> { value }
        ticket_bad(value: Ticket<Bad>) -> Ticket<Bad> { value }
        ticket_good(value: Ticket<Good>) -> Ticket<Good> { value }
        equality_answer() -> u16 { equality_outer(42) }
        equality_outer<T>(value: T) -> T
            where Box<i64>: Family<Text, Member<T> = Triple<i64, Text, T>> {
            equality_inner(value)
        }
        equality_inner<T>(value: T) -> T
            where Box<i64>: Family<Text, Member<T> = Triple<i64, Text, T>> {
            value
        }
        projection_answer() -> Text {
            let holder = Holder { value: make_member() };
            read_member(holder.value)
        }
        read_member(value: <Box<i64> as Family<Text>>::Member<u16>) -> Text {
            value.context
        }
        make_member() -> <Box<i64> as Family<Text>>::Member<u16> {
            Triple { source: 41, context: "context", item: 7 }
        }
        impl<T> Drop for Bomb<T> where T: Keyed<At<Text> = Text> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        impl<T> Use<[0,1]> for Ticket<T> where T: Keyed<At<Text> = Text> {}
        impl Keyed for Bad { type At<K> = i64; }
        impl Keyed for Good { type At<K> = K; }
        impl<S, C> Family<C> for Box<S> {
            type Member<T> = <Layer<S, C> as Layered>::Out<T>;
        }
        impl<S, C> Layered for Layer<S, C> {
            type Out<T> = Triple<S, C, T>;
        }
        struct Bomb<T> { value: T }
        struct Ticket<T> { marker: i64 }
        struct Missing { marker: i64 }
        struct Bad { marker: i64 }
        struct Good { marker: i64 }
        struct Holder { value: <Box<i64> as Family<Text>>::Member<u16> }
        struct Triple<S, C, T> { source: S, context: C, item: T }
        struct Layer<S, C> {}
        struct Box<S> { value: S }
        trait Keyed { type At<K>; }
        trait Layered { type Out<T>; }
        trait Family<C> { type Member<T>; }
    "#;
    assert_eq!(
        compile_source_to_bytecode("gat-projections-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn lexical_associated_equalities_normalize_symbolic_generic_signatures() {
    let source = r#"
        trait Value { type Item; }
        trait Keyed { type At<K>; }
        struct Good { marker: i64 }
        impl Value for Good { type Item = Text; }
        impl Keyed for Good { type At<K> = K; }
        lexical<T>(owner: T, value: <T as Value>::Item) -> <T as Value>::Item
            where T: Value<Item=Text> { value }
        nested<T>(owner: T, value: (<T as Value>::Item, i64))
            -> (<T as Value>::Item, i64)
            where T: Value<Item=Text> { value }
        keyed<T, K>(owner: T, value: <T as Keyed>::At<K>) -> <T as Keyed>::At<K>
            where T: Keyed<At<K> = K> { value }
        text_answer() -> Text { lexical(Good { marker: 0 }, "lexical") }
        nested_answer() -> i64 { nested(Good { marker: 0 }, ("nested", 42)).1 }
        keyed_answer() -> u16 { keyed(Good { marker: 0 }, 42) }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("symbolic-projection-signatures.glorious", source).unwrap();
    let bytes = artifact.encode();
    let verified = verify(artifact.clone()).unwrap();
    for (name, expected) in [
        ("text_answer", Value::Text("lexical".into())),
        ("nested_answer", Value::I64(42)),
        ("keyed_answer", Value::U64(42)),
    ] {
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            expected
        );
    }

    let reordered = r#"
        main() -> { () }
        keyed_answer() -> u16 { keyed(Good { marker: 0 }, 42) }
        nested_answer() -> i64 { nested(Good { marker: 0 }, ("nested", 42)).1 }
        text_answer() -> Text { lexical(Good { marker: 0 }, "lexical") }
        keyed<T, K>(owner: T, value: <T as Keyed>::At<K>) -> <T as Keyed>::At<K>
            where T: Keyed<At<K> = K> { value }
        nested<T>(owner: T, value: (<T as Value>::Item, i64))
            -> (<T as Value>::Item, i64)
            where T: Value<Item=Text> { value }
        lexical<T>(owner: T, value: <T as Value>::Item) -> <T as Value>::Item
            where T: Value<Item=Text> { value }
        impl Keyed for Good { type At<K> = K; }
        impl Value for Good { type Item = Text; }
        struct Good { marker: i64 }
        trait Keyed { type At<K>; }
        trait Value { type Item; }
    "#;
    assert_eq!(
        compile_source_to_bytecode(
            "symbolic-projection-signatures-reordered.glorious",
            reordered
        )
        .unwrap()
        .encode(),
        bytes
    );

    for (name, source) in [
        (
            "missing-equality",
            "trait Value{type Item;} bad<T>(value:<T as Value>::Item)-><T as Value>::Item where T:Value{value} main()->{()}",
        ),
        (
            "gat-key-mismatch",
            "trait Keyed{type At<K>;} bad<T>(value:<T as Keyed>::At<i64>)->i64 where T:Keyed<At<Text> = Text>{value} main()->{()}",
        ),
        (
            "conflicting-equality",
            "trait Value{type Item;} bad<T>(value:<T as Value>::Item)->Text where T:Value<Item = Text>,T:Value<Item = i64>{value} main()->{()}",
        ),
        (
            "recursive-equality",
            "trait Value{type Item;} bad<T>(value:<T as Value>::Item)->Text where T:Value<Item = <T as Value>::Item>{value} main()->{()}",
        ),
    ] {
        let diagnostics =
            compile_source_to_bytecode(&format!("symbolic-{name}.glorious"), source).unwrap_err();
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.code.is_some()
                    && diagnostic.span.is_some()
                    && (diagnostic.message.contains("projection")
                        || diagnostic.message.contains("equality")
                        || diagnostic.message.contains("trait environment"))
            }),
            "{name}: {diagnostics:#?}"
        );
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code.as_deref() != Some("G1BC999"))
        );
    }
}

#[test]
fn gat_rejects_invalid_item_arguments_definitions_and_normalization() {
    let cases = [
        (
            "definition-arity",
            "trait Family{type Member<T>;} impl Family for Text{type Member=Text;} main()->{()}",
            "arity",
        ),
        (
            "projection-arity",
            "trait Family{type Member<T>;} impl Family for Text{type Member<T> = T;} bad(v:<Text as Family>::Member<i64,Text>)->{()} main()->{()}",
            "arity",
        ),
        (
            "equality-arity",
            "trait Family{type Member<T>;} require_evidence<X>(v:X)->X where Text:Family<Member<i64,Text> = i64>{v} main()->{()}",
            "arity",
        ),
        (
            "missing-definition",
            "trait Family{type Member<T>;} impl Family for Text{} main()->{()}",
            "missing",
        ),
        (
            "duplicate-definition",
            "trait Family{type Member<T>;} impl Family for Text{type Member<T> = T; type Member<T> = Text;} main()->{()}",
            "more than once",
        ),
        (
            "unknown-definition",
            "trait Family{type Member<T>;} impl Family for Text{type Other<T> = T;} main()->{()}",
            "extra",
        ),
        (
            "duplicate-binder",
            "trait Family{type Member<T,T>;} main()->{()}",
            "bound more than once",
        ),
        (
            "binder-out-of-scope",
            "trait Family{type Member<T>;} struct Wrap<T>{value:T} impl Family for Text{type Member<T> = Wrap<U>;} main()->{()}",
            "unresolved",
        ),
        (
            "without-impl",
            "trait Family{type Member<T>;} bad(v:<Text as Family>::Member<i64>)->{()} main()->{()}",
            "projection",
        ),
        (
            "unresolved-generic",
            "trait Family{type Member<T>;} bad<S>(v:<S as Family>::Member<i64>)->Text where S:Family{\"bad\"} main()->{()}",
            "projection",
        ),
        (
            "recursive",
            "trait Family{type Member<T>;} impl Family for Text{type Member<T> = <Text as Family>::Member<T>;} bad(v:<Text as Family>::Member<i64>)->{()} main()->{()}",
            "projection",
        ),
        (
            "expanding",
            "trait Family{type Member<T>;} struct Wrap<T>{value:T} impl Family for Text{type Member<T> = <Text as Family>::Member<Wrap<T>>;} bad(v:<Text as Family>::Member<i64>)->{()} main()->{()}",
            "limit",
        ),
        (
            "overlap-different-definition",
            "trait Family{type Member<T>;} struct Box<S>{value:S} impl<S> Family for Box<S>{type Member<T> = S;} impl Family for Box<Text>{type Member<T> = T;} main()->{()}",
            "overlap",
        ),
        (
            "negative-definition",
            "trait Family{type Member<T>;} impl !Family for Text{type Member<T> = T;} main()->{()}",
            "negative",
        ),
        (
            "const-binder",
            "trait Family{type Member<const T>;} main()->{()}",
            "const",
        ),
        (
            "default",
            "trait Family{type Member<T> = Text;} main()->{()}",
            "default",
        ),
    ];
    for (name, source, needle) in cases {
        let errors =
            compile_source_to_bytecode(&format!("bad-gat-{name}.glorious"), source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.span.is_some()
                    && error.message.to_ascii_lowercase().contains(needle)
                    && (error.code.is_some()
                        || matches!(name, "duplicate-definition" | "duplicate-binder"))
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn ground_gat_projections_normalize_in_every_where_clause_term() {
    let source = r#"
        trait Family { type Member<T>; }
        trait Mark {}
        trait Rel<To> {}
        trait Keyed { type At<K>; }
        trait Outer {}
        struct Maker { marker: i64 }
        struct Wrap<T> { value: T }
        struct Ticket<T> { marker: i64 }
        struct Bomb<T> { value: T }
        impl Family for Maker { type Member<T> = T; }
        impl Mark for i64 {}
        impl Rel<i64> for i64 {}
        impl Keyed for Maker { type At<K> = K; }
        impl<T> Outer for Wrap<T>
            where <Maker as Family>::Member<i64>: Mark,
                  i64: Rel<<Maker as Family>::Member<i64>>,
                  Maker: Keyed<At<<Maker as Family>::Member<i64>> = i64>,
                  Maker: Keyed<At<i64> = <Maker as Family>::Member<i64>> {}
        impl<T> Use<[0,1]> for Ticket<T>
            where <Maker as Family>::Member<i64>: Mark,
                  i64: Rel<<Maker as Family>::Member<i64>>,
                  Maker: Keyed<At<<Maker as Family>::Member<i64>> = i64>,
                  Maker: Keyed<At<i64> = <Maker as Family>::Member<i64>> {}
        impl<T> Drop for Bomb<T>
            where <Maker as Family>::Member<i64>: Mark,
                  i64: Rel<<Maker as Family>::Member<i64>>,
                  Maker: Keyed<At<<Maker as Family>::Member<i64>> = i64>,
                  Maker: Keyed<At<i64> = <Maker as Family>::Member<i64>> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        all_terms<T>(value:T)->T
            where <Maker as Family>::Member<i64>: Mark,
                  i64: Rel<<Maker as Family>::Member<i64>>,
                  Maker: Keyed<At<<Maker as Family>::Member<i64>> = i64>,
                  Maker: Keyed<At<i64> = <Maker as Family>::Member<i64>> {
            value
        }
        impl_terms<T>(value:T)->T where Wrap<T>: Outer { value }
        function_answer()->Text { all_terms("function") }
        impl_answer()->Text { impl_terms("implementation") }
        ticket(value:Ticket<Text>)->Ticket<Text> { value }
        bomb(value:Bomb<Text>)->Bomb<Text> { value }
        make_bomb()->Bomb<Text> { Bomb { value: "boom" } }
        main()->{ let bomb = make_bomb(); () }
    "#;
    let phases = compile_source_to_phases("gat-where-terms.glorious", source).unwrap();
    let repeated = compile_source_to_phases("gat-where-terms.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    let ticket = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "ticket")
        .unwrap()
        .params[0];
    assert!(!phases.artifact.types[ticket as usize].claimed_duplicable());
    assert!(phases.artifact.types[ticket as usize].claimed_zero_use_allowed());
    let bomb = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "bomb")
        .unwrap()
        .params[0];
    assert!(phases.artifact.drop_glue.iter().any(|glue| glue.ty == bomb));
    for prefix in ["$specialization$all_terms#", "$specialization$impl_terms#"] {
        assert_eq!(
            phases
                .artifact
                .functions
                .iter()
                .filter(|function| function.name.starts_with(prefix))
                .count(),
            1
        );
    }

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    for (name, expected) in [
        ("function_answer", "function"),
        ("impl_answer", "implementation"),
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::Text(expected.into())
        );
    }
    let error = Vm::new(verified)
        .run(phases.artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");

    let reordered = r#"
        main()->{ let bomb = make_bomb(); () }
        make_bomb()->Bomb<Text> { Bomb { value: "boom" } }
        bomb(value:Bomb<Text>)->Bomb<Text> { value }
        ticket(value:Ticket<Text>)->Ticket<Text> { value }
        impl_answer()->Text { impl_terms("implementation") }
        function_answer()->Text { all_terms("function") }
        impl_terms<T>(value:T)->T where Wrap<T>: Outer { value }
        all_terms<T>(value:T)->T
            where Maker: Keyed<At<i64> = <Maker as Family>::Member<i64>>,
                  Maker: Keyed<At<<Maker as Family>::Member<i64>> = i64>,
                  i64: Rel<<Maker as Family>::Member<i64>>,
                  <Maker as Family>::Member<i64>: Mark { value }
        impl<T> Drop for Bomb<T>
            where Maker: Keyed<At<i64> = <Maker as Family>::Member<i64>>,
                  Maker: Keyed<At<<Maker as Family>::Member<i64>> = i64>,
                  i64: Rel<<Maker as Family>::Member<i64>>,
                  <Maker as Family>::Member<i64>: Mark {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        impl<T> Use<[0,1]> for Ticket<T>
            where Maker: Keyed<At<i64> = <Maker as Family>::Member<i64>>,
                  Maker: Keyed<At<<Maker as Family>::Member<i64>> = i64>,
                  i64: Rel<<Maker as Family>::Member<i64>>,
                  <Maker as Family>::Member<i64>: Mark {}
        impl<T> Outer for Wrap<T>
            where Maker: Keyed<At<i64> = <Maker as Family>::Member<i64>>,
                  Maker: Keyed<At<<Maker as Family>::Member<i64>> = i64>,
                  i64: Rel<<Maker as Family>::Member<i64>>,
                  <Maker as Family>::Member<i64>: Mark {}
        impl Keyed for Maker { type At<K> = K; }
        impl Rel<i64> for i64 {}
        impl Mark for i64 {}
        impl Family for Maker { type Member<T> = T; }
        struct Bomb<T> { value: T }
        struct Ticket<T> { marker: i64 }
        struct Wrap<T> { value: T }
        struct Maker { marker: i64 }
        trait Outer {}
        trait Keyed { type At<K>; }
        trait Rel<To> {}
        trait Mark {}
        trait Family { type Member<T>; }
    "#;
    assert_eq!(
        compile_source_to_bytecode("gat-where-terms-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn lexical_param_environments_key_generic_closure_specializations() {
    let source = r#"
        trait Rel<Mode> {}
        struct Left { marker: i64 }
        struct Right { marker: i64 }
        struct Token<M> { marker: i64 }
        impl Rel<Left> for i64 {}
        impl Rel<Right> for i64 {}
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        nested<M>(value: i64) -> Token<M> where i64: Rel<M> {
            Token { marker: value }
        }
        closure_site<M>(value: i64) -> Token<M> where i64: Rel<M> {
            call0({ => nested(value) })
        }
        recursive<T>(value: T) -> T where T: Rel<Left> { recursive(value) }
        left_answer() -> Token<Left> { closure_site(41) }
        right_answer() -> Token<Right> { closure_site(42) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("param-env-closure.glorious", source).unwrap();
    let repeated = compile_source_to_phases("param-env-closure.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    for prefix in ["$specialization$nested#", "$specialization$closure_site#"] {
        assert_eq!(
            phases
                .artifact
                .functions
                .iter()
                .filter(|function| function.name.starts_with(prefix))
                .count(),
            2,
            "the two lexical environments must not alias {prefix}"
        );
    }
    assert!(
        !phases
            .artifact
            .functions
            .iter()
            .any(|function| function.name.starts_with("$specialization$recursive#"))
    );
    let closures = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$closure$"))
        .collect::<Vec<_>>();
    assert_eq!(closures.len(), 2);
    assert!(
        closures
            .iter()
            .all(|function| function.params == [grandiose_vm::I64])
    );

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    let mut closure_results = closures
        .iter()
        .map(|function| function.return_type)
        .collect::<Vec<_>>();
    closure_results.sort();
    closure_results.dedup();
    assert_eq!(closure_results.len(), 2);
    for (name, marker) in [("left_answer", 41), ("right_answer", 42)] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        let result_type = phases.artifact.functions[function as usize].return_type;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::aggregate(result_type, [Value::I64(marker)])
        );
    }

    let reordered = r#"
        main() -> { () }
        right_answer() -> Token<Right> { closure_site(42) }
        left_answer() -> Token<Left> { closure_site(41) }
        recursive<T>(value: T) -> T where T: Rel<Left> { recursive(value) }
        closure_site<M>(value: i64) -> Token<M> where i64: Rel<M> {
            call0({ => nested(value) })
        }
        nested<M>(value: i64) -> Token<M> where i64: Rel<M> {
            Token { marker: value }
        }
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        impl Rel<Right> for i64 {}
        impl Rel<Left> for i64 {}
        struct Token<M> { marker: i64 }
        struct Right { marker: i64 }
        struct Left { marker: i64 }
        trait Rel<Mode> {}
    "#;
    assert_eq!(
        compile_source_to_bytecode("param-env-closure-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn uninstantiated_generics_validate_calls_under_lexical_param_environments() {
    let source = r#"
        trait Mark {}
        trait Value { type Item; }
        struct Box<T> { value: T }
        impl<T> Mark for Box<T> where T: Mark {}
        inner<T>(value:T)->T where T: Mark { value }
        outer<T>(value:T)->T where T: Mark { inner(value) }
        boxed_inner<T>(value:Box<T>)->Box<T> where Box<T>: Mark { value }
        boxed_outer<T>(value:Box<T>)->Box<T> where T: Mark {
            boxed_inner(value)
        }
        equality_inner<T>(value:T)->T where T: Value<Item=Text> { value }
        equality_outer<T>(value:T)->T where T: Value<Item=Text> {
            equality_inner(value)
        }
        negative_inner<T>(value:T)->T where T: !Mark { value }
        negative_outer<T>(value:T)->T where T: !Mark { negative_inner(value) }
        main()->{()}
    "#;
    let phases = compile_source_to_phases("symbolic-param-env.glorious", source).unwrap();
    let repeated = compile_source_to_phases("symbolic-param-env.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    let baseline =
        compile_source_to_bytecode("symbolic-param-env-baseline.glorious", "main()->{()}").unwrap();
    let specialization_names = |artifact: &Artifact| {
        artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$"))
            .map(|function| function.name.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        specialization_names(&phases.artifact),
        specialization_names(&baseline),
        "uninstantiated user generics must not add ground specialization requests"
    );

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(phases.artifact.entry_function.unwrap(), vec![])
            .unwrap(),
        Value::Unit
    );

    let reordered = r#"
        main()->{()}
        negative_outer<T>(value:T)->T where T: !Mark { negative_inner(value) }
        negative_inner<T>(value:T)->T where T: !Mark { value }
        equality_outer<T>(value:T)->T where T: Value<Item=Text> {
            equality_inner(value)
        }
        equality_inner<T>(value:T)->T where T: Value<Item=Text> { value }
        boxed_outer<T>(value:Box<T>)->Box<T> where T: Mark {
            boxed_inner(value)
        }
        boxed_inner<T>(value:Box<T>)->Box<T> where Box<T>: Mark { value }
        outer<T>(value:T)->T where T: Mark { inner(value) }
        inner<T>(value:T)->T where T: Mark { value }
        impl<T> Mark for Box<T> where T: Mark {}
        struct Box<T> { value: T }
        trait Value { type Item; }
        trait Mark {}
    "#;
    assert_eq!(
        compile_source_to_bytecode("symbolic-param-env-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn uninstantiated_generic_calls_reject_lexical_environment_mismatches() {
    let cases = [
        (
            "missing-positive",
            "trait Mark{} trait Other{} inner<T>(v:T)->T where T:Mark{v} outer<T>(v:T)->T where T:Other{inner(v)} main()->{()}",
            "matching implementation",
        ),
        (
            "missing-negative",
            "trait Mark{} trait Other{} inner<T>(v:T)->T where T:!Mark{v} outer<T>(v:T)->T where T:Other{inner(v)} main()->{()}",
            "negative evidence",
        ),
        (
            "refuted-positive",
            "trait Mark{} inner<T>(v:T)->T where T:Mark{v} outer<T>(v:T)->T where T:!Mark{inner(v)} main()->{()}",
            "refut",
        ),
        (
            "refuted-negative",
            "trait Mark{} inner<T>(v:T)->T where T:!Mark{v} outer<T>(v:T)->T where T:Mark{inner(v)} main()->{()}",
            "refut",
        ),
        (
            "missing-equality",
            "trait Value{type Item;} inner<T>(v:T)->T where T:Value<Item=Text>{v} outer<T>(v:T)->T where T:Value{inner(v)} main()->{()}",
            "matching implementation",
        ),
    ];
    for (name, source, needle) in cases {
        let errors =
            compile_source_to_bytecode(&format!("bad-symbolic-param-env-{name}.glorious"), source)
                .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.is_some()
                    && error.span.is_some()
                    && error.message.to_ascii_lowercase().contains(needle)
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn lexical_param_environments_forward_bounds_through_generic_calls() {
    let source = r#"
        trait Mark {}
        trait Value<To> { type Item; }
        struct Box<T> { value: T }
        impl Mark for Text {}
        impl<T> Mark for Box<T> where T: Mark {}
        impl Value<i64> for Text { type Item = Text; }
        impl !Value<Text> for i64 {}
        inner<T>(value: T) -> T where T: Mark { value }
        middle<T>(value: T) -> T where T: Mark { inner(value) }
        outer<T>(value: T) -> T where T: Mark { middle(value) }
        boxed_inner<T>(value: Box<T>) -> Box<T> where Box<T>: Mark { value }
        boxed_outer<T>(value: Box<T>) -> Box<T> where T: Mark {
            boxed_inner(value)
        }
        equality_inner<T>(value: T) -> T where T: Value<i64, Item=Text> { value }
        equality_middle<T>(value: T) -> T where T: Value<i64, Item=Text> {
            equality_inner(value)
        }
        equality_outer<T>(value: T) -> T where T: Value<i64, Item=Text> {
            equality_middle(value)
        }
        weaker_inner<T>(value: T) -> T where T: Value<i64> { value }
        stronger_outer<T>(value: T) -> T where T: Value<i64, Item=Text> {
            weaker_inner(value)
        }
        combined_inner<T>(value: T) -> T
            where T: Mark, T: Value<i64, Item=Text> { value }
        combined_outer<T>(value: T) -> T
            where T: Value<i64, Item=Text>, T: Mark {
            combined_inner(value)
        }
        negative_inner<T>(value: T) -> T where T: !Value<Text> { value }
        negative_outer<T>(value: T) -> T where T: !Value<Text> {
            negative_inner(value)
        }
        text_answer() -> Text { outer("forwarded") }
        boxed_answer() -> Box<Text> { boxed_outer(Box { value: "boxed" }) }
        equality_answer() -> Text { equality_outer("equal") }
        stronger_answer() -> Text { stronger_outer("stronger") }
        combined_answer() -> Text { combined_outer("combined") }
        negative_answer() -> i64 { negative_outer(42) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("lexical-param-env.glorious", source).unwrap();
    let repeated = compile_source_to_phases("lexical-param-env.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());

    for prefix in [
        "$specialization$inner#",
        "$specialization$middle#",
        "$specialization$outer#",
        "$specialization$boxed_inner#",
        "$specialization$boxed_outer#",
        "$specialization$equality_inner#",
        "$specialization$equality_middle#",
        "$specialization$equality_outer#",
        "$specialization$weaker_inner#",
        "$specialization$stronger_outer#",
        "$specialization$combined_inner#",
        "$specialization$combined_outer#",
        "$specialization$negative_inner#",
        "$specialization$negative_outer#",
    ] {
        assert_eq!(
            phases
                .artifact
                .functions
                .iter()
                .filter(|function| function.name.starts_with(prefix))
                .count(),
            1,
            "{prefix}"
        );
    }

    let bytes = phases.artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let verified = verify(phases.artifact.clone()).unwrap();
    for (name, expected) in [
        ("text_answer", "forwarded"),
        ("equality_answer", "equal"),
        ("stronger_answer", "stronger"),
        ("combined_answer", "combined"),
    ] {
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::Text(expected.into())
        );
    }
    let negative_answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "negative_answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified.clone())
            .run(negative_answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
    let boxed_answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "boxed_answer")
        .unwrap() as u32;
    let boxed = phases.artifact.functions[boxed_answer as usize].return_type;
    assert_eq!(
        Vm::new(verified).run(boxed_answer, vec![]).unwrap(),
        Value::aggregate(boxed, [Value::Text("boxed".into())])
    );

    let reordered = r#"
        main() -> { () }
        negative_answer() -> i64 { negative_outer(42) }
        combined_answer() -> Text { combined_outer("combined") }
        stronger_answer() -> Text { stronger_outer("stronger") }
        equality_answer() -> Text { equality_outer("equal") }
        boxed_answer() -> Box<Text> { boxed_outer(Box { value: "boxed" }) }
        text_answer() -> Text { outer("forwarded") }
        negative_outer<T>(value: T) -> T where T: !Value<Text> {
            negative_inner(value)
        }
        negative_inner<T>(value: T) -> T where T: !Value<Text> { value }
        combined_outer<T>(value: T) -> T
            where T: Mark, T: Value<i64, Item=Text> {
            combined_inner(value)
        }
        combined_inner<T>(value: T) -> T
            where T: Value<i64, Item=Text>, T: Mark { value }
        stronger_outer<T>(value: T) -> T where T: Value<i64, Item=Text> {
            weaker_inner(value)
        }
        weaker_inner<T>(value: T) -> T where T: Value<i64> { value }
        equality_outer<T>(value: T) -> T where T: Value<i64, Item=Text> {
            equality_middle(value)
        }
        equality_middle<T>(value: T) -> T where T: Value<i64, Item=Text> {
            equality_inner(value)
        }
        equality_inner<T>(value: T) -> T where T: Value<i64, Item=Text> { value }
        boxed_outer<T>(value: Box<T>) -> Box<T> where T: Mark {
            boxed_inner(value)
        }
        boxed_inner<T>(value: Box<T>) -> Box<T> where Box<T>: Mark { value }
        outer<T>(value: T) -> T where T: Mark { middle(value) }
        middle<T>(value: T) -> T where T: Mark { inner(value) }
        inner<T>(value: T) -> T where T: Mark { value }
        impl !Value<Text> for i64 {}
        impl Value<i64> for Text { type Item = Text; }
        impl<T> Mark for Box<T> where T: Mark {}
        impl Mark for Text {}
        struct Box<T> { value: T }
        trait Value<To> { type Item; }
        trait Mark {}
    "#;
    assert_eq!(
        compile_source_to_bytecode("lexical-param-env-reordered.glorious", reordered)
            .unwrap()
            .encode(),
        bytes
    );
}

#[test]
fn lexical_param_environments_isolate_missing_refuted_and_equality_facts() {
    let cases = [
        (
            "isolated-missing-positive",
            r#"
                trait Mark {}
                trait Other {}
                impl Mark for Text {}
                impl Other for i64 {}
                inner<T>(value:T)->T where T: Mark { value }
                good<T>(value:T)->T where T: Mark { inner(value) }
                bad<T>(value:T)->T where T: Other { inner(value) }
                good_answer()->Text { good("good") }
                bad_answer()->i64 { bad(42) }
                main()->{()}
            "#,
            "matching implementation",
        ),
        (
            "missing-negative",
            r#"
                trait Mark {}
                trait Other {}
                impl Other for i64 {}
                inner<T>(value:T)->T where T: !Mark { value }
                bad<T>(value:T)->T where T: Other { inner(value) }
                bad_answer()->i64 { bad(42) }
                main()->{()}
            "#,
            "negative evidence",
        ),
        (
            "refuted-positive",
            r#"
                trait Mark {}
                impl !Mark for i64 {}
                inner<T>(value:T)->T where T: Mark { value }
                bad<T>(value:T)->T where T: !Mark { inner(value) }
                bad_answer()->i64 { bad(42) }
                main()->{()}
            "#,
            "refut",
        ),
        (
            "refuted-negative",
            r#"
                trait Mark {}
                impl Mark for Text {}
                inner<T>(value:T)->T where T: !Mark { value }
                bad<T>(value:T)->T where T: Mark { inner(value) }
                bad_answer()->Text { bad("bad") }
                main()->{()}
            "#,
            "refut",
        ),
        (
            "missing-equality",
            r#"
                trait Value { type Item; }
                impl Value for Text { type Item=i64; }
                inner<T>(value:T)->T where T: Value<Item=Text> { value }
                bad<T>(value:T)->T where T: Value { inner(value) }
                bad_answer()->Text { bad("bad") }
                main()->{()}
            "#,
            "matching implementation",
        ),
    ];
    for (name, source, needle) in cases {
        let errors = compile_source_to_bytecode(&format!("bad-param-env-{name}.glorious"), source)
            .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.is_some()
                    && error.span.is_some()
                    && error.message.to_ascii_lowercase().contains(needle)
            }),
            "{name}: {errors:#?}"
        );
    }

    let reordered_missing = r#"
        main()->{()}
        bad_answer()->i64 { bad(42) }
        good_answer()->Text { good("good") }
        bad<T>(value:T)->T where T: Other { inner(value) }
        good<T>(value:T)->T where T: Mark { inner(value) }
        inner<T>(value:T)->T where T: Mark { value }
        impl Other for i64 {}
        impl Mark for Text {}
        trait Other {}
        trait Mark {}
    "#;
    let errors = compile_source_to_bytecode(
        "bad-param-env-isolated-reordered.glorious",
        reordered_missing,
    )
    .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error
                    .message
                    .to_ascii_lowercase()
                    .contains("matching implementation")
        }),
        "{errors:#?}"
    );
}

#[test]
fn unused_marker_metadata_is_request_free_and_order_independent() {
    let baseline = "main() -> { () }";
    let first =
        "trait Left {} trait Right {} impl Left for i64 {} impl Right for Text {} main() -> { () }";
    let reordered =
        "impl Right for Text {} main() -> { () } trait Right {} impl Left for i64 {} trait Left {}";
    let baseline = compile_source_to_bytecode("marker-baseline.glorious", baseline)
        .unwrap()
        .encode();
    assert_eq!(
        baseline,
        compile_source_to_bytecode("marker-unused.glorious", first)
            .unwrap()
            .encode()
    );
    assert_eq!(
        baseline,
        compile_source_to_bytecode("marker-reordered.glorious", reordered)
            .unwrap()
            .encode()
    );
}

#[test]
fn grounded_generic_drop_body_discovers_function_nominal_and_cleanup() {
    let source = r#"
        struct Root<T> { value: T }
        struct Bomb<T> { value: T }
        spawn<T>(value: T) -> Bomb<T> { Bomb { value: value } }
        impl<T> Drop for Root<T> {
            drop(&mut self) -> { let bomb = spawn(self.value); () }
        }
        impl<T> Drop for Bomb<T> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        make() -> Root<i64> { Root { value: 42 } }
        main() -> { let root = make(); () }
    "#;
    let phases = compile_source_to_phases("drop-rooted-specialization.glorious", source).unwrap();
    let artifact = &phases.artifact;

    assert_eq!(
        artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$spawn#"))
            .count(),
        1
    );
    let bomb = artifact
        .types
        .iter()
        .position(|ty| {
            matches!(ty.representation(), Type::Struct { name, fields, .. }
                if name == "Bomb" && fields.len() == 1 && fields[0].ty == grandiose_vm::I64)
        })
        .expect("the Drop-rooted call must discover Bomb<i64>") as u32;
    assert!(artifact.drop_glue.iter().any(|glue| glue.ty == bomb));

    let bytes = artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let error = Vm::new(verify(artifact.clone()).unwrap())
        .run(artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");

    let reordered = r#"
        main() -> { let root = make(); () }
        make() -> Root<i64> { Root { value: 42 } }
        impl<T> Drop for Bomb<T> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        impl<T> Drop for Root<T> {
            drop(&mut self) -> { let bomb = spawn(self.value); () }
        }
        spawn<T>(value: T) -> Bomb<T> { Bomb { value: value } }
        struct Bomb<T> { value: T }
        struct Root<T> { value: T }
    "#;
    let reordered =
        compile_source_to_phases("drop-rooted-specialization-reordered.glorious", reordered)
            .unwrap();
    assert_eq!(bytes, reordered.artifact.encode());
}

#[test]
fn grounded_generic_drop_discovery_reaches_a_transitive_fixed_point() {
    let source = r#"
        struct Root<T> { value: T }
        struct Middle<T> { value: T }
        struct Terminal<T> { value: T }
        first<T>(value: T) -> Middle<T> { Middle { value: value } }
        second<T>(value: T) -> Terminal<T> { Terminal { value: value } }
        impl<T> Drop for Root<T> {
            drop(&mut self) -> { let middle = first(self.value); () }
        }
        impl<T> Drop for Middle<T> {
            drop(&mut self) -> { let terminal = second(self.value); () }
        }
        impl<T> Drop for Terminal<T> {
            drop(&mut self) -> { self.value; 1 / 0; () }
        }
        make() -> Root<i64> { Root { value: 42 } }
        main() -> { let root = make(); () }
    "#;
    let artifact = compile_source_to_bytecode("transitive-drop-roots.glorious", source).unwrap();

    for name in ["$specialization$first#", "$specialization$second#"] {
        assert_eq!(
            artifact
                .functions
                .iter()
                .filter(|function| function.name.starts_with(name))
                .count(),
            1,
            "expected exactly one {name} specialization"
        );
    }
    for name in ["Root", "Middle", "Terminal"] {
        let ty = artifact
            .types
            .iter()
            .position(|ty| {
                matches!(ty.representation(), Type::Struct { name: found, fields, .. }
                    if found == name && fields.len() == 1 && fields[0].ty == grandiose_vm::I64)
            })
            .unwrap_or_else(|| panic!("missing fixed-point instance {name}"))
            as u32;
        assert!(artifact.drop_glue.iter().any(|glue| glue.ty == ty));
    }
    let error = Vm::new(verify(artifact.clone()).unwrap())
        .run(artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");
}

#[test]
fn drop_rooted_recursive_specialization_and_generic_field_borrow_are_deduplicated() {
    let finite = r#"
        struct Root<T> { value: T }
        recurse<T>(value: T) -> T { recurse(value) }
        impl<T> Drop for Root<T> {
            drop(&mut self) -> { recurse(self.value); () }
        }
        keep(value: Root<i64>) -> Root<i64> { value }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("finite-drop-rooted-recursion.glorious", finite).unwrap();
    assert_eq!(
        artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$recurse#"))
            .count(),
        1
    );
    verify(Artifact::decode(&artifact.encode()).unwrap()).unwrap();

    let borrowed = r#"
        struct Root<T> { value: T }
        inspect<T>(value: &T) -> { value; () }
        impl<T> Drop for Root<T> {
            drop(&mut self) -> { inspect(&self.value); () }
        }
        keep(value: Root<i64>) -> Root<i64> { value }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("drop-rooted-borrow.glorious", borrowed).unwrap();
    verify(Artifact::decode(&artifact.encode()).unwrap()).unwrap();
    assert!(
        artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::ProjectBorrowShared { .. })),
        "the concrete generic Drop instance must project its field borrow"
    );
}

#[test]
fn drop_rooted_captureless_callback_and_nested_generic_are_closed_and_execute() {
    let source = r#"
        struct Root<T> { value: T }
        id<T>(value: T) -> T { value }
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        impl<T> Drop for Root<T> {
            drop(&mut self) -> {
                call0({ => { id(42); 1 / 0; () } });
                ()
            }
        }
        make() -> Root<i64> { Root { value: 7 } }
        main() -> { let root = make(); () }
    "#;
    let phases = compile_source_to_phases("drop-rooted-callback.glorious", source).unwrap();
    let artifact = &phases.artifact;

    for prefix in ["$specialization$call0#", "$specialization$id#", "$closure$"] {
        assert_eq!(
            artifact
                .functions
                .iter()
                .filter(|function| function.name.starts_with(prefix))
                .count(),
            1,
            "expected exactly one emitted function with prefix {prefix}"
        );
    }
    assert_direct_only_functions(artifact, |name| {
        name.starts_with("$closure$")
            || name.starts_with("$specialization$call0#")
            || name.starts_with("$specialization$id#")
            || name == "main"
            || name == "make"
    });
    let bytes = artifact.encode();
    assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    let error = Vm::new(verify(artifact.clone()).unwrap())
        .run(artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");

    let repeated = compile_source_to_phases("drop-rooted-callback.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(bytes, repeated.artifact.encode());

    let reordered = r#"
        main() -> { let root = make(); () }
        make() -> Root<i64> { Root { value: 7 } }
        impl<T> Drop for Root<T> {
            drop(&mut self) -> {
                call0({ => { id(42); 1 / 0; () } });
                ()
            }
        }
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        id<T>(value: T) -> T { value }
        struct Root<T> { value: T }
    "#;
    let reordered =
        compile_source_to_bytecode("drop-rooted-callback-reordered.glorious", reordered)
            .unwrap()
            .encode();
    assert_eq!(bytes, reordered);
}

#[test]
fn drop_rooted_observe_capture_is_a_nonescaping_hook_loan() {
    let source = r#"
        struct Root<T> { value: T }
        call0<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
        impl<T> Drop for Root<T> {
            drop(&mut self) -> { call0({ => { self.value; () } }); () }
        }
        keep(value: Root<i64>) -> Root<i64> { value }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("drop-rooted-captureful.glorious", source).unwrap();
    verify(Artifact::decode(&artifact.encode()).unwrap()).unwrap();
}

#[test]
fn borrowed_vec_does_not_grant_the_multishot_snapshot_owner_exemption() {
    let source = r#"
        struct TicketView { marker: i64, values: &Vec<i64> }
        impl Use<[1,1]> for TicketView {}
        effect Choose { [2,2] choose() -> i64 }
        new_values() -> Vec<i64> { Vec::new() }
        consume(value: TicketView) -> i64 {
            let TicketView { marker, values } = move value;
            values;
            marker
        }
        selected() -> i64 {
            let values = new_values();
            let owner = TicketView { marker: 40, values: &values };
            handle {
                let choice = perform Choose::choose();
                consume(move owner) + choice
            } {
                Choose::choose() with continuation => {
                    let first = resume(continuation, 1);
                    let second = resume(move continuation, 2);
                    first + second
                }
            }
        }
        main() -> () { selected(); () }
    "#;
    let errors =
        compile_source_to_phases("borrowed-vec-snapshot-owner.glorious", source).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1BC001")
                && error
                    .message
                    .contains("restricted-use value at multi-shot call")
        }),
        "{errors:#?}"
    );
}
