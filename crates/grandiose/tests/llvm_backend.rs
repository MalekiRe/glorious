use std::{fs, process::Command};

use grandiose_vm::{Value, Vm, verify};

#[test]
fn scalar_main_emits_valid_llvm_ir() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-scalar.glorious",
        "selected() -> i64 { 42 } main() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let module = grandiose::emit_llvm_ir(&phases, &grandiose::LlvmOptions::default()).unwrap();
    assert!(module.ir.contains("define i64 @g1_f"));
    assert!(module.ir.contains("define i32 @main()"));
    assert!(module.ir.contains("target datalayout"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("module.ll");
    let bitcode = directory.path().join("module.bc");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("llvm-as")
        .arg(&source)
        .arg("-o")
        .arg(&bitcode)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn tuples_are_lowered_to_native_llvm_aggregates() {
    let module = grandiose::compile_source_to_llvm_ir(
        "llvm-aggregate.glorious",
        "selected() -> (i64, i64) { (1, 2) } first(value: (i64, i64)) -> i64 { let(head, ignored) = move value; ignored; move head } main() -> () { first(selected()); () }",
    )
    .unwrap();
    assert!(module.ir.contains("insertvalue { i64, i64 }"));
    assert!(module.ir.contains("extractvalue { i64, i64 }"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("aggregate.ll");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("llvm-as")
        .arg(&source)
        .arg("-o")
        .arg("/dev/null")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn references_lower_to_native_pointers() {
    let module = grandiose::compile_source_to_llvm_ir(
        "llvm-reference.glorious",
        "read(value: &i64) -> i64 { *value } selected() -> i64 { let value = 7; read(&value) } main() -> () { selected(); () }",
    )
    .unwrap();
    assert!(module.ir.contains("store ptr %r"));
    assert!(module.ir.contains("load i64, ptr %"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("reference.ll");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("llvm-as")
        .arg(&source)
        .arg("-o")
        .arg("/dev/null")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn enum_tags_and_payloads_lower_to_native_llvm_values() {
    let module = grandiose::compile_source_to_llvm_ir(
        "llvm-enum.glorious",
        "enum Choice { Yes(i64), No } select(choice: Choice) -> i64 { if(choice is Choice::Yes(value)) { value } else { 0 } } main() -> () { select(Choice::Yes(9)); () }",
    )
    .unwrap();
    assert!(module.ir.contains("insertvalue { i32, [1 x i128] }"));
    assert!(module.ir.contains("extractvalue { i32, [1 x i128] }"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("enum.ll");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("llvm-as")
        .arg(&source)
        .arg("-o")
        .arg("/dev/null")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn custom_drop_hooks_run_before_native_structural_cleanup() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-custom-drop.glorious",
        "struct Guard { text: String, marker: i64 }\nimpl Drop for Guard { drop(&mut self) -> { self.marker; () } }\nselected() -> () { let guard = Guard { text: String::concat(\"drop\", \" me\"), marker: 1 }; () }\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let glue = phases.artifact.drop_glue.first().unwrap().function;
    let selected = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(module.ir.contains(&format!("call void @g1_f{glue}(ptr %")));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("custom-drop.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("custom-drop");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "extern void g1_f{selected}(void);\nint main(void) {{ g1_f{selected}(); return 0; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn cli_emits_an_llvm_module() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("main.glorious");
    let output = directory.path().join("main.ll");
    fs::write(&source, "main() -> () { () }").unwrap();
    let status = Command::new(env!("CARGO_BIN_EXE_grc"))
        .arg("--emit")
        .arg("llvm-ir")
        .arg("-o")
        .arg(&output)
        .arg(&source)
        .status()
        .unwrap();
    assert!(status.success());
    let ir = fs::read_to_string(output).unwrap();
    assert!(ir.contains("target triple"));
    assert!(ir.contains("define i32 @main()"));
}

#[test]
fn cli_emits_native_objects_and_executables() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("native.glorious");
    let object = directory.path().join("native.o");
    let executable = directory.path().join("native");
    fs::write(&source, "main() -> () { () }").unwrap();

    for (kind, output) in [("llvm-object", &object), ("executable", &executable)] {
        let status = Command::new(env!("CARGO_BIN_EXE_grc"))
            .arg("--emit")
            .arg(kind)
            .arg("-o")
            .arg(output)
            .arg(&source)
            .status()
            .unwrap();
        assert!(status.success(), "{kind}");
        assert!(output.is_file(), "{kind}");
    }
    let status = Command::new(executable).status().unwrap();
    assert!(status.success(), "{status:?}");
}

#[test]
fn checked_integer_and_shift_primitives_emit_valid_guarded_ir() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-integer-primitives.glorious",
        "divide(value: i64) -> i64 { 84 / value }\nremain(value: i64) -> i64 { 85 % value }\nshift_case(value: i64) -> i64 { shift_left(value, 1) }\nmain() -> () { divide(2); remain(2); shift_case(2); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let module = grandiose::emit_llvm_ir(&phases, &grandiose::LlvmOptions::default()).unwrap();
    assert!(module.ir.contains("sdiv i64"));
    assert!(module.ir.contains("srem i64"));
    assert!(module.ir.contains("icmp eq i64"));
    assert!(module.ir.contains("icmp uge i32"));
    assert!(module.ir.contains("shl i64"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("integer-primitives.ll");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("llvm-as")
        .arg(&source)
        .arg("-o")
        .arg("/dev/null")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn float_char_and_bit_primitives_emit_valid_llvm_ir() {
    let module = grandiose::compile_source_to_llvm_ir(
        "llvm-scalar-conversions.glorious",
        "float_case(value: f64) -> f64 { f64_neg(value) }\nbit_case(value: f64) -> u64 { f64_to_bits(value) }\nchar_case(value: char) -> u32 { char_to_u32(value) }\nmain() -> () { float_case(1.0); bit_case(1.0); char_case('A'); () }",
    )
    .unwrap();
    assert!(module.ir.contains("fneg double"));
    assert!(module.ir.contains("bitcast double"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("scalar-conversions.ll");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("llvm-as")
        .arg(&source)
        .arg("-o")
        .arg("/dev/null")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn nonescaping_closures_use_the_specialized_direct_call_path() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-closure.glorious",
        "invoke<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }\nselected(value: i64) -> i64 { invoke(() -> i64 { value }) }\nmain() -> () { selected(42); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let module = grandiose::emit_llvm_ir(&phases, &grandiose::LlvmOptions::default()).unwrap();
    assert!(module.ir.contains("tail call i64 @g1_f"));
}

#[test]
fn outward_effects_propagate_through_indirect_callables() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-indirect-outward-effect.glorious",
        r#"
            effect Ask { [1,1] ask() -> i64 }
            call_body() -> i64 / {Ask} {
                let text = String::concat("ke", "pt");
                let ask = { => {
                    let answer = perform Ask::ask();
                    String::byte_len(&text);
                    answer
                } };
                ask() + 0
            }
            tail_body() -> i64 / {Ask} {
                let text = String::concat("st", "ill kept");
                let ask = { => {
                    let answer = perform Ask::ask();
                    String::byte_len(&text);
                    answer
                } };
                move ask()
            }
            selected() -> i64 {
                handle call_body() {
                    Ask::ask() with continuation => resume(move continuation, 20)
                };
                handle tail_body() {
                    Ask::ask() with continuation => resume(move continuation, 42)
                }
            }
            main() -> () { selected(); () }
        "#,
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let selected = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    assert!(phases.mir.functions.iter().any(|function| {
        function.blocks.iter().any(|block| {
            matches!(
                block.terminator,
                grandiose::compiler_mir::Terminator::CallIndirect { .. }
            )
        })
    }));
    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(module.ir.contains("%g1.effect_guard = type"));
    assert!(module.ir.contains("call ptr %"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("indirect-outward-effect.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("indirect-outward-effect");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{selected}(void);\nint main(void) {{ return g1_f{selected}() == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn scalar_numeric_conversions_emit_native_llvm_casts() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-numeric-conversions.glorious",
        "narrow(value: i64) -> u8 { wrapping_convert_to_u8(value) }\nwiden(value: u8) -> i16 { wrapping_convert_to_i16(value) }\nto_float(value: i64) -> f64 { i64_to_f64(value) }\nfloat_width(value: f32) -> f64 { f32_to_f64(value) }\nmain() -> () { narrow(258); widen(7); to_float(-9); float_width(1.0); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let module = grandiose::emit_llvm_ir(&phases, &grandiose::LlvmOptions::default()).unwrap();
    assert!(module.ir.contains("trunc i64"));
    assert!(module.ir.contains("zext i8"));
    assert!(module.ir.contains("sitofp i64"));
    assert!(module.ir.contains("fpext float"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("numeric-conversions.ll");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("llvm-as")
        .arg(&source)
        .arg("-o")
        .arg("/dev/null")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn target_options_control_pointer_sized_integer_layout() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-target-layout.glorious",
        "pointer_identity(value: usize) -> usize { value }\nmain() -> () { pointer_identity(7); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let triple = "i686-unknown-linux-gnu".to_owned();
    let module = grandiose::emit_llvm_ir(
        &phases,
        &grandiose::LlvmOptions {
            target_data_layout: grandiose::default_target_data_layout(&triple).map(str::to_owned),
            target_triple: triple,
            emit_entry_wrapper: true,
        },
    )
    .unwrap();
    assert!(
        module
            .ir
            .contains("target triple = \"i686-unknown-linux-gnu\"")
    );
    assert!(module.ir.contains("target datalayout = \"e-m:e-p:32:32"));
    assert!(module.ir.contains("define i32 @g1_f"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("target-layout.ll");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("llvm-as")
        .arg(&source)
        .arg("-o")
        .arg("/dev/null")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn text_and_bytes_use_the_native_reference_counted_runtime() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-text-bytes.glorious",
        "enum Owned { Some(String), None }\ndiscard_owned() -> () {\n  let value = Owned::Some(String::concat(\"owned\", \" enum\"));\n  ()\n}\nselected() -> usize {\n  discard_owned();\n  let unicode = \"a😀\";\n  let unicode_len = String::byte_len(&unicode);\n  unicode_len;\n  let joined = String::concat(\"grand\", \"iose\");\n  let joined_len = String::byte_len(&joined);\n  joined_len;\n  let left_text = \"ab\";\n  let right_text = \"cde\";\n  let left = String::as_bytes(&left_text);\n  let right = String::as_bytes(&right_text);\n  let joined_bytes = Bytes::concat(move left, move right);\n  Bytes::len(&joined_bytes)\n}\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let vm_function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_function, vec![])
            .unwrap(),
        Value::U64(5)
    );
    let llvm_function = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let mut module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(module.ir.contains("%g1.bytes = type"));
    assert!(module.ir.contains("define internal void @g1_bytes_retain"));
    assert!(module.ir.contains("define internal void @g1_bytes_release"));
    assert!(module.ir.contains("call ptr @g1_bytes_allocate"));
    assert!(module.ir.contains("@llvm.memcpy"));
    assert!(module.ir.contains("@g1_utf8_validate"));
    module.ir.push_str(
        "define i1 @g1_test_utf8(ptr %object) {\n  %valid = call i1 @g1_utf8_validate(ptr %object)\n  ret i1 %valid\n}\n",
    );

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("text-bytes.ll");
    fs::write(&source, module.ir).unwrap();
    let output = Command::new("llvm-as")
        .arg(&source)
        .arg("-o")
        .arg("/dev/null")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("text-bytes");
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\n#include <stddef.h>\ntypedef struct {{ int64_t count; uintptr_t length; unsigned char data[10]; }} G1Bytes;\nextern uint64_t g1_f{llvm_function}(void);\nextern _Bool g1_test_utf8(G1Bytes *);\nint main(void) {{\n  G1Bytes valid = {{1, 10, {{0x41, 0xc2, 0xa2, 0xe2, 0x82, 0xac, 0xf0, 0x9f, 0x98, 0x80}}}};\n  G1Bytes overlong = {{1, 3, {{0xe0, 0x80, 0x80}}}};\n  G1Bytes continuation = {{1, 2, {{0xc2, 0x41}}}};\n  G1Bytes surrogate = {{1, 3, {{0xed, 0xa0, 0x80}}}};\n  G1Bytes too_large = {{1, 4, {{0xf4, 0x90, 0x80, 0x80}}}};\n  return g1_f{llvm_function}() == 5 && g1_test_utf8(&valid) && !g1_test_utf8(&overlong) && !g1_test_utf8(&continuation) && !g1_test_utf8(&surrogate) && !g1_test_utf8(&too_large) ? 0 : 1;\n}}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_and_vm_backends_execute_the_same_scalar_program() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-vm-differential.glorious",
        "selected(value: i64) -> i64 { 84 / value }\nmain() -> () { selected(2); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let vm_function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    let vm_result = Vm::new(verify(phases.artifact.clone()).unwrap())
        .run(vm_function, vec![Value::I64(2)])
        .unwrap();
    assert_eq!(vm_result, Value::I64(42));

    let llvm_function = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("module.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("differential");
    fs::write(source.as_path(), module.ir).unwrap();
    fs::write(
        harness.as_path(),
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{llvm_function}(int64_t);\nint main(void) {{ return g1_f{llvm_function}(2) == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg(source)
        .arg(harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(Command::new(executable).status().unwrap().success());
}

#[test]
fn llvm_and_vm_backends_execute_the_same_captured_callable_program() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-callable-differential.glorious",
        "struct Ticket { value: i64 }\nimpl Use<[1,1]> for Ticket {}\nretain<F>(body: F) -> F where F: Fn<(), Output=i64> { body }\nunique_capture() -> i64 {\n  let state = 40;\n  let mutate = () -> i64 { state = state + 2; state };\n  mutate()\n}\nowned_capture() -> i64 {\n  let ticket = Ticket { value: 42 };\n  let consume = { => { let Ticket { value } = move ticket; value } };\n  consume()\n}\ntext_capture() -> usize {\n  let text = String::concat(\"forty\", \"two\");\n  let length = { => String::byte_len(&text) };\n  length()\n}\nretained_capture() -> i64 {\n  let base = 42;\n  let answer = retain({ => base });\n  answer()\n}\ncopied_capture() -> i64 {\n  let base = 42;\n  let answer = { => base };\n  let copied = retain(answer);\n  copied()\n}\nselected() -> i64 {\n  unique_capture();\n  owned_capture();\n  text_capture();\n  retained_capture();\n  copied_capture();\n  let base = 42;\n  let answer = { => base };\n  answer()\n}\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let vm_function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_function, vec![])
            .unwrap(),
        Value::I64(42)
    );

    let llvm_function = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(module.ir.contains("%g1.callable = type"));
    assert!(module.ir.contains("call i64 %"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("callable.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("callable");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{llvm_function}(void);\nint main(void) {{ return g1_f{llvm_function}() == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_handler_values_own_and_destroy_their_clause_callables() {
    let mut phases = grandiose::compile_source_to_phases_with_options(
        "llvm-handler-value.glorious",
        "effect Stop { stop() -> ! }\nselected() -> i64 { handle perform Stop::stop() { Stop::stop() => 42 } }\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let selected = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let block = &mut phases.mir.functions[selected].blocks[0];
    block.statements.retain(|instruction| {
        !matches!(
            instruction.kind,
            grandiose::compiler_mir::InstructionKind::MakeCallable { dst: 3, .. }
        )
    });
    block.statements.push(grandiose::compiler_mir::Instruction {
        span: grandiose::span::Span::default(),
        kind: grandiose::compiler_mir::InstructionKind::Const {
            dst: 4,
            value: grandiose_vm::Constant::I64(42),
        },
    });
    block.statements.push(grandiose::compiler_mir::Instruction {
        span: grandiose::span::Span::default(),
        kind: grandiose::compiler_mir::InstructionKind::Drop {
            owner: grandiose::compiler_mir::Operand {
                register: 2,
                mode: grandiose::compiler_mir::UseMode::Move,
            },
        },
    });
    block.terminator = grandiose::compiler_mir::Terminator::Return {
        value: Some(grandiose::compiler_mir::Operand {
            register: 4,
            mode: grandiose::compiler_mir::UseMode::Move,
        }),
    };

    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(module.ir.contains("%g1.handler = type"));
    assert!(module.ir.contains("%g1.capture = type"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("handler-value.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("handler-value");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{selected}(void);\nint main(void) {{ return g1_f{selected}() == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_and_vm_backends_execute_the_same_terminal_handler() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-terminal-handler.glorious",
        "struct Resource { text: String }\nimpl Use<[0,1]> for Resource {}\nstruct Parcel { left: Resource, right: Resource }\nconsume(value: Resource) -> () { () }\neffect Stop { stop(value: i64) -> ! }\nprepare() -> String / {Stop} { String::concat(\"le\", \"ak\") }\nleaf(value: i64) -> i64 / {Stop} { perform Stop::stop(value) }\nforward(value: i64) -> i64 / {Stop} { leaf(value) }\nselected() -> i64 { handle { let retained = prepare(); let parcel = Parcel { left: Resource { text: String::concat(\"mo\", \"ved\") }, right: Resource { text: String::concat(\"ke\", \"pt\") } }; let left = parcel.left; consume(move left); forward(42) } { Stop::stop(value) => value } }\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let forward = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "forward")
        .unwrap();
    assert!(forward.blocks.iter().any(|block| {
        matches!(
            block.terminator,
            grandiose::compiler_mir::Terminator::TailCall { .. }
        )
    }));
    let vm_function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_function, vec![])
            .unwrap(),
        Value::I64(42)
    );
    let llvm_function = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(module.ir.contains("%g1.effect_frame = type"));
    assert!(module.ir.contains("%g1.effect_runtime = type"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("terminal-handler.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("terminal-handler");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{llvm_function}(void);\nint main(void) {{ return g1_f{llvm_function}() == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_and_vm_backends_execute_the_same_one_shot_resumption() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-one-shot-resumption.glorious",
        "effect Ask { [1,1] ask(value: i64) -> i64 }\nleaf(value: i64) -> i64 / {Ask} { perform Ask::ask(value) }\nselected() -> i64 { handle { let first = leaf(1); let second = leaf(2); first + second + 1 } { Ask::ask(value) with continuation => resume(continuation, value + 19) } }\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let selected = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let vm_selected = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_selected, vec![])
            .unwrap(),
        Value::I64(42)
    );

    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(module.ir.contains("%g1.resumption = type"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("one-shot-resumption.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("one-shot-resumption");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{selected}(void);\nint main(void) {{ return g1_f{selected}() == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_one_shot_tail_resume_and_cancel_match_the_vm() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-one-shot-tail-cancel.glorious",
        "struct Resource { text: String }\nimpl Use<[0,1]> for Resource {}\nconsume(value: Resource) -> () { () }\neffect Ask { [1,1] ask() -> i64 }\neffect Maybe { [0,1] ask() -> i64 }\neffect Choice { [1,1] first() -> i64 stop() -> ! }\ntail_selected() -> i64 { handle { let answer = perform Ask::ask(); answer + 1 } { Ask::ask() with continuation => tail(continuation, 41) } }\ncancel_selected() -> i64 { handle { let retained = Resource { text: String::concat(\"can\", \"cel\") }; let answer = perform Maybe::ask(); consume(move retained); answer } { Maybe::ask() with continuation => { cancel(continuation); 42 } } }\nmixed_selected() -> i64 { handle { perform Choice::first(); perform Choice::stop() } { Choice::first() with continuation => resume(move continuation, 0), Choice::stop() => 42 } }\nmain() -> () { tail_selected(); cancel_selected(); mixed_selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let function = |name: &str| {
        phases
            .mir
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap()
    };
    let vm_function = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32
    };
    let artifact = verify(phases.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(artifact.clone())
            .run(vm_function("tail_selected"), vec![])
            .unwrap(),
        Value::I64(42)
    );
    assert_eq!(
        Vm::new(artifact.clone())
            .run(vm_function("cancel_selected"), vec![])
            .unwrap(),
        Value::I64(42)
    );
    assert_eq!(
        Vm::new(artifact)
            .run(vm_function("mixed_selected"), vec![])
            .unwrap(),
        Value::I64(42)
    );

    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("one-shot-tail-cancel.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("one-shot-tail-cancel");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{}(void);\nextern int64_t g1_f{}(void);\nextern int64_t g1_f{}(void);\nint main(void) {{ return g1_f{}() == 42 && g1_f{}() == 42 && g1_f{}() == 42 ? 0 : 1; }}\n",
            function("tail_selected"),
            function("cancel_selected"),
            function("mixed_selected"),
            function("tail_selected"),
            function("cancel_selected"),
            function("mixed_selected"),
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_two_shot_resumption_clones_each_native_frame_snapshot() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-two-shot-resumption.glorious",
        "effect Choose { [2,2] choose() -> i64 }\nleaf() -> i64 / {Choose} { perform Choose::choose() }\nselected() -> i64 { handle { let retained = String::concat(\"snap\", \"shot\"); let choice = leaf(); choice + 1 } { Choose::choose() with continuation => { let ignored = resume(continuation, 19); resume(move continuation, 41) } } }\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let selected = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let vm_selected = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_selected, vec![])
            .unwrap(),
        Value::I64(42)
    );

    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(module.ir.contains("@g1_effect_clone_chain"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("two-shot-resumption.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("two-shot-resumption");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{selected}(void);\nint main(void) {{ return g1_f{selected}() == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_two_shot_clones_and_drops_only_live_residual_fields() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-two-shot-residual.glorious",
        "struct Resource { text: String }\nimpl Use<[0,1]> for Resource {}\nconsume(value: Resource) -> () { () }\nconsume_text(value: String) -> () { () }\neffect Choose { [2,2] choose() -> i64 }\nselected() -> i64 { handle { let pair = (Resource { text: String::concat(\"mo\", \"ved\") }, String::concat(\"ke\", \"pt\")); let moved = pair.0; consume(move moved); let choice = perform Choose::choose(); let retained = pair.1; consume_text(move retained); choice } { Choose::choose() with continuation => { let first = resume(continuation, 20); let second = resume(move continuation, 22); first + second } } }\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let selected = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let vm_selected = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_selected, vec![])
            .unwrap(),
        Value::I64(42)
    );

    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("two-shot-residual.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("two-shot-residual");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{selected}(void);\nint main(void) {{ return g1_f{selected}() == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_two_shot_preserves_internal_and_projected_shared_aliases() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-two-shot-shared-aliases.glorious",
        r#"
            struct Pair { left: i64, right: i64 }
            effect Choose { [2,2] choose() -> i64 }
            whole() -> i64 {
                handle {
                    let value = 40;
                    let reference = &value;
                    let selected = perform Choose::choose();
                    *reference + selected
                } {
                    Choose::choose() with continuation => {
                        let ignored = resume(continuation, 1);
                        resume(move continuation, 2)
                    }
                }
            }
            projected() -> i64 {
                handle {
                    let pair = Pair { left: 40, right: 0 };
                    let reference = &pair.left;
                    let selected = perform Choose::choose();
                    *reference + selected
                } {
                    Choose::choose() with continuation => {
                        let ignored = resume(continuation, 1);
                        resume(move continuation, 2)
                    }
                }
            }
            main() -> () { whole(); projected(); () }
        "#,
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let function = |name: &str| {
        phases
            .mir
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap()
    };
    let vm_function = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32
    };
    let artifact = verify(phases.artifact.clone()).unwrap();
    for name in ["whole", "projected"] {
        assert_eq!(
            Vm::new(artifact.clone())
                .run(vm_function(name), vec![])
                .unwrap(),
            Value::I64(42)
        );
    }

    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("two-shot-shared-aliases.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("two-shot-shared-aliases");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{}(void);\nextern int64_t g1_f{}(void);\nint main(void) {{ return g1_f{}() == 42 && g1_f{}() == 42 ? 0 : 1; }}\n",
            function("whole"),
            function("projected"),
            function("whole"),
            function("projected"),
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_two_shot_retains_nested_aggregate_and_callable_captures() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-two-shot-nested-callable.glorious",
        r#"
            effect Choose { [2,2] choose() -> i64 }
            selected() -> i64 {
                handle {
                    let base = 40;
                    let borrowed = &base;
                    let nested = (
                        (() -> i64 { *borrowed },),
                        String::concat("ne", "sted")
                    );
                    let choice = perform Choose::choose();
                    let callable_tuple = nested.0;
                    let callable = callable_tuple.0;
                    let text = nested.1;
                    move text;
                    move callable;
                    choice + 40
                } {
                    Choose::choose() with continuation => {
                        let ignored = resume(continuation, 1);
                        resume(move continuation, 2)
                    }
                }
            }
            main() -> () { selected(); () }
        "#,
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let selected = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let vm_selected = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_selected, vec![])
            .unwrap(),
        Value::I64(42)
    );

    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("two-shot-nested-callable.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("two-shot-nested-callable");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{selected}(void);\nint main(void) {{ return g1_f{selected}() == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_borrowed_replays_do_not_consume_shared_terminal_clause_callable() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-two-shot-terminal-replay.glorious",
        r#"
            effect Choice { [2,2] first() -> i64 stop() -> ! }
            selected() -> i64 {
                handle {
                    perform Choice::first();
                    perform Choice::stop()
                } {
                    Choice::first() with continuation => {
                        let first = resume(continuation, 0);
                        let second = resume(move continuation, 0);
                        first + second
                    },
                    Choice::stop() => 42
                }
            }
            main() -> () { selected(); () }
        "#,
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let selected = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let vm_selected = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_selected, vec![])
            .unwrap(),
        Value::I64(84)
    );

    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("two-shot-terminal-replay.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("two-shot-terminal-replay");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{selected}(void);\nint main(void) {{ return g1_f{selected}() == 84 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_multishot_cancel_drops_owned_suspended_graph() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-multishot-cancel.glorious",
        r#"
            effect Choose { [0,2] choose() -> i64 }
            selected() -> i64 {
                handle {
                    let retained = String::concat("can", "cel");
                    let choice = perform Choose::choose();
                    move retained;
                    choice + 1
                } {
                    Choose::choose() with continuation => {
                        cancel(move continuation);
                        42
                    }
                }
            }
            main() -> () { selected(); () }
        "#,
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let selected = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let vm_selected = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_selected, vec![])
            .unwrap(),
        Value::I64(42)
    );

    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("multishot-cancel.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("multishot-cancel");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern int64_t g1_f{selected}(void);\nint main(void) {{ return g1_f{selected}() == 42 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_backend_invokes_the_native_host_abi_and_consumes_arguments() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-host-call.glorious",
        "selected() -> () { __g1_diagnostic_write(String::concat(\"o\", \"k\")) }\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let llvm_function = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(
        module
            .ir
            .contains("declare void @g1_host_diagnostic_write(ptr)")
    );

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("host.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("host");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\n#include <stddef.h>\ntypedef struct {{ int64_t count; uintptr_t length; unsigned char data[]; }} G1Bytes;\nstatic int observed;\nvoid g1_host_diagnostic_write(G1Bytes *text) {{ observed = text->length == 2 && text->data[0] == 'o' && text->data[1] == 'k'; }}\nextern void g1_f{llvm_function}(void);\nint main(void) {{ g1_f{llvm_function}(); return observed ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}

#[test]
fn llvm_and_vm_backends_execute_the_same_vec_program() {
    let phases = grandiose::compile_source_to_phases_with_options(
        "llvm-array-differential.glorious",
        "enum Item { Text(String), Empty }\nnew_values() -> Vec<i64> { Vec::with_capacity(1) }\nnew_byte_values() -> Vec<u8> { Vec::new() }\nnew_text_values() -> Vec<String> { Vec::new() }\nnew_items() -> Vec<Item> { Vec::new() }\nowned_elements() -> usize {\n  let values = new_text_values();\n  Vec::push(&mut values, \"a\");\n  Vec::push(&mut values, String::concat(\"b\", \"c\"));\n  Vec::len(&values)\n}\nowned_enum_elements() -> usize {\n  let values = new_items();\n  Vec::push(&mut values, Item::Text(String::concat(\"d\", \"e\")));\n  Vec::push(&mut values, Item::Empty);\n  Vec::len(&values)\n}\nselected() -> usize {\n  let values = new_values();\n  Vec::push(&mut values, 10);\n  Vec::push(&mut values, 32);\n  Vec::reserve(&mut values, 4);\n  Vec::len(&values);\n  owned_elements();\n  owned_enum_elements();\n  let byte_values = new_byte_values();\n  Vec::push(&mut byte_values, 65);\n  Vec::push(&mut byte_values, 66);\n  let bytes = Bytes::from_vec(move byte_values);\n  let restored = Bytes::to_vec(move bytes);\n  Vec::len(&restored)\n}\nmain() -> () { selected(); () }",
        grandiose::CompileOptions {
            optimization_level: grandiose::OptimizationLevel::O0,
        },
    )
    .unwrap();
    let vm_function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact.clone()).unwrap())
            .run(vm_function, vec![])
            .unwrap(),
        Value::U64(2)
    );

    let llvm_function = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap();
    let mut options = grandiose::LlvmOptions::default();
    options.emit_entry_wrapper = false;
    let module = grandiose::emit_llvm_ir(&phases, &options).unwrap();
    assert!(module.ir.contains("%g1.array = type"));
    assert!(module.ir.contains("@g1_array_grow"));

    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("array.ll");
    let harness = directory.path().join("harness.c");
    let executable = directory.path().join("array");
    fs::write(&source, module.ir).unwrap();
    fs::write(
        &harness,
        format!(
            "#include <stdint.h>\nextern uint64_t g1_f{llvm_function}(void);\nint main(void) {{ return g1_f{llvm_function}() == 2 ? 0 : 1; }}\n"
        ),
    )
    .unwrap();
    let output = Command::new("clang")
        .arg("-fsanitize=address")
        .arg(&source)
        .arg(&harness)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let execution = Command::new(executable).output().unwrap();
    assert!(
        execution.status.success(),
        "{:?}\n{}",
        execution.status,
        String::from_utf8_lossy(&execution.stderr)
    );
}
