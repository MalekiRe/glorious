//! LLVM IR emission from optimized Grandiose MIR.
//!
//! This first backend slice deliberately supports the pure scalar/control-flow
//! core. Unsupported ownership-heavy operations are diagnosed instead of being
//! assigned an accidental ABI.

use std::collections::{BTreeMap, BTreeSet};

use grandiose_vm::{Constant, Primitive, Type, TypeId};

use crate::{
    CompiledPhases,
    compiler_mir::{self as mir, InstructionKind, Terminator},
    diagnostic::Diagnostic,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmModule {
    pub ir: String,
    pub target_triple: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmOptions {
    pub target_triple: String,
    pub target_data_layout: Option<String>,
    pub emit_entry_wrapper: bool,
}

impl Default for LlvmOptions {
    fn default() -> Self {
        let target_triple = default_target_triple();
        Self {
            target_data_layout: default_target_data_layout(&target_triple).map(str::to_owned),
            target_triple,
            emit_entry_wrapper: true,
        }
    }
}

pub fn default_target_triple() -> String {
    match (std::env::consts::ARCH, std::env::consts::OS) {
        ("x86_64", "linux") => "x86_64-unknown-linux-gnu",
        ("aarch64", "linux") => "aarch64-unknown-linux-gnu",
        ("x86_64", "macos") => "x86_64-apple-darwin",
        ("aarch64", "macos") => "arm64-apple-darwin",
        ("x86_64", "windows") => "x86_64-pc-windows-msvc",
        (arch, os) => return format!("{arch}-unknown-{os}"),
    }
    .into()
}

pub fn default_target_data_layout(target_triple: &str) -> Option<&'static str> {
    Some(match target_triple {
        "x86_64-unknown-linux-gnu" => {
            "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
        }
        "i686-unknown-linux-gnu" => "e-m:e-p:32:32-i64:64-i128:128-f80:128-n8:16:32-S128",
        "aarch64-unknown-linux-gnu" => "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128",
        "x86_64-apple-darwin" => "e-m:o-i64:64-i128:128-f80:128-n8:16:32:64-S128",
        "arm64-apple-darwin" => "e-m:o-i64:64-i128:128-n32:64-S128",
        "x86_64-pc-windows-msvc" => {
            "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
        }
        _ => return None,
    })
}

pub fn emit_llvm_ir(
    phases: &CompiledPhases,
    options: &LlvmOptions,
) -> Result<LlvmModule, Vec<Diagnostic>> {
    Emitter::new(phases, options).emit()
}

struct Emitter<'a> {
    phases: &'a CompiledPhases,
    options: &'a LlvmOptions,
    output: String,
    temporary: u32,
    overflow_widths: BTreeSet<(u16, &'static str)>,
    byte_literals: BTreeMap<Vec<u8>, u32>,
    uses_byte_runtime: bool,
}

impl<'a> Emitter<'a> {
    fn new(phases: &'a CompiledPhases, options: &'a LlvmOptions) -> Self {
        Self {
            phases,
            options,
            output: String::new(),
            temporary: 0,
            overflow_widths: BTreeSet::new(),
            byte_literals: BTreeMap::new(),
            uses_byte_runtime: false,
        }
    }

    fn emit(mut self) -> Result<LlvmModule, Vec<Diagnostic>> {
        let reachable = self.reachable_functions()?;
        self.prepare_byte_runtime(&reachable)?;
        self.line("; Grandiose LLVM backend");
        self.line(&format!(
            "target triple = \"{}\"",
            llvm_string(&self.options.target_triple)
        ));
        if let Some(layout) = &self.options.target_data_layout {
            self.line(&format!("target datalayout = \"{}\"", llvm_string(layout)));
        }
        self.line("");
        self.line("declare void @llvm.trap() cold noreturn nounwind");
        if self.uses_byte_runtime {
            self.emit_byte_runtime();
        }
        self.line("");

        for function in &reachable {
            self.emit_function(*function)?;
        }
        if self.options.emit_entry_wrapper {
            self.emit_entry_wrapper(&reachable)?;
        }

        let declarations = self
            .overflow_widths
            .iter()
            .map(|(width, operation)| {
                format!(
                    "declare {{ i{width}, i1 }} @llvm.{operation}.with.overflow.i{width}(i{width}, i{width}) nounwind readnone"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        if !declarations.is_empty() {
            self.output.push_str(&declarations);
            self.output.push('\n');
        }
        Ok(LlvmModule {
            ir: self.output,
            target_triple: self.options.target_triple.clone(),
        })
    }

    fn reachable_functions(&self) -> Result<Vec<usize>, Vec<Diagnostic>> {
        let Some(entry) = self
            .phases
            .mir
            .functions
            .iter()
            .position(|function| function.name == "main")
        else {
            return Err(vec![backend_error(
                "LLVM emission requires a source `main` function",
            )]);
        };
        let mut pending = vec![entry];
        let mut reachable = BTreeSet::new();
        while let Some(index) = pending.pop() {
            if !reachable.insert(index) {
                continue;
            }
            let Some(function) = self.phases.mir.functions.get(index) else {
                return Err(vec![backend_error(format!(
                    "MIR references missing function {index}"
                ))]);
            };
            for block in &function.blocks {
                match &block.terminator {
                    Terminator::Call {
                        function,
                        normal: _,
                        ..
                    }
                    | Terminator::TailCall { function, .. }
                    | Terminator::CallKnownReceiver { function, .. }
                    | Terminator::TailCallKnownReceiver { function, .. } => {
                        pending.push(*function as usize);
                    }
                    Terminator::CallIndirect {
                        known_function: Some(function),
                        ..
                    }
                    | Terminator::TailCallIndirect {
                        known_function: Some(function),
                        ..
                    } => pending.push(*function as usize),
                    _ => {}
                }
            }
        }
        Ok(reachable.into_iter().collect())
    }

    fn prepare_byte_runtime(&mut self, reachable: &[usize]) -> Result<(), Vec<Diagnostic>> {
        let mut literals = BTreeSet::new();
        for &index in reachable {
            let function = &self.phases.mir.functions[index];
            for &ty in function
                .register_types
                .iter()
                .chain(function.params.iter())
                .chain(std::iter::once(&function.result))
            {
                self.uses_byte_runtime |=
                    self.type_contains_byte_object(ty, &mut BTreeSet::new())?;
            }
            for block in &function.blocks {
                for instruction in &block.statements {
                    if let InstructionKind::Const { value, .. } = &instruction.kind {
                        match value {
                            Constant::Text(value) => {
                                literals.insert(value.as_bytes().to_vec());
                            }
                            Constant::Bytes(value) => {
                                literals.insert(value.clone());
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        self.byte_literals = literals
            .into_iter()
            .enumerate()
            .map(|(index, bytes)| (bytes, index as u32))
            .collect();
        Ok(())
    }

    fn emit_byte_runtime(&mut self) {
        let usize_ty = format!("i{}", self.pointer_width());
        self.line(&format!("%g1.bytes = type {{ i64, {usize_ty}, [0 x i8] }}"));
        let literals = self
            .byte_literals
            .iter()
            .map(|(bytes, index)| (bytes.clone(), *index))
            .collect::<Vec<_>>();
        for (bytes, index) in literals {
            self.line(&format!(
                "@g1.bytes.{index} = private constant {{ i64, {usize_ty}, [{} x i8] }} {{ i64 -1, {usize_ty} {}, [{} x i8] c\"{}\" }}, align 8",
                bytes.len(),
                bytes.len(),
                bytes.len(),
                llvm_bytes(&bytes)
            ));
        }
        self.line(&format!("declare ptr @malloc({usize_ty})"));
        self.line("declare void @free(ptr)");
        self.line(&format!(
            "declare void @llvm.memcpy.p0.p0.{usize_ty}(ptr nocapture writeonly, ptr nocapture readonly, {usize_ty}, i1 immarg)"
        ));
        self.line(&format!("declare i32 @memcmp(ptr, ptr, {usize_ty})"));
        self.line("");
        self.line("define internal void @g1_bytes_retain(ptr %object) {");
        self.line("entry:");
        self.line("  %count.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 0");
        self.line("  %count = load i64, ptr %count.address");
        self.line("  %immortal = icmp eq i64 %count, -1");
        self.line("  br i1 %immortal, label %return, label %owned");
        self.line("owned:");
        self.line("  %incremented = add i64 %count, 1");
        self.line("  store i64 %incremented, ptr %count.address");
        self.line("  br label %return");
        self.line("return:");
        self.line("  ret void");
        self.line("}");
        self.line("");
        self.line("define internal void @g1_bytes_release(ptr %object) {");
        self.line("entry:");
        self.line("  %count.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 0");
        self.line("  %count = load i64, ptr %count.address");
        self.line("  %immortal = icmp eq i64 %count, -1");
        self.line("  br i1 %immortal, label %return, label %owned");
        self.line("owned:");
        self.line("  %last = icmp eq i64 %count, 1");
        self.line("  br i1 %last, label %destroy, label %decrement");
        self.line("decrement:");
        self.line("  %next = sub i64 %count, 1");
        self.line("  store i64 %next, ptr %count.address");
        self.line("  br label %return");
        self.line("destroy:");
        self.line("  call void @free(ptr %object)");
        self.line("  br label %return");
        self.line("return:");
        self.line("  ret void");
        self.line("}");
        self.line("");
        self.line(&format!(
            "define internal ptr @g1_bytes_allocate({usize_ty} %length) {{"
        ));
        self.line("entry:");
        self.line(&format!(
            "  %end = getelementptr %g1.bytes, ptr null, {usize_ty} 1"
        ));
        self.line(&format!("  %header = ptrtoint ptr %end to {usize_ty}"));
        self.line(&format!("  %size = add {usize_ty} %header, %length"));
        self.line(&format!("  %object = call ptr @malloc({usize_ty} %size)"));
        self.line("  %count.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 0");
        self.line("  store i64 1, ptr %count.address");
        self.line(
            "  %length.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 1",
        );
        self.line(&format!("  store {usize_ty} %length, ptr %length.address"));
        self.line("  ret ptr %object");
        self.line("}");
        self.line("");
        self.line("define internal ptr @g1_bytes_data(ptr %object) {");
        self.line("entry:");
        self.line("  %data = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 2, i32 0");
        self.line("  ret ptr %data");
        self.line("}");
        self.line("");
        self.line("define internal i32 @g1_bytes_equal(ptr %left, ptr %right) {");
        self.line("entry:");
        self.line(
            "  %left.length.address = getelementptr inbounds %g1.bytes, ptr %left, i32 0, i32 1",
        );
        self.line(&format!(
            "  %left.length = load {usize_ty}, ptr %left.length.address"
        ));
        self.line(
            "  %right.length.address = getelementptr inbounds %g1.bytes, ptr %right, i32 0, i32 1",
        );
        self.line(&format!(
            "  %right.length = load {usize_ty}, ptr %right.length.address"
        ));
        self.line(&format!(
            "  %same.length = icmp eq {usize_ty} %left.length, %right.length"
        ));
        self.line("  br i1 %same.length, label %compare, label %different");
        self.line("compare:");
        self.line("  %left.data = call ptr @g1_bytes_data(ptr %left)");
        self.line("  %right.data = call ptr @g1_bytes_data(ptr %right)");
        self.line(&format!(
            "  %ordering = call i32 @memcmp(ptr %left.data, ptr %right.data, {usize_ty} %left.length)"
        ));
        self.line("  %same.bytes = icmp eq i32 %ordering, 0");
        self.line("  %same = zext i1 %same.bytes to i32");
        self.line("  ret i32 %same");
        self.line("different:");
        self.line("  ret i32 0");
        self.line("}");
    }

    fn emit_function(&mut self, index: usize) -> Result<(), Vec<Diagnostic>> {
        let function = &self.phases.mir.functions[index];
        if function.receiver_mode.is_some() {
            return Err(vec![unsupported(function, "callable receivers")]);
        }
        if !function.outward_protocols.is_empty() {
            return Err(vec![unsupported(function, "outward effects")]);
        }
        let result = self.llvm_return_type(function.result)?;
        let params = function
            .params
            .iter()
            .enumerate()
            .map(|(index, ty)| Ok(format!("{} %arg{index}", self.llvm_type(*ty)?)))
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?
            .join(", ");
        self.line(&format!("define {} @g1_f{index}({params}) {{", result));
        self.line("entry.allocas:");
        for (register, ty) in function.register_types.iter().enumerate() {
            self.line(&format!("  %r{register} = alloca {}", self.llvm_type(*ty)?));
        }
        for (parameter, ty) in function.params.iter().enumerate() {
            self.line(&format!(
                "  store {} %arg{parameter}, ptr %r{}",
                self.llvm_type(*ty)?,
                parameter + 1
            ));
        }
        self.line(&format!("  br label %bb{}", function.entry));

        for block in &function.blocks {
            self.line(&format!("bb{}:", block.id));
            for instruction in &block.statements {
                self.emit_instruction(function, &instruction.kind)?;
            }
            self.emit_terminator(index, function, &block.terminator)?;
        }
        self.line("}");
        self.line("");
        Ok(())
    }

    fn emit_instruction(
        &mut self,
        function: &mir::Function,
        instruction: &InstructionKind,
    ) -> Result<(), Vec<Diagnostic>> {
        match instruction {
            InstructionKind::Const { dst, value } => {
                let ty = self.register_type(function, *dst)?;
                let value = self.llvm_constant(value)?;
                self.line(&format!("  store {ty} {value}, ptr %r{dst}"));
            }
            InstructionKind::Copy { dst, src } => {
                let value = self.load_operand(function, src)?;
                let ty = self.register_type(function, *dst)?;
                let runtime_ty = self.register_runtime_type(function, *dst)?;
                self.emit_retain(runtime_ty, &value, function)?;
                self.line(&format!("  store {ty} {value}, ptr %r{dst}"));
            }
            InstructionKind::Move { dst, src } => {
                let value = self.load_operand(function, src)?;
                let ty = self.register_type(function, *dst)?;
                self.line(&format!("  store {ty} {value}, ptr %r{dst}"));
            }
            InstructionKind::Borrow { dst, src, .. } => {
                self.line(&format!("  store ptr %r{src}, ptr %r{dst}"));
            }
            InstructionKind::ProjectBorrow {
                dst, src, field, ..
            } => {
                let aggregate = self.register_runtime_type(function, *src)?;
                let aggregate_ty = self.llvm_type(aggregate)?;
                let llvm_field = if matches!(self.runtime_type(aggregate)?, Type::Enum { .. }) {
                    self.enum_slot_words(aggregate, *field)?;
                    field + 1
                } else {
                    self.aggregate_field_type(aggregate, *field)?;
                    *field
                };
                let address = self.temp();
                self.line(&format!(
                    "  %{address} = getelementptr inbounds {aggregate_ty}, ptr %r{src}, i32 0, i32 {llvm_field}"
                ));
                self.line(&format!("  store ptr %{address}, ptr %r{dst}"));
            }
            InstructionKind::Reborrow { dst, src, .. } => {
                let reference = self.load_register(function, *src)?;
                self.line(&format!("  store ptr {reference}, ptr %r{dst}"));
            }
            InstructionKind::DerefCopy { dst, src } | InstructionKind::DerefMove { dst, src } => {
                let reference = self.load_register(function, *src)?;
                let ty = self.register_type(function, *dst)?;
                let value = self.temp();
                self.line(&format!("  %{value} = load {ty}, ptr {reference}"));
                if matches!(instruction, InstructionKind::DerefCopy { .. }) {
                    let runtime_ty = self.register_runtime_type(function, *dst)?;
                    self.emit_retain(runtime_ty, &format!("%{value}"), function)?;
                }
                self.line(&format!("  store {ty} %{value}, ptr %r{dst}"));
            }
            InstructionKind::DerefStore { dst, src } => {
                let reference = self.load_register(function, *dst)?;
                let ty = self.register_type(function, src.register)?;
                let value = self.load_operand(function, src)?;
                if src.mode == mir::UseMode::Copy {
                    let runtime_ty = self.register_runtime_type(function, src.register)?;
                    self.emit_retain(runtime_ty, &value, function)?;
                }
                self.line(&format!("  store {ty} {value}, ptr {reference}"));
            }
            InstructionKind::Construct {
                dst,
                ty,
                variant: None,
                fields,
            } => {
                let aggregate_ty = self.llvm_type(*ty)?;
                let mut aggregate = "poison".to_owned();
                for (index, field) in fields.iter().enumerate() {
                    self.aggregate_field_type(*ty, index as u32)?;
                    let field_ty = self.register_type(function, field.register)?;
                    let value = self.load_operand(function, field)?;
                    if field.mode == mir::UseMode::Copy {
                        let runtime_ty = self.register_runtime_type(function, field.register)?;
                        self.emit_retain(runtime_ty, &value, function)?;
                    }
                    let inserted = self.temp();
                    self.line(&format!(
                        "  %{inserted} = insertvalue {aggregate_ty} {aggregate}, {field_ty} {value}, {index}"
                    ));
                    aggregate = format!("%{inserted}");
                }
                self.line(&format!("  store {aggregate_ty} {aggregate}, ptr %r{dst}"));
            }
            InstructionKind::Construct {
                dst,
                ty,
                variant: Some(variant),
                fields,
            } => {
                let aggregate_ty = self.llvm_type(*ty)?;
                let variants = match self.runtime_type(*ty)? {
                    Type::Enum { variants, .. } => variants,
                    other => {
                        return Err(vec![backend_error(format!(
                            "tagged construction requires an enum, found {other:?}"
                        ))]);
                    }
                };
                let declaration = variants.get(*variant as usize).ok_or_else(|| {
                    vec![backend_error(format!(
                        "enum t{ty} has no variant {variant}"
                    ))]
                })?;
                if declaration.fields.len() != fields.len() {
                    return Err(vec![backend_error(format!(
                        "enum t{ty} variant {variant} expects {} fields, received {}",
                        declaration.fields.len(),
                        fields.len()
                    ))]);
                }
                let tagged = self.temp();
                self.line(&format!(
                    "  %{tagged} = insertvalue {aggregate_ty} poison, i32 {variant}, 0"
                ));
                let mut aggregate = format!("%{tagged}");
                for (index, field) in fields.iter().enumerate() {
                    let words = self.enum_slot_words(*ty, index as u32)?;
                    let slot_ty = format!("[{words} x i128]");
                    let slot = self.temp();
                    self.line(&format!("  %{slot} = alloca {slot_ty}"));
                    self.line(&format!(
                        "  store {slot_ty} zeroinitializer, ptr %{slot}, align 1"
                    ));
                    let field_ty = self.register_type(function, field.register)?;
                    let value = self.load_operand(function, field)?;
                    if field.mode == mir::UseMode::Copy {
                        let runtime_ty = self.register_runtime_type(function, field.register)?;
                        self.emit_retain(runtime_ty, &value, function)?;
                    }
                    self.line(&format!("  store {field_ty} {value}, ptr %{slot}, align 1"));
                    let packed = self.temp();
                    self.line(&format!(
                        "  %{packed} = load {slot_ty}, ptr %{slot}, align 1"
                    ));
                    let inserted = self.temp();
                    self.line(&format!(
                        "  %{inserted} = insertvalue {aggregate_ty} {aggregate}, {slot_ty} %{packed}, {}",
                        index + 1
                    ));
                    aggregate = format!("%{inserted}");
                }
                self.line(&format!("  store {aggregate_ty} {aggregate}, ptr %r{dst}"));
            }
            InstructionKind::ProjectCopy { dst, src, field }
            | InstructionKind::ProjectMove { dst, src, field } => {
                let aggregate_id = self.register_runtime_type(function, src.register)?;
                let aggregate_ty = self.llvm_type(aggregate_id)?;
                let aggregate = self.load_operand(function, src)?;
                let field_ty = self.register_type(function, *dst)?;
                let value = if matches!(self.runtime_type(aggregate_id)?, Type::Enum { .. }) {
                    let words = self.enum_slot_words(aggregate_id, *field)?;
                    let slot_ty = format!("[{words} x i128]");
                    let packed = self.temp();
                    self.line(&format!(
                        "  %{packed} = extractvalue {aggregate_ty} {aggregate}, {}",
                        field + 1
                    ));
                    let slot = self.temp();
                    self.line(&format!("  %{slot} = alloca {slot_ty}"));
                    self.line(&format!(
                        "  store {slot_ty} %{packed}, ptr %{slot}, align 1"
                    ));
                    let value = self.temp();
                    self.line(&format!(
                        "  %{value} = load {field_ty}, ptr %{slot}, align 1"
                    ));
                    value
                } else {
                    self.aggregate_field_type(aggregate_id, *field)?;
                    let value = self.temp();
                    self.line(&format!(
                        "  %{value} = extractvalue {aggregate_ty} {aggregate}, {field}"
                    ));
                    value
                };
                if matches!(instruction, InstructionKind::ProjectCopy { .. }) {
                    let runtime_ty = self.register_runtime_type(function, *dst)?;
                    self.emit_retain(runtime_ty, &format!("%{value}"), function)?;
                }
                self.line(&format!("  store {field_ty} %{value}, ptr %r{dst}"));
            }
            InstructionKind::EnumTag { dst, src } => {
                let aggregate_id = self.register_runtime_type(function, *src)?;
                if !matches!(self.runtime_type(aggregate_id)?, Type::Enum { .. }) {
                    return Err(vec![unsupported(function, "tag read from a non-enum")]);
                }
                let aggregate_ty = self.llvm_type(aggregate_id)?;
                let aggregate = self.load_register(function, *src)?;
                let tag = self.temp();
                self.line(&format!(
                    "  %{tag} = extractvalue {aggregate_ty} {aggregate}, 0"
                ));
                let dst_ty = self.register_type(function, *dst)?;
                self.line(&format!("  store {dst_ty} %{tag}, ptr %r{dst}"));
            }
            InstructionKind::Primitive {
                dst,
                primitive,
                args,
            } => self.emit_primitive(function, *dst, *primitive, args)?,
            InstructionKind::Drop { owner } => {
                let ty = self.register_runtime_type(function, owner.register)?;
                if self.is_byte_object(ty)? {
                    let value = self.load_operand(function, owner)?;
                    self.line(&format!("  call void @g1_bytes_release(ptr {value})"));
                } else if self.type_contains_byte_object(ty, &mut BTreeSet::new())? {
                    return Err(vec![unsupported(
                        function,
                        "dropping aggregates that contain Text or Bytes",
                    )]);
                }
            }
            InstructionKind::EndBorrow { .. } | InstructionKind::Deconstruct { .. } => {}
            other => {
                return Err(vec![unsupported(
                    function,
                    format!("MIR instruction {other:?}"),
                )]);
            }
        }
        Ok(())
    }

    fn emit_primitive(
        &mut self,
        function: &mir::Function,
        dst: u32,
        primitive: Primitive,
        args: &[mir::Operand],
    ) -> Result<(), Vec<Diagnostic>> {
        let dst_ty = self.register_type(function, dst)?;
        let loaded = args
            .iter()
            .map(|operand| {
                Ok((
                    self.register_type(function, operand.register)?,
                    self.load_operand(function, operand)?,
                ))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        for (operand, (_, value)) in args.iter().zip(&loaded) {
            if operand.mode == mir::UseMode::Copy {
                let ty = self.register_runtime_type(function, operand.register)?;
                self.emit_retain(ty, value, function)?;
            }
        }
        let result = match primitive {
            Primitive::IntCheckedAdd | Primitive::IntCheckedSub | Primitive::IntCheckedMul => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed checked arithmetic")]);
                };
                let width = integer_width(ty)
                    .ok_or_else(|| vec![unsupported(function, "non-integer checked arithmetic")])?;
                let signed = self.register_is_signed(function, args[0].register)?;
                let operation = match (primitive, signed) {
                    (Primitive::IntCheckedAdd, true) => "sadd",
                    (Primitive::IntCheckedAdd, false) => "uadd",
                    (Primitive::IntCheckedSub, true) => "ssub",
                    (Primitive::IntCheckedSub, false) => "usub",
                    (Primitive::IntCheckedMul, true) => "smul",
                    (Primitive::IntCheckedMul, false) => "umul",
                    _ => unreachable!(),
                };
                self.overflow_widths.insert((width, operation));
                let pair = self.temp();
                let value = self.temp();
                let overflow = self.temp();
                let trap = self.temp();
                let continuation = self.temp();
                self.line(&format!(
                    "  %{pair} = call {{ {ty}, i1 }} @llvm.{operation}.with.overflow.i{width}({ty} {left}, {ty} {right})"
                ));
                self.line(&format!(
                    "  %{value} = extractvalue {{ {ty}, i1 }} %{pair}, 0"
                ));
                self.line(&format!(
                    "  %{overflow} = extractvalue {{ {ty}, i1 }} %{pair}, 1"
                ));
                self.line(&format!(
                    "  br i1 %{overflow}, label %trap{trap}, label %cont{continuation}"
                ));
                self.line(&format!("trap{trap}:"));
                self.line("  call void @llvm.trap()");
                self.line("  unreachable");
                self.line(&format!("cont{continuation}:"));
                format!("%{value}")
            }
            Primitive::IntCheckedDiv | Primitive::IntCheckedRem => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(
                        function,
                        "malformed checked division or remainder",
                    )]);
                };
                let width = integer_width(ty).ok_or_else(|| {
                    vec![unsupported(
                        function,
                        "non-integer checked division or remainder",
                    )]
                })?;
                let zero = self.temp();
                self.line(&format!("  %{zero} = icmp eq {ty} {right}, 0"));
                let invalid = if self.register_is_signed(function, args[0].register)? {
                    let minimum = signed_minimum(width);
                    let minimum_operand = self.temp();
                    let negative_one = self.temp();
                    let overflow = self.temp();
                    let invalid = self.temp();
                    self.line(&format!(
                        "  %{minimum_operand} = icmp eq {ty} {left}, {minimum}"
                    ));
                    self.line(&format!("  %{negative_one} = icmp eq {ty} {right}, -1"));
                    self.line(&format!(
                        "  %{overflow} = and i1 %{minimum_operand}, %{negative_one}"
                    ));
                    self.line(&format!("  %{invalid} = or i1 %{zero}, %{overflow}"));
                    invalid
                } else {
                    zero
                };
                self.emit_trap_if(invalid);
                let temporary = self.temp();
                let operation = match (
                    primitive,
                    self.register_is_signed(function, args[0].register)?,
                ) {
                    (Primitive::IntCheckedDiv, true) => "sdiv",
                    (Primitive::IntCheckedDiv, false) => "udiv",
                    (Primitive::IntCheckedRem, true) => "srem",
                    (Primitive::IntCheckedRem, false) => "urem",
                    _ => unreachable!(),
                };
                self.line(&format!(
                    "  %{temporary} = {operation} {ty} {left}, {right}"
                ));
                format!("%{temporary}")
            }
            Primitive::IntWrappingAdd
            | Primitive::IntWrappingSub
            | Primitive::IntWrappingMul
            | Primitive::IntBitAnd
            | Primitive::IntBitOr
            | Primitive::IntBitXor
            | Primitive::IntShl
            | Primitive::IntShr => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed integer primitive")]);
                };
                let operation = match primitive {
                    Primitive::IntWrappingAdd => "add",
                    Primitive::IntWrappingSub => "sub",
                    Primitive::IntWrappingMul => "mul",
                    Primitive::IntBitAnd => "and",
                    Primitive::IntBitOr => "or",
                    Primitive::IntBitXor => "xor",
                    Primitive::IntShl => "shl",
                    Primitive::IntShr if self.register_is_signed(function, args[0].register)? => {
                        "ashr"
                    }
                    Primitive::IntShr => "lshr",
                    _ => unreachable!(),
                };
                let shift = matches!(primitive, Primitive::IntShl | Primitive::IntShr);
                if shift {
                    let width = integer_width(ty)
                        .ok_or_else(|| vec![unsupported(function, "non-integer shift operand")])?;
                    let count_ty = &loaded[1].0;
                    let invalid = self.temp();
                    self.line(&format!(
                        "  %{invalid} = icmp uge {count_ty} {right}, {width}"
                    ));
                    self.emit_trap_if(invalid);
                }
                let right = if shift && loaded[1].0 != ty {
                    let widened = self.temp();
                    self.line(&format!(
                        "  %{widened} = zext {} {right} to {ty}",
                        loaded[1].0
                    ));
                    format!("%{widened}")
                } else {
                    right.to_owned()
                };
                let temporary = self.temp();
                self.line(&format!(
                    "  %{temporary} = {operation} {ty} {left}, {right}"
                ));
                format!("%{temporary}")
            }
            Primitive::IntBitNot | Primitive::IntCheckedNeg | Primitive::IntWrappingNeg => {
                let Some((ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed unary integer primitive",
                    )]);
                };
                let signed = self.register_is_signed(function, args[0].register)?;
                if primitive == Primitive::IntCheckedNeg {
                    let invalid = self.temp();
                    if signed {
                        let width = integer_width(ty).ok_or_else(|| {
                            vec![unsupported(function, "non-integer checked negation")]
                        })?;
                        self.line(&format!(
                            "  %{invalid} = icmp eq {ty} {value}, {}",
                            signed_minimum(width)
                        ));
                    } else {
                        self.line(&format!("  %{invalid} = icmp ne {ty} {value}, 0"));
                    }
                    self.emit_trap_if(invalid);
                }
                let temporary = self.temp();
                let operation = if primitive == Primitive::IntBitNot {
                    "xor"
                } else {
                    "sub"
                };
                let identity = if primitive == Primitive::IntBitNot {
                    "-1"
                } else {
                    "0"
                };
                self.line(&format!(
                    "  %{temporary} = {operation} {ty} {identity}, {value}"
                ));
                format!("%{temporary}")
            }
            Primitive::IntEq
            | Primitive::IntNe
            | Primitive::IntLt
            | Primitive::IntLe
            | Primitive::IntGt
            | Primitive::IntGe => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed integer comparison")]);
                };
                let signed = self.register_is_signed(function, args[0].register)?;
                let predicate = match (primitive, signed) {
                    (Primitive::IntEq, _) => "eq",
                    (Primitive::IntNe, _) => "ne",
                    (Primitive::IntLt, true) => "slt",
                    (Primitive::IntLt, false) => "ult",
                    (Primitive::IntLe, true) => "sle",
                    (Primitive::IntLe, false) => "ule",
                    (Primitive::IntGt, true) => "sgt",
                    (Primitive::IntGt, false) => "ugt",
                    (Primitive::IntGe, true) => "sge",
                    (Primitive::IntGe, false) => "uge",
                    _ => unreachable!(),
                };
                let flag = self.temp();
                let extended = self.temp();
                self.line(&format!(
                    "  %{flag} = icmp {predicate} {ty} {left}, {right}"
                ));
                self.line(&format!("  %{extended} = zext i1 %{flag} to {dst_ty}"));
                format!("%{extended}")
            }
            Primitive::IntConvertChecked | Primitive::IntConvertWrapping => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed integer conversion")]);
                };
                let source_id = self.register_runtime_type(function, args[0].register)?;
                let target_id = self.register_runtime_type(function, dst)?;
                let (source_signed, source_width) = self
                    .integer_type_info(source_id)
                    .ok_or_else(|| vec![unsupported(function, "non-integer conversion source")])?;
                let (target_signed, target_width) = self
                    .integer_type_info(target_id)
                    .ok_or_else(|| vec![unsupported(function, "non-integer conversion target")])?;
                if primitive == Primitive::IntConvertChecked {
                    let mut invalid = None;
                    let mut add_guard = |this: &mut Self, guard: u32| {
                        invalid = Some(if let Some(previous) = invalid {
                            let combined = this.temp();
                            this.line(&format!("  %{combined} = or i1 %{previous}, %{guard}"));
                            combined
                        } else {
                            guard
                        });
                    };
                    match (source_signed, target_signed) {
                        (true, true) if target_width < source_width => {
                            let below = self.temp();
                            let above = self.temp();
                            self.line(&format!(
                                "  %{below} = icmp slt {source_ty} {value}, {}",
                                signed_minimum(target_width)
                            ));
                            self.line(&format!(
                                "  %{above} = icmp sgt {source_ty} {value}, {}",
                                signed_maximum(target_width)
                            ));
                            add_guard(self, below);
                            add_guard(self, above);
                        }
                        (false, false) if target_width < source_width => {
                            let above = self.temp();
                            self.line(&format!(
                                "  %{above} = icmp ugt {source_ty} {value}, {}",
                                unsigned_maximum(target_width)
                            ));
                            add_guard(self, above);
                        }
                        (true, false) => {
                            let negative = self.temp();
                            self.line(&format!("  %{negative} = icmp slt {source_ty} {value}, 0"));
                            add_guard(self, negative);
                            if target_width < source_width {
                                let above = self.temp();
                                self.line(&format!(
                                    "  %{above} = icmp ugt {source_ty} {value}, {}",
                                    unsigned_maximum(target_width)
                                ));
                                add_guard(self, above);
                            }
                        }
                        (false, true) if target_width <= source_width => {
                            let above = self.temp();
                            self.line(&format!(
                                "  %{above} = icmp ugt {source_ty} {value}, {}",
                                signed_maximum(target_width)
                            ));
                            add_guard(self, above);
                        }
                        _ => {}
                    }
                    if let Some(invalid) = invalid {
                        self.emit_trap_if(invalid);
                    }
                }
                if source_width == target_width {
                    value.clone()
                } else {
                    let temporary = self.temp();
                    let operation = if target_width < source_width {
                        "trunc"
                    } else if source_signed {
                        "sext"
                    } else {
                        "zext"
                    };
                    self.line(&format!(
                        "  %{temporary} = {operation} {source_ty} {value} to {dst_ty}"
                    ));
                    format!("%{temporary}")
                }
            }
            Primitive::FloatAdd
            | Primitive::FloatSub
            | Primitive::FloatMul
            | Primitive::FloatDiv
            | Primitive::FloatRem => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed float arithmetic")]);
                };
                let operation = match primitive {
                    Primitive::FloatAdd => "fadd",
                    Primitive::FloatSub => "fsub",
                    Primitive::FloatMul => "fmul",
                    Primitive::FloatDiv => "fdiv",
                    Primitive::FloatRem => "frem",
                    _ => unreachable!(),
                };
                let temporary = self.temp();
                self.line(&format!(
                    "  %{temporary} = {operation} {ty} {left}, {right}"
                ));
                format!("%{temporary}")
            }
            Primitive::FloatNeg => {
                let Some((ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed float negation")]);
                };
                let temporary = self.temp();
                self.line(&format!("  %{temporary} = fneg {ty} {value}"));
                format!("%{temporary}")
            }
            Primitive::FloatEq
            | Primitive::FloatNe
            | Primitive::FloatLt
            | Primitive::FloatLe
            | Primitive::FloatGt
            | Primitive::FloatGe => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed float comparison")]);
                };
                let predicate = match primitive {
                    Primitive::FloatEq => "oeq",
                    Primitive::FloatNe => "une",
                    Primitive::FloatLt => "olt",
                    Primitive::FloatLe => "ole",
                    Primitive::FloatGt => "ogt",
                    Primitive::FloatGe => "oge",
                    _ => unreachable!(),
                };
                let flag = self.temp();
                let extended = self.temp();
                self.line(&format!(
                    "  %{flag} = fcmp {predicate} {ty} {left}, {right}"
                ));
                self.line(&format!("  %{extended} = zext i1 %{flag} to {dst_ty}"));
                format!("%{extended}")
            }
            Primitive::FloatToBits | Primitive::FloatFromBits => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed float bit conversion",
                    )]);
                };
                let temporary = self.temp();
                self.line(&format!(
                    "  %{temporary} = bitcast {source_ty} {value} to {dst_ty}"
                ));
                format!("%{temporary}")
            }
            Primitive::FloatConvert => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed float conversion")]);
                };
                if source_ty == &dst_ty {
                    value.clone()
                } else {
                    let temporary = self.temp();
                    let operation = if source_ty == "float" {
                        "fpext"
                    } else {
                        "fptrunc"
                    };
                    self.line(&format!(
                        "  %{temporary} = {operation} {source_ty} {value} to {dst_ty}"
                    ));
                    format!("%{temporary}")
                }
            }
            Primitive::IntToFloat => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed integer-to-float conversion",
                    )]);
                };
                let source_id = self.register_runtime_type(function, args[0].register)?;
                let (signed, _) = self.integer_type_info(source_id).ok_or_else(|| {
                    vec![unsupported(function, "non-integer integer-to-float source")]
                })?;
                let temporary = self.temp();
                let operation = if signed { "sitofp" } else { "uitofp" };
                self.line(&format!(
                    "  %{temporary} = {operation} {source_ty} {value} to {dst_ty}"
                ));
                format!("%{temporary}")
            }
            Primitive::FloatToIntChecked => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed checked float-to-integer conversion",
                    )]);
                };
                let target_id = self.register_runtime_type(function, dst)?;
                let (signed, width) = self.integer_type_info(target_id).ok_or_else(|| {
                    vec![unsupported(
                        function,
                        "non-integer checked float conversion target",
                    )]
                })?;
                let lower = if signed {
                    llvm_float_power(source_ty, i32::from(width) - 1, true)?
                } else {
                    if source_ty == "float" {
                        "0.000000e+00".to_owned()
                    } else {
                        "0.000000e+00".to_owned()
                    }
                };
                let upper =
                    llvm_float_power(source_ty, i32::from(width - u16::from(signed)), false)?;
                let unordered = self.temp();
                let below = self.temp();
                let above = self.temp();
                let invalid_range = self.temp();
                let invalid = self.temp();
                self.line(&format!(
                    "  %{unordered} = fcmp uno {source_ty} {value}, {value}"
                ));
                self.line(&format!(
                    "  %{below} = fcmp olt {source_ty} {value}, {lower}"
                ));
                self.line(&format!(
                    "  %{above} = fcmp oge {source_ty} {value}, {upper}"
                ));
                self.line(&format!("  %{invalid_range} = or i1 %{below}, %{above}"));
                self.line(&format!(
                    "  %{invalid} = or i1 %{unordered}, %{invalid_range}"
                ));
                self.emit_trap_if(invalid);
                let temporary = self.temp();
                let operation = if signed { "fptosi" } else { "fptoui" };
                self.line(&format!(
                    "  %{temporary} = {operation} {source_ty} {value} to {dst_ty}"
                ));
                format!("%{temporary}")
            }
            Primitive::TextByteLen | Primitive::BytesLen => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed byte length operation",
                    )]);
                };
                let length_address = self.temp();
                let length = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.bytes, ptr {object}, i32 0, i32 1"
                ));
                self.line(&format!(
                    "  %{length} = load {dst_ty}, ptr %{length_address}"
                ));
                self.release_byte_operands(function, args, &loaded)?;
                format!("%{length}")
            }
            Primitive::TextEq => {
                let Some((_, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed text equality")]);
                };
                let result = self.temp();
                self.line(&format!(
                    "  %{result} = call i32 @g1_bytes_equal(ptr {left}, ptr {right})"
                ));
                self.release_byte_operands(function, args, &loaded)?;
                format!("%{result}")
            }
            Primitive::TextConcat | Primitive::BytesConcat => {
                let Some((_, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed byte concatenation")]);
                };
                let result = self.emit_byte_concat(left, right);
                self.release_byte_operands(function, args, &loaded)?;
                result
            }
            Primitive::TextAsBytes => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed Text-to-Bytes conversion",
                    )]);
                };
                object.clone()
            }
            Primitive::BytesGet => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed byte indexing")]);
                };
                let Some((index_ty, index)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed byte indexing")]);
                };
                let length_address = self.temp();
                let length = self.temp();
                let invalid = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.bytes, ptr {object}, i32 0, i32 1"
                ));
                self.line(&format!(
                    "  %{length} = load {index_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{invalid} = icmp uge {index_ty} {index}, %{length}"
                ));
                self.emit_trap_if(invalid);
                let data = self.temp();
                let address = self.temp();
                let byte = self.temp();
                self.line(&format!(
                    "  %{data} = call ptr @g1_bytes_data(ptr {object})"
                ));
                self.line(&format!(
                    "  %{address} = getelementptr inbounds i8, ptr %{data}, {index_ty} {index}"
                ));
                self.line(&format!("  %{byte} = load i8, ptr %{address}"));
                self.release_byte_operands(function, args, &loaded)?;
                format!("%{byte}")
            }
            Primitive::BytesSlice => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed byte slice")]);
                };
                let Some((index_ty, start)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed byte slice")]);
                };
                let Some((end_ty, end)) = loaded.get(2) else {
                    return Err(vec![unsupported(function, "malformed byte slice")]);
                };
                if index_ty != end_ty {
                    return Err(vec![unsupported(
                        function,
                        "byte slice index width mismatch",
                    )]);
                }
                let length_address = self.temp();
                let source_length = self.temp();
                let reverse = self.temp();
                let beyond = self.temp();
                let invalid = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.bytes, ptr {object}, i32 0, i32 1"
                ));
                self.line(&format!(
                    "  %{source_length} = load {index_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{reverse} = icmp ugt {index_ty} {start}, {end}"
                ));
                self.line(&format!(
                    "  %{beyond} = icmp ugt {index_ty} {end}, %{source_length}"
                ));
                self.line(&format!("  %{invalid} = or i1 %{reverse}, %{beyond}"));
                self.emit_trap_if(invalid);
                let length = self.temp();
                let result = self.temp();
                let source_data = self.temp();
                let source_start = self.temp();
                let result_data = self.temp();
                self.line(&format!("  %{length} = sub {index_ty} {end}, {start}"));
                self.line(&format!(
                    "  %{result} = call ptr @g1_bytes_allocate({index_ty} %{length})"
                ));
                self.line(&format!(
                    "  %{source_data} = call ptr @g1_bytes_data(ptr {object})"
                ));
                self.line(&format!(
                    "  %{source_start} = getelementptr inbounds i8, ptr %{source_data}, {index_ty} {start}"
                ));
                self.line(&format!(
                    "  %{result_data} = call ptr @g1_bytes_data(ptr %{result})"
                ));
                self.line(&format!(
                    "  call void @llvm.memcpy.p0.p0.{index_ty}(ptr %{result_data}, ptr %{source_start}, {index_ty} %{length}, i1 false)"
                ));
                self.release_byte_operands(function, args, &loaded)?;
                format!("%{result}")
            }
            Primitive::CharToU32 => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed character conversion",
                    )]);
                };
                if source_ty != &dst_ty {
                    return Err(vec![unsupported(
                        function,
                        "character conversion with mismatched widths",
                    )]);
                }
                value.clone()
            }
            Primitive::CharFromU32Checked => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed character conversion",
                    )]);
                };
                if source_ty != &dst_ty {
                    return Err(vec![unsupported(
                        function,
                        "character conversion with mismatched widths",
                    )]);
                }
                let above_unicode = self.temp();
                let surrogate_start = self.temp();
                let surrogate_end = self.temp();
                let surrogate = self.temp();
                let invalid = self.temp();
                self.line(&format!(
                    "  %{above_unicode} = icmp ugt {source_ty} {value}, 1114111"
                ));
                self.line(&format!(
                    "  %{surrogate_start} = icmp uge {source_ty} {value}, 55296"
                ));
                self.line(&format!(
                    "  %{surrogate_end} = icmp ule {source_ty} {value}, 57343"
                ));
                self.line(&format!(
                    "  %{surrogate} = and i1 %{surrogate_start}, %{surrogate_end}"
                ));
                self.line(&format!(
                    "  %{invalid} = or i1 %{above_unicode}, %{surrogate}"
                ));
                self.emit_trap_if(invalid);
                value.clone()
            }
            _ => {
                return Err(vec![unsupported(
                    function,
                    format!("primitive {primitive:?}"),
                )]);
            }
        };
        self.line(&format!("  store {dst_ty} {result}, ptr %r{dst}"));
        Ok(())
    }

    fn emit_terminator(
        &mut self,
        function_index: usize,
        function: &mir::Function,
        terminator: &Terminator,
    ) -> Result<(), Vec<Diagnostic>> {
        match terminator {
            Terminator::Goto(edge) => self.emit_edge(function, edge)?,
            Terminator::Return { value } => {
                if let Some(value) = value {
                    let ty = self.register_type(function, value.register)?;
                    let loaded = self.load_operand(function, value)?;
                    if value.mode == mir::UseMode::Copy {
                        let runtime_ty = self.register_runtime_type(function, value.register)?;
                        self.emit_retain(runtime_ty, &loaded, function)?;
                    }
                    self.line(&format!("  ret {ty} {loaded}"));
                } else {
                    self.line("  ret void");
                }
            }
            Terminator::Call {
                result,
                function: callee,
                args,
                normal,
            } => self.emit_call(function, *result, *callee as usize, args, normal, false)?,
            Terminator::CallSelf {
                result,
                args,
                normal,
            } => self.emit_call(function, *result, function_index, args, normal, false)?,
            Terminator::TailCall {
                function: callee,
                args,
            } => self.emit_tail_call(function, *callee as usize, args)?,
            Terminator::TailCallSelf { args } => {
                self.emit_tail_call(function, function_index, args)?
            }
            Terminator::Switch {
                discr,
                cases,
                otherwise,
            } => {
                if !otherwise.args.is_empty() || cases.iter().any(|(_, edge)| !edge.args.is_empty())
                {
                    return Err(vec![unsupported(
                        function,
                        "switch edges carrying block arguments",
                    )]);
                }
                let ty = self.register_type(function, discr.register)?;
                let value = self.load_operand(function, discr)?;
                self.line(&format!(
                    "  switch {ty} {value}, label %bb{} [",
                    otherwise.target
                ));
                for (constant, edge) in cases {
                    self.line(&format!(
                        "    {ty} {}, label %bb{}",
                        llvm_scalar_constant(constant)?,
                        edge.target
                    ));
                }
                self.line("  ]");
            }
            Terminator::Abort { .. } => {
                self.line("  call void @llvm.trap()");
                self.line("  unreachable");
            }
            Terminator::Unreachable => self.line("  unreachable"),
            other => {
                return Err(vec![unsupported(
                    function,
                    format!("MIR terminator {other:?}"),
                )]);
            }
        }
        Ok(())
    }

    fn emit_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callee_index: usize,
        args: &[mir::Operand],
        normal: &mir::Edge,
        tail: bool,
    ) -> Result<(), Vec<Diagnostic>> {
        let callee = self
            .phases
            .mir
            .functions
            .get(callee_index)
            .ok_or_else(|| vec![unsupported(caller, "call to a missing function")])?;
        let arguments = args
            .iter()
            .map(|operand| {
                let ty = self.register_type(caller, operand.register)?;
                let value = self.load_operand(caller, operand)?;
                if operand.mode == mir::UseMode::Copy {
                    let runtime_ty = self.register_runtime_type(caller, operand.register)?;
                    self.emit_retain(runtime_ty, &value, caller)?;
                }
                Ok(format!("{ty} {value}"))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?
            .join(", ");
        let result_ty = self.llvm_return_type(callee.result)?;
        let call = if result_ty == "void" {
            self.line(&format!(
                "  {}call void @g1_f{callee_index}({arguments})",
                if tail { "tail " } else { "" }
            ));
            None
        } else {
            let temporary = self.temp();
            self.line(&format!(
                "  %{temporary} = {}call {result_ty} @g1_f{callee_index}({arguments})",
                if tail { "tail " } else { "" }
            ));
            Some(temporary)
        };
        if let (Some(dst), Some(value)) = (result, call) {
            self.line(&format!("  store {result_ty} %{value}, ptr %r{dst}"));
        }
        self.emit_edge_with_preassigned(caller, normal, result.into_iter().collect())
    }

    fn emit_tail_call(
        &mut self,
        caller: &mir::Function,
        callee: usize,
        args: &[mir::Operand],
    ) -> Result<(), Vec<Diagnostic>> {
        let target = self
            .phases
            .mir
            .functions
            .get(callee)
            .ok_or_else(|| vec![unsupported(caller, "tail call to a missing function")])?;
        let arguments = args
            .iter()
            .map(|operand| {
                let ty = self.register_type(caller, operand.register)?;
                let value = self.load_operand(caller, operand)?;
                if operand.mode == mir::UseMode::Copy {
                    let runtime_ty = self.register_runtime_type(caller, operand.register)?;
                    self.emit_retain(runtime_ty, &value, caller)?;
                }
                Ok(format!("{ty} {value}"))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?
            .join(", ");
        let result = self.llvm_return_type(target.result)?;
        if result == "void" {
            self.line(&format!("  tail call void @g1_f{callee}({arguments})"));
            self.line("  ret void");
        } else {
            let temporary = self.temp();
            self.line(&format!(
                "  %{temporary} = tail call {result} @g1_f{callee}({arguments})"
            ));
            self.line(&format!("  ret {result} %{temporary}"));
        }
        Ok(())
    }

    fn emit_edge(
        &mut self,
        function: &mir::Function,
        edge: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        self.emit_edge_with_preassigned(function, edge, BTreeSet::new())
    }

    fn emit_edge_with_preassigned(
        &mut self,
        function: &mir::Function,
        edge: &mir::Edge,
        preassigned: BTreeSet<u32>,
    ) -> Result<(), Vec<Diagnostic>> {
        let target = function
            .blocks
            .iter()
            .find(|block| block.id == edge.target)
            .ok_or_else(|| vec![unsupported(function, "edge to a missing block")])?;
        let parameters = target
            .params
            .iter()
            .filter(|parameter| !preassigned.contains(&parameter.register))
            .collect::<Vec<_>>();
        if parameters.len() != edge.args.len() {
            return Err(vec![unsupported(function, "malformed block argument edge")]);
        }
        let values = edge
            .args
            .iter()
            .map(|operand| {
                let ty = self.register_type(function, operand.register)?;
                let value = self.load_operand(function, operand)?;
                if operand.mode == mir::UseMode::Copy {
                    let runtime_ty = self.register_runtime_type(function, operand.register)?;
                    self.emit_retain(runtime_ty, &value, function)?;
                }
                Ok((ty, value))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        for (parameter, (ty, value)) in parameters.into_iter().zip(values) {
            self.line(&format!(
                "  store {ty} {value}, ptr %r{}",
                parameter.register
            ));
        }
        self.line(&format!("  br label %bb{}", edge.target));
        Ok(())
    }

    fn emit_entry_wrapper(&mut self, reachable: &[usize]) -> Result<(), Vec<Diagnostic>> {
        let entry = reachable
            .iter()
            .copied()
            .find(|index| self.phases.mir.functions[*index].name == "main")
            .unwrap();
        let function = &self.phases.mir.functions[entry];
        if !function.params.is_empty() || function.receiver_mode.is_some() {
            return Err(vec![unsupported(
                function,
                "native entry points with parameters",
            )]);
        }
        let result = self.llvm_return_type(function.result)?;
        self.line("define i32 @main() {");
        if result == "void" {
            self.line(&format!("  call void @g1_f{entry}()"));
        } else {
            self.line(&format!("  %result = call {result} @g1_f{entry}()"));
        }
        self.line("  ret i32 0");
        self.line("}");
        self.line("");
        Ok(())
    }

    fn register_type(
        &self,
        function: &mir::Function,
        register: u32,
    ) -> Result<String, Vec<Diagnostic>> {
        let ty = function
            .register_types
            .get(register as usize)
            .copied()
            .ok_or_else(|| vec![unsupported(function, "register without a type")])?;
        self.llvm_type(ty)
    }

    fn register_runtime_type(
        &self,
        function: &mir::Function,
        register: u32,
    ) -> Result<TypeId, Vec<Diagnostic>> {
        function
            .register_types
            .get(register as usize)
            .copied()
            .ok_or_else(|| vec![unsupported(function, "register without a runtime type")])
    }

    fn runtime_type(&self, ty: TypeId) -> Result<&Type, Vec<Diagnostic>> {
        self.phases
            .artifact
            .types
            .get(ty as usize)
            .map(Type::representation)
            .ok_or_else(|| vec![backend_error(format!("missing runtime type t{ty}"))])
    }

    fn is_byte_object(&self, ty: TypeId) -> Result<bool, Vec<Diagnostic>> {
        Ok(matches!(self.runtime_type(ty)?, Type::Text | Type::Bytes))
    }

    fn type_contains_byte_object(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<bool, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(false);
        }
        let contains =
            match self.runtime_type(ty)? {
                Type::Text | Type::Bytes => true,
                Type::Tuple { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_byte_object(*field, visiting)
                        .unwrap_or(true)
                }),
                Type::Struct { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_byte_object(field.ty, visiting)
                        .unwrap_or(true)
                }),
                Type::Enum { variants, .. } => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| {
                        self.type_contains_byte_object(field.ty, visiting)
                            .unwrap_or(true)
                    }),
                _ => false,
            };
        visiting.remove(&ty);
        Ok(contains)
    }

    fn emit_retain(
        &mut self,
        ty: TypeId,
        value: &str,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        if self.is_byte_object(ty)? {
            self.line(&format!("  call void @g1_bytes_retain(ptr {value})"));
        } else if self.type_contains_byte_object(ty, &mut BTreeSet::new())? {
            return Err(vec![unsupported(
                function,
                "copying aggregates that contain Text or Bytes",
            )]);
        }
        Ok(())
    }

    fn release_byte_operands(
        &mut self,
        function: &mir::Function,
        operands: &[mir::Operand],
        loaded: &[(String, String)],
    ) -> Result<(), Vec<Diagnostic>> {
        for (operand, (_, value)) in operands.iter().zip(loaded) {
            let ty = self.register_runtime_type(function, operand.register)?;
            if self.is_byte_object(ty)? {
                self.line(&format!("  call void @g1_bytes_release(ptr {value})"));
            }
        }
        Ok(())
    }

    fn emit_byte_concat(&mut self, left: &str, right: &str) -> String {
        let usize_ty = format!("i{}", self.pointer_width());
        self.overflow_widths.insert((self.pointer_width(), "uadd"));
        let left_length_address = self.temp();
        let left_length = self.temp();
        let right_length_address = self.temp();
        let right_length = self.temp();
        let pair = self.temp();
        let length = self.temp();
        let overflow = self.temp();
        self.line(&format!(
            "  %{left_length_address} = getelementptr inbounds %g1.bytes, ptr {left}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{left_length} = load {usize_ty}, ptr %{left_length_address}"
        ));
        self.line(&format!(
            "  %{right_length_address} = getelementptr inbounds %g1.bytes, ptr {right}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{right_length} = load {usize_ty}, ptr %{right_length_address}"
        ));
        self.line(&format!(
            "  %{pair} = call {{ {usize_ty}, i1 }} @llvm.uadd.with.overflow.{usize_ty}({usize_ty} %{left_length}, {usize_ty} %{right_length})"
        ));
        self.line(&format!(
            "  %{length} = extractvalue {{ {usize_ty}, i1 }} %{pair}, 0"
        ));
        self.line(&format!(
            "  %{overflow} = extractvalue {{ {usize_ty}, i1 }} %{pair}, 1"
        ));
        self.emit_trap_if(overflow);
        let result = self.temp();
        let result_data = self.temp();
        let left_data = self.temp();
        let result_right = self.temp();
        let right_data = self.temp();
        self.line(&format!(
            "  %{result} = call ptr @g1_bytes_allocate({usize_ty} %{length})"
        ));
        self.line(&format!(
            "  %{result_data} = call ptr @g1_bytes_data(ptr %{result})"
        ));
        self.line(&format!(
            "  %{left_data} = call ptr @g1_bytes_data(ptr {left})"
        ));
        self.line(&format!(
            "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{result_data}, ptr %{left_data}, {usize_ty} %{left_length}, i1 false)"
        ));
        self.line(&format!(
            "  %{result_right} = getelementptr inbounds i8, ptr %{result_data}, {usize_ty} %{left_length}"
        ));
        self.line(&format!(
            "  %{right_data} = call ptr @g1_bytes_data(ptr {right})"
        ));
        self.line(&format!(
            "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{result_right}, ptr %{right_data}, {usize_ty} %{right_length}, i1 false)"
        ));
        format!("%{result}")
    }

    fn llvm_constant(&self, value: &Constant) -> Result<String, Vec<Diagnostic>> {
        match value {
            Constant::Text(value) => self.byte_literal(value.as_bytes()),
            Constant::Bytes(value) => self.byte_literal(value),
            _ => llvm_scalar_constant(value),
        }
    }

    fn byte_literal(&self, bytes: &[u8]) -> Result<String, Vec<Diagnostic>> {
        self.byte_literals
            .get(bytes)
            .map(|index| format!("@g1.bytes.{index}"))
            .ok_or_else(|| vec![backend_error("missing prepared Text or Bytes literal")])
    }

    fn enum_slot_words(&self, ty: TypeId, field: u32) -> Result<usize, Vec<Diagnostic>> {
        let Type::Enum { variants, .. } = self.runtime_type(ty)? else {
            return Err(vec![backend_error(format!(
                "runtime type t{ty} is not an enum"
            ))]);
        };
        let mut maximum = 0usize;
        for variant in variants {
            if let Some(field) = variant.fields.get(field as usize) {
                maximum = maximum.max(self.storage_size(field.ty, &mut BTreeSet::new())?);
            }
        }
        if maximum == 0 {
            return Err(vec![backend_error(format!(
                "enum t{ty} has no payload field {field}"
            ))]);
        }
        Ok(maximum.div_ceil(16).max(1))
    }

    /// Conservative byte size used only for enum payload slots. Slots are
    /// i128-aligned and all payload accesses carry `align 1`, so overestimating
    /// padding is ABI-safe and keeps this independent of host `size_of`.
    fn storage_size(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<usize, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Err(vec![backend_error(format!(
                "recursive by-value runtime type t{ty}"
            ))]);
        }
        let size = match self.runtime_type(ty)? {
            Type::Unit => 1,
            Type::Never => 0,
            Type::U8 | Type::I8 => 1,
            Type::U16 | Type::I16 => 2,
            Type::U32 | Type::I32 | Type::Char | Type::F32 => 4,
            Type::U64 | Type::I64 | Type::F64 => 8,
            Type::Usize | Type::Isize => usize::from(self.pointer_width() / 8),
            Type::U128 | Type::I128 => 16,
            Type::Text | Type::Bytes | Type::RefShared { .. } | Type::RefUnique { .. } => {
                usize::from(self.pointer_width() / 8)
            }
            Type::Tuple { fields, .. } => {
                let mut size = 0usize;
                for field in fields {
                    size += self.storage_size(*field, visiting)?.div_ceil(16) * 16;
                }
                size.max(1)
            }
            Type::Struct { fields, .. } => {
                let mut size = 0usize;
                for field in fields {
                    size += self.storage_size(field.ty, visiting)?.div_ceil(16) * 16;
                }
                size.max(1)
            }
            Type::Enum { variants, .. } => {
                let fields = variants
                    .iter()
                    .map(|variant| variant.fields.len())
                    .max()
                    .unwrap_or(0);
                let mut size = 16usize;
                for index in 0..fields {
                    let mut maximum = 1usize;
                    for variant in variants {
                        if let Some(field) = variant.fields.get(index) {
                            maximum = maximum.max(self.storage_size(field.ty, visiting)?);
                        }
                    }
                    size += maximum.div_ceil(16) * 16;
                }
                size
            }
            other => {
                return Err(vec![backend_error(format!(
                    "LLVM enum payload layout does not yet support {other:?}"
                ))]);
            }
        };
        visiting.remove(&ty);
        Ok(size)
    }

    fn aggregate_field_type(
        &self,
        aggregate: TypeId,
        field: u32,
    ) -> Result<TypeId, Vec<Diagnostic>> {
        let ty = self
            .phases
            .artifact
            .types
            .get(aggregate as usize)
            .ok_or_else(|| vec![backend_error(format!("missing runtime type t{aggregate}"))])?;
        match ty.representation() {
            Type::Tuple { fields, .. } => fields.get(field as usize).copied(),
            Type::Struct { fields, .. } => fields.get(field as usize).map(|field| field.ty),
            other => {
                return Err(vec![backend_error(format!(
                    "LLVM projection requires a tuple or struct, found {other:?}"
                ))]);
            }
        }
        .ok_or_else(|| {
            vec![backend_error(format!(
                "aggregate t{aggregate} has no field {field}"
            ))]
        })
    }

    fn register_is_signed(
        &self,
        function: &mir::Function,
        register: u32,
    ) -> Result<bool, Vec<Diagnostic>> {
        let ty = function
            .register_types
            .get(register as usize)
            .and_then(|ty| self.phases.artifact.types.get(*ty as usize))
            .ok_or_else(|| vec![unsupported(function, "register without a runtime type")])?;
        Ok(matches!(
            ty.representation(),
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::Isize
        ))
    }

    fn integer_type_info(&self, ty: TypeId) -> Option<(bool, u16)> {
        Some(match self.runtime_type(ty).ok()? {
            Type::U8 => (false, 8),
            Type::U16 => (false, 16),
            Type::U32 | Type::Char => (false, 32),
            Type::U64 => (false, 64),
            Type::Usize => (false, self.pointer_width()),
            Type::U128 => (false, 128),
            Type::I8 => (true, 8),
            Type::I16 => (true, 16),
            Type::I32 => (true, 32),
            Type::I64 => (true, 64),
            Type::Isize => (true, self.pointer_width()),
            Type::I128 => (true, 128),
            _ => return None,
        })
    }

    fn load_operand(
        &mut self,
        function: &mir::Function,
        operand: &mir::Operand,
    ) -> Result<String, Vec<Diagnostic>> {
        let ty = self.register_type(function, operand.register)?;
        let temporary = self.temp();
        self.line(&format!(
            "  %{temporary} = load {ty}, ptr %r{}",
            operand.register
        ));
        Ok(format!("%{temporary}"))
    }

    fn load_register(
        &mut self,
        function: &mir::Function,
        register: u32,
    ) -> Result<String, Vec<Diagnostic>> {
        self.load_operand(
            function,
            &mir::Operand {
                register,
                mode: mir::UseMode::Copy,
            },
        )
    }

    fn llvm_type(&self, id: TypeId) -> Result<String, Vec<Diagnostic>> {
        let Some(ty) = self.phases.artifact.types.get(id as usize) else {
            return Err(vec![backend_error(format!("missing runtime type t{id}"))]);
        };
        Ok(match ty.representation() {
            Type::Unit => "i8".into(),
            Type::Never => "void".into(),
            Type::U8 | Type::I8 => "i8".into(),
            Type::U16 | Type::I16 => "i16".into(),
            Type::U32 | Type::I32 | Type::Char => "i32".into(),
            Type::U64 | Type::I64 => "i64".into(),
            Type::Usize | Type::Isize => format!("i{}", self.pointer_width()),
            Type::U128 | Type::I128 => "i128".into(),
            Type::F32 => "float".into(),
            Type::F64 => "double".into(),
            Type::Text | Type::Bytes | Type::RefShared { .. } | Type::RefUnique { .. } => {
                "ptr".into()
            }
            Type::Tuple { fields, .. } => format!(
                "{{ {} }}",
                fields
                    .iter()
                    .map(|field| self.llvm_type(*field))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ")
            ),
            Type::Struct { fields, .. } => format!(
                "{{ {} }}",
                fields
                    .iter()
                    .map(|field| self.llvm_type(field.ty))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ")
            ),
            Type::Enum { variants, .. } => {
                let fields = variants
                    .iter()
                    .map(|variant| variant.fields.len())
                    .max()
                    .unwrap_or(0);
                let slots = (0..fields)
                    .map(|field| {
                        self.enum_slot_words(id, field as u32)
                            .map(|words| format!("[{words} x i128]"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if slots.is_empty() {
                    "{ i32 }".into()
                } else {
                    format!("{{ i32, {} }}", slots.join(", "))
                }
            }
            other => {
                return Err(vec![backend_error(format!(
                    "LLVM scalar slice does not yet lower runtime type {other:?}"
                ))]);
            }
        })
    }

    fn llvm_return_type(&self, id: TypeId) -> Result<String, Vec<Diagnostic>> {
        let Some(ty) = self.phases.artifact.types.get(id as usize) else {
            return Err(vec![backend_error(format!("missing runtime type t{id}"))]);
        };
        if matches!(ty.representation(), Type::Unit | Type::Never) {
            Ok("void".into())
        } else {
            self.llvm_type(id)
        }
    }

    fn temp(&mut self) -> u32 {
        let temporary = self.temporary;
        self.temporary += 1;
        temporary
    }

    fn line(&mut self, line: &str) {
        self.output.push_str(line);
        self.output.push('\n');
    }

    fn emit_trap_if(&mut self, condition: u32) {
        let trap = self.temp();
        let continuation = self.temp();
        self.line(&format!(
            "  br i1 %{condition}, label %trap{trap}, label %cont{continuation}"
        ));
        self.line(&format!("trap{trap}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        self.line(&format!("cont{continuation}:"));
    }

    fn pointer_width(&self) -> u16 {
        let triple = self.options.target_triple.as_str();
        if triple.starts_with("i386")
            || triple.starts_with("i486")
            || triple.starts_with("i586")
            || triple.starts_with("i686")
            || triple.starts_with("armv7")
            || triple.starts_with("thumbv7")
            || triple.starts_with("wasm32")
        {
            32
        } else {
            64
        }
    }
}

fn integer_width(ty: &str) -> Option<u16> {
    ty.strip_prefix('i')?.parse().ok()
}

fn signed_minimum(width: u16) -> String {
    if width == 128 {
        i128::MIN.to_string()
    } else {
        (-(1_i128 << (width - 1))).to_string()
    }
}

fn signed_maximum(width: u16) -> String {
    if width == 128 {
        i128::MAX.to_string()
    } else {
        ((1_u128 << (width - 1)) - 1).to_string()
    }
}

fn unsigned_maximum(width: u16) -> String {
    if width == 128 {
        u128::MAX.to_string()
    } else {
        ((1_u128 << width) - 1).to_string()
    }
}

fn llvm_float_power(
    llvm_type: &str,
    exponent: i32,
    negative: bool,
) -> Result<String, Vec<Diagnostic>> {
    let mut value = 2_f64.powi(exponent);
    if negative {
        value = -value;
    }
    Ok(match llvm_type {
        "float" => format!("0x{:016X}", f64::from(value as f32).to_bits()),
        "double" => format!("0x{:016X}", value.to_bits()),
        _ => {
            return Err(vec![backend_error(format!(
                "checked float conversion requires float or double, found {llvm_type}"
            ))]);
        }
    })
}

fn binary_operands(loaded: &[(String, String)]) -> Option<(&str, &str, &str)> {
    let left = loaded.first()?;
    let right = loaded.get(1)?;
    Some((left.0.as_str(), left.1.as_str(), right.1.as_str()))
}

fn llvm_scalar_constant(value: &Constant) -> Result<String, Vec<Diagnostic>> {
    Ok(match value {
        Constant::Unit => "0".into(),
        Constant::U8(value) => value.to_string(),
        Constant::U16(value) => value.to_string(),
        Constant::U32(value) => value.to_string(),
        Constant::U64(value) | Constant::Usize(value) => value.to_string(),
        Constant::U128(value) => value.to_string(),
        Constant::I8(value) => value.to_string(),
        Constant::I16(value) => value.to_string(),
        Constant::I32(value) => value.to_string(),
        Constant::I64(value) | Constant::Isize(value) => value.to_string(),
        Constant::I128(value) => value.to_string(),
        // LLVM's hexadecimal spelling for `float` constants uses the
        // corresponding exactly-representable IEEE-754 double bit pattern.
        Constant::F32(value) => format!("0x{:016X}", f64::from(*value).to_bits()),
        Constant::F64(value) => format!("0x{:016X}", value.to_bits()),
        Constant::Char(value) => u32::from(*value).to_string(),
        Constant::Text(_) | Constant::Bytes(_) => unreachable!("byte literals use runtime globals"),
    })
}

fn unsupported(function: &mir::Function, feature: impl std::fmt::Display) -> Diagnostic {
    backend_error(format!(
        "LLVM backend does not yet support {feature} in `{}`",
        function.name
    ))
}

fn backend_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic::plain(message).with_code("G1LLVM001").with_help(
        "use the bytecode backend, or lower this program within the supported LLVM scalar slice",
    )
}

fn llvm_string(value: &str) -> String {
    value.replace('\\', "\\5C").replace('"', "\\22")
}

fn llvm_bytes(value: &[u8]) -> String {
    value.iter().map(|byte| format!("\\{byte:02X}")).collect()
}
