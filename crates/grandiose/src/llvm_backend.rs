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
    compiler_traits::HostImportRole,
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
    uses_array_runtime: bool,
    uses_callable_runtime: bool,
    host_imports: BTreeSet<HostImportRole>,
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
            uses_array_runtime: false,
            uses_callable_runtime: false,
            host_imports: BTreeSet::new(),
        }
    }

    fn emit(mut self) -> Result<LlvmModule, Vec<Diagnostic>> {
        let reachable = self.reachable_functions()?;
        self.prepare_runtime(&reachable)?;
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
        if self.uses_array_runtime {
            self.emit_array_runtime();
        }
        if self.uses_callable_runtime {
            self.emit_callable_runtime();
        }
        self.emit_host_import_declarations();
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
            for ty in function
                .register_types
                .iter()
                .chain(function.params.iter())
                .chain(std::iter::once(&function.result))
            {
                self.collect_drop_glue_functions(*ty, &mut BTreeSet::new(), &mut pending)?;
            }
            for block in &function.blocks {
                for instruction in &block.statements {
                    if let InstructionKind::MakeCallable {
                        function: target, ..
                    } = &instruction.kind
                    {
                        pending.push(*target as usize);
                    }
                }
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

    fn collect_drop_glue_functions(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
        pending: &mut Vec<usize>,
    ) -> Result<(), Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(());
        }
        if let Some(glue) = self
            .phases
            .artifact
            .drop_glue
            .iter()
            .find(|glue| glue.ty == ty)
        {
            pending.push(glue.function as usize);
        }
        match self.runtime_type(ty)? {
            Type::Array { element } => {
                self.collect_drop_glue_functions(*element, visiting, pending)?;
            }
            Type::Callable { capture_type, .. }
            | Type::Handler { capture_type, .. }
            | Type::BindingPack {
                payload_type: capture_type,
                ..
            } => {
                self.collect_drop_glue_functions(*capture_type, visiting, pending)?;
            }
            Type::Tuple { fields, .. } => {
                for field in fields {
                    self.collect_drop_glue_functions(*field, visiting, pending)?;
                }
            }
            Type::Struct { fields, .. } => {
                for field in fields {
                    self.collect_drop_glue_functions(field.ty, visiting, pending)?;
                }
            }
            Type::Enum { variants, .. } => {
                for field in variants.iter().flat_map(|variant| &variant.fields) {
                    self.collect_drop_glue_functions(field.ty, visiting, pending)?;
                }
            }
            _ => {}
        }
        visiting.remove(&ty);
        Ok(())
    }

    fn prepare_runtime(&mut self, reachable: &[usize]) -> Result<(), Vec<Diagnostic>> {
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
                self.uses_array_runtime |= self.type_contains_array(ty, &mut BTreeSet::new())?;
                self.uses_callable_runtime |=
                    self.type_contains_callable(ty, &mut BTreeSet::new())?;
            }
            for block in &function.blocks {
                if let Terminator::HostCall { import, .. } = &block.terminator {
                    self.host_imports.insert(*import);
                }
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

    fn emit_host_import_declarations(&mut self) {
        let imports = self.host_imports.iter().copied().collect::<Vec<_>>();
        for import in imports {
            match import {
                HostImportRole::ProcessArgsGet => {
                    self.line("declare ptr @g1_host_process_args_get()");
                }
                HostImportRole::FsRead => {
                    self.line("declare ptr @g1_host_fs_read(ptr)");
                }
                HostImportRole::FsWrite => {
                    self.line("declare void @g1_host_fs_write(ptr, ptr)");
                }
                HostImportRole::DiagnosticWrite => {
                    self.line("declare void @g1_host_diagnostic_write(ptr)");
                }
            }
        }
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

    fn emit_array_runtime(&mut self) {
        let usize_ty = format!("i{}", self.pointer_width());
        self.overflow_widths.insert((self.pointer_width(), "umul"));
        self.overflow_widths.insert((self.pointer_width(), "uadd"));
        self.line(&format!(
            "%g1.array = type {{ {usize_ty}, {usize_ty}, {usize_ty}, ptr, ptr }}"
        ));
        if !self.uses_byte_runtime {
            self.line(&format!("declare ptr @malloc({usize_ty})"));
            self.line("declare void @free(ptr)");
        }
        self.line(&format!("declare ptr @realloc(ptr, {usize_ty})"));
        self.line(&format!(
            "declare void @llvm.memset.p0.{usize_ty}(ptr nocapture writeonly, i8, {usize_ty}, i1 immarg)"
        ));
        self.line("");
        self.line(&format!(
            "define internal ptr @g1_array_allocate({usize_ty} %capacity, {usize_ty} %element.size) {{"
        ));
        self.line("entry:");
        self.line(&format!(
            "  %header.end = getelementptr %g1.array, ptr null, {usize_ty} 1"
        ));
        self.line(&format!(
            "  %header.size = ptrtoint ptr %header.end to {usize_ty}"
        ));
        self.line(&format!(
            "  %array = call ptr @malloc({usize_ty} %header.size)"
        ));
        self.line("  %length.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 0");
        self.line(&format!("  store {usize_ty} 0, ptr %length.address"));
        self.line(
            "  %capacity.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 1",
        );
        self.line(&format!(
            "  store {usize_ty} %capacity, ptr %capacity.address"
        ));
        self.line(
            "  %element.size.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 2",
        );
        self.line(&format!(
            "  store {usize_ty} %element.size, ptr %element.size.address"
        ));
        self.line(&format!("  %empty = icmp eq {usize_ty} %capacity, 0"));
        self.line("  br i1 %empty, label %zero, label %allocate");
        self.line("zero:");
        self.line("  br label %finish");
        self.line("allocate:");
        self.line(&format!(
            "  %size.pair = call {{ {usize_ty}, i1 }} @llvm.umul.with.overflow.{usize_ty}({usize_ty} %capacity, {usize_ty} %element.size)"
        ));
        self.line(&format!(
            "  %data.size = extractvalue {{ {usize_ty}, i1 }} %size.pair, 0"
        ));
        self.line(&format!(
            "  %size.overflow = extractvalue {{ {usize_ty}, i1 }} %size.pair, 1"
        ));
        self.line("  br i1 %size.overflow, label %trap, label %allocate.storage");
        self.line("trap:");
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        self.line("allocate.storage:");
        self.line(&format!(
            "  %data = call ptr @malloc({usize_ty} %data.size)"
        ));
        self.line(&format!(
            "  %initialized = call ptr @malloc({usize_ty} %capacity)"
        ));
        self.line(&format!(
            "  call void @llvm.memset.p0.{usize_ty}(ptr %initialized, i8 0, {usize_ty} %capacity, i1 false)"
        ));
        self.line("  br label %finish");
        self.line("finish:");
        self.line("  %final.data = phi ptr [ null, %zero ], [ %data, %allocate.storage ]");
        self.line(
            "  %final.initialized = phi ptr [ null, %zero ], [ %initialized, %allocate.storage ]",
        );
        self.line("  %data.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 3");
        self.line("  store ptr %final.data, ptr %data.address");
        self.line(
            "  %initialized.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 4",
        );
        self.line("  store ptr %final.initialized, ptr %initialized.address");
        self.line("  ret ptr %array");
        self.line("}");
        self.line("");
        self.line(&format!(
            "define internal void @g1_array_grow(ptr %array, {usize_ty} %required) {{"
        ));
        self.line("entry:");
        self.line(
            "  %capacity.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 1",
        );
        self.line(&format!(
            "  %capacity = load {usize_ty}, ptr %capacity.address"
        ));
        self.line(&format!(
            "  %enough = icmp uge {usize_ty} %capacity, %required"
        ));
        self.line("  br i1 %enough, label %return, label %grow");
        self.line("grow:");
        self.line(&format!(
            "  %double.pair = call {{ {usize_ty}, i1 }} @llvm.uadd.with.overflow.{usize_ty}({usize_ty} %capacity, {usize_ty} %capacity)"
        ));
        self.line(&format!(
            "  %doubled = extractvalue {{ {usize_ty}, i1 }} %double.pair, 0"
        ));
        self.line(&format!(
            "  %double.overflow = extractvalue {{ {usize_ty}, i1 }} %double.pair, 1"
        ));
        self.line(&format!("  %minimum = icmp ult {usize_ty} %doubled, 1"));
        self.line(&format!(
            "  %at.least.one = select i1 %minimum, {usize_ty} 1, {usize_ty} %doubled"
        ));
        self.line(&format!(
            "  %below.required = icmp ult {usize_ty} %at.least.one, %required"
        ));
        self.line(&format!(
            "  %grown = select i1 %below.required, {usize_ty} %required, {usize_ty} %at.least.one"
        ));
        self.line(&format!(
            "  %new.capacity = select i1 %double.overflow, {usize_ty} %required, {usize_ty} %grown"
        ));
        self.line(
            "  %element.size.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 2",
        );
        self.line(&format!(
            "  %element.size = load {usize_ty}, ptr %element.size.address"
        ));
        self.line(&format!(
            "  %size.pair = call {{ {usize_ty}, i1 }} @llvm.umul.with.overflow.{usize_ty}({usize_ty} %new.capacity, {usize_ty} %element.size)"
        ));
        self.line(&format!(
            "  %data.size = extractvalue {{ {usize_ty}, i1 }} %size.pair, 0"
        ));
        self.line(&format!(
            "  %size.overflow = extractvalue {{ {usize_ty}, i1 }} %size.pair, 1"
        ));
        self.line("  br i1 %size.overflow, label %trap, label %resize");
        self.line("trap:");
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        self.line("resize:");
        self.line("  %data.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 3");
        self.line("  %data = load ptr, ptr %data.address");
        self.line(&format!(
            "  %new.data = call ptr @realloc(ptr %data, {usize_ty} %data.size)"
        ));
        self.line("  store ptr %new.data, ptr %data.address");
        self.line(
            "  %initialized.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 4",
        );
        self.line("  %initialized = load ptr, ptr %initialized.address");
        self.line(&format!(
            "  %new.initialized = call ptr @realloc(ptr %initialized, {usize_ty} %new.capacity)"
        ));
        self.line(&format!(
            "  %added = sub {usize_ty} %new.capacity, %capacity"
        ));
        self.line(&format!(
            "  %new.initialized.start = getelementptr inbounds i8, ptr %new.initialized, {usize_ty} %capacity"
        ));
        self.line(&format!(
            "  call void @llvm.memset.p0.{usize_ty}(ptr %new.initialized.start, i8 0, {usize_ty} %added, i1 false)"
        ));
        self.line("  store ptr %new.initialized, ptr %initialized.address");
        self.line(&format!(
            "  store {usize_ty} %new.capacity, ptr %capacity.address"
        ));
        self.line("  br label %return");
        self.line("return:");
        self.line("  ret void");
        self.line("}");
        self.line("");
        self.line("define internal void @g1_array_free(ptr %array) {");
        self.line("entry:");
        self.line("  %data.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 3");
        self.line("  %data = load ptr, ptr %data.address");
        self.line("  call void @free(ptr %data)");
        self.line(
            "  %initialized.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 4",
        );
        self.line("  %initialized = load ptr, ptr %initialized.address");
        self.line("  call void @free(ptr %initialized)");
        self.line("  call void @free(ptr %array)");
        self.line("  ret void");
        self.line("}");
    }

    fn emit_callable_runtime(&mut self) {
        let usize_ty = format!("i{}", self.pointer_width());
        self.line("%g1.callable = type { i64, ptr, ptr }");
        if !self.uses_byte_runtime && !self.uses_array_runtime {
            self.line(&format!("declare ptr @malloc({usize_ty})"));
            self.line("declare void @free(ptr)");
        }
    }

    fn emit_make_callable(
        &mut self,
        caller: &mir::Function,
        callable_type: TypeId,
        target: usize,
        captures: &[mir::Operand],
    ) -> Result<String, Vec<Diagnostic>> {
        let Type::Callable {
            capture_type,
            receiver_mode,
            ..
        } = self.runtime_type(callable_type)?.clone()
        else {
            return Err(vec![unsupported(
                caller,
                "MakeCallable with a non-callable runtime type",
            )]);
        };
        let target_function = self
            .phases
            .mir
            .functions
            .get(target)
            .ok_or_else(|| vec![unsupported(caller, "MakeCallable target is missing")])?;
        if target_function.receiver_mode != Some(receiver_mode) {
            return Err(vec![unsupported(
                caller,
                "MakeCallable receiver mode does not match its target",
            )]);
        }

        let capture_ty = self.llvm_type(capture_type)?;
        let capture_value = match self.runtime_type(capture_type)? {
            Type::Unit => {
                if !captures.is_empty() {
                    return Err(vec![unsupported(
                        caller,
                        "captureless callable with capture operands",
                    )]);
                }
                "0".to_owned()
            }
            Type::Tuple { fields, .. } => {
                if fields.len() != captures.len() {
                    return Err(vec![unsupported(caller, "callable capture count mismatch")]);
                }
                let fields = fields.clone();
                self.emit_capture_aggregate(caller, &capture_ty, &fields, captures)?
            }
            Type::Struct { fields, .. } => {
                if fields.len() != captures.len() {
                    return Err(vec![unsupported(caller, "callable capture count mismatch")]);
                }
                let fields = fields.iter().map(|field| field.ty).collect::<Vec<_>>();
                self.emit_capture_aggregate(caller, &capture_ty, &fields, captures)?
            }
            other => {
                return Err(vec![unsupported(
                    caller,
                    format!("callable capture layout {other:?}"),
                )]);
            }
        };

        let usize_ty = format!("i{}", self.pointer_width());
        let callable_end = self.temp();
        self.line(&format!(
            "  %{callable_end} = getelementptr %g1.callable, ptr null, {usize_ty} 1"
        ));
        let callable_size = self.temp();
        self.line(&format!(
            "  %{callable_size} = ptrtoint ptr %{callable_end} to {usize_ty}"
        ));
        let callable = self.temp();
        self.line(&format!(
            "  %{callable} = call ptr @malloc({usize_ty} %{callable_size})"
        ));
        let capture_size = self.emit_array_element_size(&capture_ty);
        let capture = self.temp();
        self.line(&format!(
            "  %{capture} = call ptr @malloc({usize_ty} {capture_size})"
        ));
        self.line(&format!(
            "  store {capture_ty} {capture_value}, ptr %{capture}"
        ));
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{count_address}"));
        let function_address = self.temp();
        self.line(&format!(
            "  %{function_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  store ptr @g1_f{target}, ptr %{function_address}"
        ));
        let capture_address = self.temp();
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 2"
        ));
        self.line(&format!("  store ptr %{capture}, ptr %{capture_address}"));
        Ok(format!("%{callable}"))
    }

    fn emit_capture_aggregate(
        &mut self,
        caller: &mir::Function,
        aggregate_ty: &str,
        fields: &[TypeId],
        captures: &[mir::Operand],
    ) -> Result<String, Vec<Diagnostic>> {
        let mut aggregate = "poison".to_owned();
        for (index, (expected, capture)) in fields.iter().zip(captures).enumerate() {
            let actual = self.register_runtime_type(caller, capture.register)?;
            if actual != *expected {
                return Err(vec![unsupported(caller, "callable capture type mismatch")]);
            }
            let field_ty = self.llvm_type(*expected)?;
            let value = self.load_operand(caller, capture)?;
            if capture.mode == mir::UseMode::Copy {
                self.emit_retain(*expected, &value, caller)?;
            }
            let inserted = self.temp();
            self.line(&format!(
                "  %{inserted} = insertvalue {aggregate_ty} {aggregate}, {field_ty} {value}, {index}"
            ));
            aggregate = format!("%{inserted}");
        }
        Ok(aggregate)
    }

    fn emit_function(&mut self, index: usize) -> Result<(), Vec<Diagnostic>> {
        let function = &self.phases.mir.functions[index];
        if !function.outward_protocols.is_empty() {
            return Err(vec![unsupported(function, "outward effects")]);
        }
        let result = self.llvm_return_type(function.result)?;
        let mut params = function
            .params
            .iter()
            .enumerate()
            .map(|(index, ty)| Ok(format!("{} %arg{index}", self.llvm_type(*ty)?)))
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        if function.receiver_mode.is_some() {
            params.insert(
                0,
                format!("{} %receiver", self.llvm_type(function.receiver_type)?),
            );
        }
        let params = params.join(", ");
        self.line(&format!("define {} @g1_f{index}({params}) {{", result));
        self.line("entry.allocas:");
        for (register, ty) in function.register_types.iter().enumerate() {
            self.line(&format!("  %r{register} = alloca {}", self.llvm_type(*ty)?));
        }
        if function.receiver_mode.is_some() {
            self.line(&format!(
                "  store {} %receiver, ptr %r0",
                self.llvm_type(function.receiver_type)?
            ));
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
                let source = self.register_runtime_type(function, *src)?;
                let (aggregate, base) = match self.runtime_type(source)? {
                    Type::RefShared { referent } | Type::RefUnique { referent } => {
                        (*referent, self.load_register(function, *src)?)
                    }
                    _ => (source, format!("%r{src}")),
                };
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
                    "  %{address} = getelementptr inbounds {aggregate_ty}, ptr {base}, i32 0, i32 {llvm_field}"
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
                let source_id = self.register_runtime_type(function, src.register)?;
                let (aggregate_id, through_reference) = match self.runtime_type(source_id)? {
                    Type::RefShared { referent } | Type::RefUnique { referent } => {
                        (*referent, true)
                    }
                    _ => (source_id, false),
                };
                let aggregate_ty = self.llvm_type(aggregate_id)?;
                let aggregate = self.load_operand(function, src)?;
                let field_ty = self.register_type(function, *dst)?;
                let value = if matches!(self.runtime_type(aggregate_id)?, Type::Enum { .. }) {
                    let words = self.enum_slot_words(aggregate_id, *field)?;
                    let slot_ty = format!("[{words} x i128]");
                    let packed = if through_reference {
                        let address = self.temp();
                        self.line(&format!(
                            "  %{address} = getelementptr inbounds {aggregate_ty}, ptr {aggregate}, i32 0, i32 {}",
                            field + 1
                        ));
                        let packed = self.temp();
                        self.line(&format!("  %{packed} = load {slot_ty}, ptr %{address}"));
                        packed
                    } else {
                        let packed = self.temp();
                        self.line(&format!(
                            "  %{packed} = extractvalue {aggregate_ty} {aggregate}, {}",
                            field + 1
                        ));
                        packed
                    };
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
                    if through_reference {
                        let address = self.temp();
                        self.line(&format!(
                            "  %{address} = getelementptr inbounds {aggregate_ty}, ptr {aggregate}, i32 0, i32 {field}"
                        ));
                        let value = self.temp();
                        self.line(&format!("  %{value} = load {field_ty}, ptr %{address}"));
                        value
                    } else {
                        let value = self.temp();
                        self.line(&format!(
                            "  %{value} = extractvalue {aggregate_ty} {aggregate}, {field}"
                        ));
                        value
                    }
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
            InstructionKind::MakeCallable {
                dst,
                callable_type,
                function: target,
                captures,
            } => {
                let callable =
                    self.emit_make_callable(function, *callable_type, *target as usize, captures)?;
                self.line(&format!("  store ptr {callable}, ptr %r{dst}"));
            }
            InstructionKind::MakeBindingPack {
                dst,
                binding_type,
                payloads,
            } => {
                let Type::BindingPack { payload_type, .. } =
                    self.runtime_type(*binding_type)?.clone()
                else {
                    return Err(vec![unsupported(
                        function,
                        "MakeBindingPack with a non-binding runtime type",
                    )]);
                };
                let aggregate_ty = self.llvm_type(payload_type)?;
                let fields = match self.runtime_type(payload_type)? {
                    Type::Tuple { fields, .. } => fields.clone(),
                    Type::Struct { fields, .. } => fields.iter().map(|field| field.ty).collect(),
                    other => {
                        return Err(vec![unsupported(
                            function,
                            format!("binding payload layout {other:?}"),
                        )]);
                    }
                };
                if fields.len() != payloads.len() {
                    return Err(vec![unsupported(
                        function,
                        "binding payload count mismatch",
                    )]);
                }
                let value =
                    self.emit_capture_aggregate(function, &aggregate_ty, &fields, payloads)?;
                self.line(&format!("  store {aggregate_ty} {value}, ptr %r{dst}"));
            }
            InstructionKind::Drop { owner } => {
                let ty = self.register_runtime_type(function, owner.register)?;
                let value = self.load_operand(function, owner)?;
                self.emit_destroy(ty, &value, function)?;
            }
            InstructionKind::EndBorrow { .. }
            | InstructionKind::Deconstruct { .. }
            | InstructionKind::LabelPush { .. }
            | InstructionKind::LabelPop { .. } => {}
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
            Primitive::BytesFromArrayMove => {
                let Some((_, array)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed Array-to-Bytes conversion",
                    )]);
                };
                let array_ty = self.register_runtime_type(function, args[0].register)?;
                let element = self.array_element(array_ty)?;
                if !matches!(self.runtime_type(element)?, Type::U8) {
                    return Err(vec![unsupported(
                        function,
                        "Array-to-Bytes conversion with non-u8 elements",
                    )]);
                }
                let usize_ty = format!("i{}", self.pointer_width());
                let length_address = self.temp();
                let length = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.emit_array_dense_check(array, &format!("%{length}"), &usize_ty);
                let bytes = self.temp();
                let bytes_data = self.temp();
                let array_data_address = self.temp();
                let array_data = self.temp();
                self.line(&format!(
                    "  %{bytes} = call ptr @g1_bytes_allocate({usize_ty} %{length})"
                ));
                self.line(&format!(
                    "  %{bytes_data} = call ptr @g1_bytes_data(ptr %{bytes})"
                ));
                self.line(&format!(
                    "  %{array_data_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 3"
                ));
                self.line(&format!(
                    "  %{array_data} = load ptr, ptr %{array_data_address}"
                ));
                self.line(&format!(
                    "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{bytes_data}, ptr %{array_data}, {usize_ty} %{length}, i1 false)"
                ));
                self.line(&format!("  call void @g1_array_free(ptr {array})"));
                format!("%{bytes}")
            }
            Primitive::BytesToArray => {
                let Some((_, bytes)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed Bytes-to-Array conversion",
                    )]);
                };
                let array_ty = self.register_runtime_type(function, dst)?;
                let element = self.array_element(array_ty)?;
                if !matches!(self.runtime_type(element)?, Type::U8) {
                    return Err(vec![unsupported(
                        function,
                        "Bytes-to-Array conversion with non-u8 elements",
                    )]);
                }
                let usize_ty = format!("i{}", self.pointer_width());
                let length_address = self.temp();
                let length = self.temp();
                let array = self.temp();
                let array_length_address = self.temp();
                let bytes_data = self.temp();
                let array_data_address = self.temp();
                let array_data = self.temp();
                let initialized_address = self.temp();
                let initialized = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.bytes, ptr {bytes}, i32 0, i32 1"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{array} = call ptr @g1_array_allocate({usize_ty} %{length}, {usize_ty} 1)"
                ));
                self.line(&format!(
                    "  %{array_length_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  store {usize_ty} %{length}, ptr %{array_length_address}"
                ));
                self.line(&format!(
                    "  %{bytes_data} = call ptr @g1_bytes_data(ptr {bytes})"
                ));
                self.line(&format!(
                    "  %{array_data_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 3"
                ));
                self.line(&format!(
                    "  %{array_data} = load ptr, ptr %{array_data_address}"
                ));
                self.line(&format!(
                    "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{array_data}, ptr %{bytes_data}, {usize_ty} %{length}, i1 false)"
                ));
                self.line(&format!(
                    "  %{initialized_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 4"
                ));
                self.line(&format!(
                    "  %{initialized} = load ptr, ptr %{initialized_address}"
                ));
                self.line(&format!(
                    "  call void @llvm.memset.p0.{usize_ty}(ptr %{initialized}, i8 1, {usize_ty} %{length}, i1 false)"
                ));
                self.line(&format!("  call void @g1_bytes_release(ptr {bytes})"));
                format!("%{array}")
            }
            Primitive::ArrayEmpty => {
                let array_ty = self.register_runtime_type(function, dst)?;
                let element = self.array_element(array_ty)?;
                self.ensure_plain_array_element(element, function)?;
                let element_ty = self.llvm_type(element)?;
                let element_size = self.emit_array_element_size(&element_ty);
                let usize_ty = format!("i{}", self.pointer_width());
                let array = self.temp();
                self.line(&format!(
                    "  %{array} = call ptr @g1_array_allocate({usize_ty} 0, {usize_ty} {element_size})"
                ));
                format!("%{array}")
            }
            Primitive::ArrayNew => {
                let Some((length_ty, length)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array allocation")]);
                };
                let Some((fill_ty, fill)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array allocation")]);
                };
                let array_ty = self.register_runtime_type(function, dst)?;
                let element = self.array_element(array_ty)?;
                self.ensure_plain_array_element(element, function)?;
                let expected = self.llvm_type(element)?;
                if &expected != fill_ty {
                    return Err(vec![unsupported(
                        function,
                        "Array fill value has the wrong LLVM type",
                    )]);
                }
                let element_size = self.emit_array_element_size(fill_ty);
                let array = self.temp();
                self.line(&format!(
                    "  %{array} = call ptr @g1_array_allocate({length_ty} {length}, {length_ty} {element_size})"
                ));
                let length_address = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  store {length_ty} {length}, ptr %{length_address}"
                ));
                let empty = self.temp();
                let loop_id = self.temp();
                let index_address = self.temp();
                self.line(&format!("  %{empty} = icmp eq {length_ty} {length}, 0"));
                self.line(&format!("  %{index_address} = alloca {length_ty}"));
                self.line(&format!("  store {length_ty} 0, ptr %{index_address}"));
                self.line(&format!(
                    "  br i1 %{empty}, label %array.fill.done{loop_id}, label %array.fill{loop_id}"
                ));
                self.line(&format!("array.fill{loop_id}:"));
                let index = self.temp();
                self.line(&format!(
                    "  %{index} = load {length_ty}, ptr %{index_address}"
                ));
                let data_address = self.temp();
                let data = self.temp();
                let slot = self.temp();
                let initialized_address = self.temp();
                let initialized = self.temp();
                let initialized_slot = self.temp();
                self.line(&format!(
                    "  %{data_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 3"
                ));
                self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
                self.line(&format!(
                    "  %{slot} = getelementptr inbounds {fill_ty}, ptr %{data}, {length_ty} %{index}"
                ));
                self.emit_retain(element, fill, function)?;
                self.line(&format!("  store {fill_ty} {fill}, ptr %{slot}"));
                self.line(&format!(
                    "  %{initialized_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 4"
                ));
                self.line(&format!(
                    "  %{initialized} = load ptr, ptr %{initialized_address}"
                ));
                self.line(&format!(
                    "  %{initialized_slot} = getelementptr inbounds i8, ptr %{initialized}, {length_ty} %{index}"
                ));
                self.line(&format!("  store i8 1, ptr %{initialized_slot}"));
                let next = self.temp();
                let more = self.temp();
                self.line(&format!("  %{next} = add {length_ty} %{index}, 1"));
                self.line(&format!(
                    "  store {length_ty} %{next}, ptr %{index_address}"
                ));
                self.line(&format!(
                    "  %{more} = icmp ult {length_ty} %{next}, {length}"
                ));
                self.line(&format!(
                    "  br i1 %{more}, label %array.fill{loop_id}, label %array.fill.done{loop_id}"
                ));
                self.line(&format!("array.fill.done{loop_id}:"));
                self.emit_destroy(element, fill, function)?;
                format!("%{array}")
            }
            Primitive::ArrayLen | Primitive::ArrayCapacity => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed Array metadata access",
                    )]);
                };
                self.referenced_array_element(function, args[0].register)?;
                let array = self.emit_array_from_reference(reference);
                let address = self.temp();
                let value = self.temp();
                let field = if primitive == Primitive::ArrayLen {
                    0
                } else {
                    1
                };
                self.line(&format!(
                    "  %{address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 {field}"
                ));
                self.line(&format!("  %{value} = load {dst_ty}, ptr %{address}"));
                format!("%{value}")
            }
            Primitive::ArrayGetCopy | Primitive::ArrayGetMove => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array access")]);
                };
                let Some((index_ty, index)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array access")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                if element_ty != dst_ty {
                    return Err(vec![unsupported(function, "Array element type mismatch")]);
                }
                let array = self.emit_array_from_reference(reference);
                let (slot, initialized) =
                    self.emit_checked_array_slot(&array, index_ty, index, &element_ty, true);
                let value = self.temp();
                self.line(&format!("  %{value} = load {element_ty}, ptr {slot}"));
                if primitive == Primitive::ArrayGetCopy {
                    self.emit_retain(element, &format!("%{value}"), function)?;
                } else {
                    self.line(&format!("  store i8 0, ptr {initialized}"));
                }
                format!("%{value}")
            }
            Primitive::ArrayGetBorrowShared | Primitive::ArrayGetBorrowUnique => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array borrow")]);
                };
                let Some((index_ty, index)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array borrow")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                let array = self.emit_array_from_reference(reference);
                let (slot, _) =
                    self.emit_checked_array_slot(&array, index_ty, index, &element_ty, true);
                slot
            }
            Primitive::ArraySetMove => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array store")]);
                };
                let Some((index_ty, index)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array store")]);
                };
                let Some((value_ty, value)) = loaded.get(2) else {
                    return Err(vec![unsupported(function, "malformed Array store")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                if &element_ty != value_ty {
                    return Err(vec![unsupported(
                        function,
                        "Array stored value type mismatch",
                    )]);
                }
                let array = self.emit_array_from_reference(reference);
                let (slot, initialized) =
                    self.emit_checked_array_slot(&array, index_ty, index, &element_ty, false);
                self.line(&format!("  store {element_ty} {value}, ptr {slot}"));
                self.line(&format!("  store i8 1, ptr {initialized}"));
                "0".to_owned()
            }
            Primitive::ArrayPushMove => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array push")]);
                };
                let Some((value_ty, value)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array push")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                if &element_ty != value_ty {
                    return Err(vec![unsupported(
                        function,
                        "Array pushed value type mismatch",
                    )]);
                }
                let usize_ty = format!("i{}", self.pointer_width());
                self.overflow_widths.insert((self.pointer_width(), "uadd"));
                let array = self.emit_array_from_reference(reference);
                let length_address = self.temp();
                let length = self.temp();
                let pair = self.temp();
                let required = self.temp();
                let overflow = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{pair} = call {{ {usize_ty}, i1 }} @llvm.uadd.with.overflow.{usize_ty}({usize_ty} %{length}, {usize_ty} 1)"
                ));
                self.line(&format!(
                    "  %{required} = extractvalue {{ {usize_ty}, i1 }} %{pair}, 0"
                ));
                self.line(&format!(
                    "  %{overflow} = extractvalue {{ {usize_ty}, i1 }} %{pair}, 1"
                ));
                self.emit_trap_if(overflow);
                self.line(&format!(
                    "  call void @g1_array_grow(ptr {array}, {usize_ty} %{required})"
                ));
                let data_address = self.temp();
                let data = self.temp();
                let slot = self.temp();
                let initialized_address = self.temp();
                let initialized = self.temp();
                let initialized_slot = self.temp();
                self.line(&format!(
                    "  %{data_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 3"
                ));
                self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
                self.line(&format!(
                    "  %{slot} = getelementptr inbounds {element_ty}, ptr %{data}, {usize_ty} %{length}"
                ));
                self.line(&format!("  store {element_ty} {value}, ptr %{slot}"));
                self.line(&format!(
                    "  %{initialized_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
                ));
                self.line(&format!(
                    "  %{initialized} = load ptr, ptr %{initialized_address}"
                ));
                self.line(&format!(
                    "  %{initialized_slot} = getelementptr inbounds i8, ptr %{initialized}, {usize_ty} %{length}"
                ));
                self.line(&format!("  store i8 1, ptr %{initialized_slot}"));
                self.line(&format!(
                    "  store {usize_ty} %{required}, ptr %{length_address}"
                ));
                "0".to_owned()
            }
            Primitive::ArrayPopMove => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array pop")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                if element_ty != dst_ty {
                    return Err(vec![unsupported(
                        function,
                        "Array popped value type mismatch",
                    )]);
                }
                let usize_ty = format!("i{}", self.pointer_width());
                let array = self.emit_array_from_reference(reference);
                let length_address = self.temp();
                let length = self.temp();
                let empty = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.line(&format!("  %{empty} = icmp eq {usize_ty} %{length}, 0"));
                self.emit_trap_if(empty);
                let index = self.temp();
                self.line(&format!("  %{index} = sub {usize_ty} %{length}, 1"));
                let (slot, initialized) = self.emit_checked_array_slot(
                    &array,
                    &usize_ty,
                    &format!("%{index}"),
                    &element_ty,
                    true,
                );
                let value = self.temp();
                self.line(&format!("  %{value} = load {element_ty}, ptr {slot}"));
                self.line(&format!("  store i8 0, ptr {initialized}"));
                self.line(&format!(
                    "  store {usize_ty} %{index}, ptr %{length_address}"
                ));
                format!("%{value}")
            }
            Primitive::ArrayReserve => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array reserve")]);
                };
                let Some((additional_ty, additional)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array reserve")]);
                };
                self.referenced_array_element(function, args[0].register)?;
                self.overflow_widths.insert((self.pointer_width(), "uadd"));
                let array = self.emit_array_from_reference(reference);
                let length_address = self.temp();
                let length = self.temp();
                let pair = self.temp();
                let required = self.temp();
                let overflow = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {additional_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{pair} = call {{ {additional_ty}, i1 }} @llvm.uadd.with.overflow.{additional_ty}({additional_ty} %{length}, {additional_ty} {additional})"
                ));
                self.line(&format!(
                    "  %{required} = extractvalue {{ {additional_ty}, i1 }} %{pair}, 0"
                ));
                self.line(&format!(
                    "  %{overflow} = extractvalue {{ {additional_ty}, i1 }} %{pair}, 1"
                ));
                self.emit_trap_if(overflow);
                self.line(&format!(
                    "  call void @g1_array_grow(ptr {array}, {additional_ty} %{required})"
                ));
                "0".to_owned()
            }
            Primitive::ArrayFinishDrained => {
                let Some((_, array)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed drained Array finish",
                    )]);
                };
                let array_ty = self.register_runtime_type(function, args[0].register)?;
                let element = self.array_element(array_ty)?;
                self.ensure_plain_array_element(element, function)?;
                let usize_ty = format!("i{}", self.pointer_width());
                let length_address = self.temp();
                let length = self.temp();
                let empty = self.temp();
                let loop_id = self.temp();
                let index_address = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.line(&format!("  %{empty} = icmp eq {usize_ty} %{length}, 0"));
                self.line(&format!("  %{index_address} = alloca {usize_ty}"));
                self.line(&format!("  store {usize_ty} 0, ptr %{index_address}"));
                self.line(&format!(
                    "  br i1 %{empty}, label %array.drain.done{loop_id}, label %array.drain.check{loop_id}"
                ));
                self.line(&format!("array.drain.check{loop_id}:"));
                let index = self.temp();
                let initialized_address = self.temp();
                let initialized = self.temp();
                let slot = self.temp();
                let state = self.temp();
                let occupied = self.temp();
                self.line(&format!(
                    "  %{index} = load {usize_ty}, ptr %{index_address}"
                ));
                self.line(&format!(
                    "  %{initialized_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
                ));
                self.line(&format!(
                    "  %{initialized} = load ptr, ptr %{initialized_address}"
                ));
                self.line(&format!(
                    "  %{slot} = getelementptr inbounds i8, ptr %{initialized}, {usize_ty} %{index}"
                ));
                self.line(&format!("  %{state} = load i8, ptr %{slot}"));
                self.line(&format!("  %{occupied} = icmp ne i8 %{state}, 0"));
                let trap_label = self.temp();
                let continue_label = self.temp();
                self.line(&format!(
                    "  br i1 %{occupied}, label %array.drain.trap{trap_label}, label %array.drain.continue{continue_label}"
                ));
                self.line(&format!("array.drain.trap{trap_label}:"));
                self.line("  call void @llvm.trap()");
                self.line("  unreachable");
                self.line(&format!("array.drain.continue{continue_label}:"));
                let next = self.temp();
                let more = self.temp();
                self.line(&format!("  %{next} = add {usize_ty} %{index}, 1"));
                self.line(&format!("  store {usize_ty} %{next}, ptr %{index_address}"));
                self.line(&format!(
                    "  %{more} = icmp ult {usize_ty} %{next}, %{length}"
                ));
                self.line(&format!(
                    "  br i1 %{more}, label %array.drain.check{loop_id}, label %array.drain.done{loop_id}"
                ));
                self.line(&format!("array.drain.done{loop_id}:"));
                self.line(&format!("  call void @g1_array_free(ptr {array})"));
                "0".to_owned()
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
            Terminator::CallKnownReceiver {
                result,
                function: callee,
                receiver,
                args,
                normal,
            } => self.emit_call_with_receiver(
                function,
                *result,
                *callee as usize,
                receiver,
                args,
                normal,
                false,
            )?,
            Terminator::HostCall {
                result,
                import,
                args,
                normal,
            } => self.emit_host_call(function, *result, *import, args, normal)?,
            Terminator::CallIndirect {
                result,
                callable,
                known_function,
                receiver_mode,
                cleanup_callable,
                args,
                normal,
            } => self.emit_indirect_call(
                function,
                *result,
                callable,
                *known_function,
                *receiver_mode,
                *cleanup_callable,
                args,
                Some(normal),
            )?,
            Terminator::TailCall {
                function: callee,
                args,
            } => self.emit_tail_call(function, *callee as usize, args)?,
            Terminator::TailCallSelf { args } => {
                self.emit_tail_call(function, function_index, args)?
            }
            Terminator::TailCallKnownReceiver {
                function: callee,
                receiver,
                args,
            } => self.emit_call_with_receiver(
                function,
                None,
                *callee as usize,
                receiver,
                args,
                &mir::Edge {
                    target: u32::MAX,
                    args: Vec::new(),
                },
                true,
            )?,
            Terminator::TailCallIndirect {
                callable,
                known_function,
                receiver_mode,
                args,
            } => self.emit_indirect_call(
                function,
                None,
                callable,
                *known_function,
                *receiver_mode,
                false,
                args,
                None,
            )?,
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
            Terminator::Leave { target, .. } => self.emit_edge(function, target)?,
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

    fn emit_call_with_receiver(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callee_index: usize,
        receiver: &mir::Operand,
        args: &[mir::Operand],
        normal: &mir::Edge,
        tail: bool,
    ) -> Result<(), Vec<Diagnostic>> {
        let callee = self
            .phases
            .mir
            .functions
            .get(callee_index)
            .ok_or_else(|| vec![unsupported(caller, "call to a missing receiver function")])?;
        if callee.receiver_mode != Some(0) {
            return Err(vec![unsupported(
                caller,
                "known-receiver calls whose target does not use a shared receiver",
            )]);
        }
        let receiver_ty = self.register_type(caller, receiver.register)?;
        let receiver_value = self.load_operand(caller, receiver)?;
        let mut arguments = vec![format!("{receiver_ty} {receiver_value}")];
        for operand in args {
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                let runtime_ty = self.register_runtime_type(caller, operand.register)?;
                self.emit_retain(runtime_ty, &value, caller)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let arguments = arguments.join(", ");
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
        if tail {
            if let Some(value) = call {
                self.line(&format!("  ret {result_ty} %{value}"));
            } else {
                self.line("  ret void");
            }
            return Ok(());
        }
        if let (Some(dst), Some(value)) = (result, call) {
            self.line(&format!("  store {result_ty} %{value}, ptr %r{dst}"));
        }
        self.emit_edge_with_preassigned(caller, normal, result.into_iter().collect())
    }

    fn emit_host_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        import: HostImportRole,
        args: &[mir::Operand],
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let expected_args = match import {
            HostImportRole::ProcessArgsGet => Vec::new(),
            HostImportRole::FsRead | HostImportRole::DiagnosticWrite => vec![Type::Text],
            HostImportRole::FsWrite => vec![Type::Text, Type::Bytes],
        };
        if args.len() != expected_args.len() {
            return Err(vec![unsupported(
                caller,
                "host call argument count mismatch",
            )]);
        }
        let mut arguments = Vec::with_capacity(args.len());
        let mut loaded = Vec::with_capacity(args.len());
        for (operand, expected) in args.iter().zip(&expected_args) {
            let runtime_ty = self.register_runtime_type(caller, operand.register)?;
            if self.runtime_type(runtime_ty)? != expected {
                return Err(vec![unsupported(
                    caller,
                    "host call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(runtime_ty, &value, caller)?;
            }
            arguments.push(format!("{ty} {value}"));
            loaded.push((runtime_ty, value));
        }
        let arguments = arguments.join(", ");
        let returned = match import {
            HostImportRole::ProcessArgsGet => {
                let dst = result.ok_or_else(|| {
                    vec![unsupported(
                        caller,
                        "process-args host call without a result",
                    )]
                })?;
                let result_ty = self.register_runtime_type(caller, dst)?;
                let Type::Array { element } = self.runtime_type(result_ty)? else {
                    return Err(vec![unsupported(
                        caller,
                        "process-args host result is not an Array",
                    )]);
                };
                if !matches!(self.runtime_type(*element)?, Type::Text) {
                    return Err(vec![unsupported(
                        caller,
                        "process-args host result is not Array<Text>",
                    )]);
                }
                let value = self.temp();
                self.line(&format!(
                    "  %{value} = call ptr @g1_host_process_args_get()"
                ));
                Some(value)
            }
            HostImportRole::FsRead => {
                let dst = result.ok_or_else(|| {
                    vec![unsupported(caller, "fs-read host call without a result")]
                })?;
                let result_ty = self.register_runtime_type(caller, dst)?;
                if !matches!(self.runtime_type(result_ty)?, Type::Bytes) {
                    return Err(vec![unsupported(
                        caller,
                        "fs-read host result is not Bytes",
                    )]);
                }
                let value = self.temp();
                self.line(&format!(
                    "  %{value} = call ptr @g1_host_fs_read({arguments})"
                ));
                Some(value)
            }
            HostImportRole::FsWrite => {
                self.line(&format!("  call void @g1_host_fs_write({arguments})"));
                None
            }
            HostImportRole::DiagnosticWrite => {
                self.line(&format!(
                    "  call void @g1_host_diagnostic_write({arguments})"
                ));
                None
            }
        };
        for (runtime_ty, value) in loaded {
            self.emit_destroy(runtime_ty, &value, caller)?;
        }
        if let (Some(dst), Some(value)) = (result, returned) {
            self.line(&format!("  store ptr %{value}, ptr %r{dst}"));
        }
        self.emit_edge_with_preassigned(caller, normal, result.into_iter().collect())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_indirect_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callable_operand: &mir::Operand,
        known_function: Option<u32>,
        requested_mode: u32,
        cleanup_callable: bool,
        args: &[mir::Operand],
        normal: Option<&mir::Edge>,
    ) -> Result<(), Vec<Diagnostic>> {
        let callable_type = self.register_runtime_type(caller, callable_operand.register)?;
        let Type::Callable {
            signature,
            capture_type,
            receiver_mode,
            ..
        } = self.runtime_type(callable_type)?.clone()
        else {
            return Err(vec![unsupported(
                caller,
                "indirect call through a non-callable value",
            )]);
        };
        if requested_mode > 2 || requested_mode < receiver_mode {
            return Err(vec![unsupported(
                caller,
                "indirect call with an incompatible receiver mode",
            )]);
        }
        if signature.params.len() != args.len() {
            return Err(vec![unsupported(
                caller,
                "indirect call argument count mismatch",
            )]);
        }
        if let Some(target) = known_function {
            let target = self
                .phases
                .mir
                .functions
                .get(target as usize)
                .ok_or_else(|| vec![unsupported(caller, "missing known indirect-call target")])?;
            if target.receiver_mode != Some(receiver_mode) {
                return Err(vec![unsupported(
                    caller,
                    "known indirect-call receiver mode mismatch",
                )]);
            }
        }

        let callable = self.load_operand(caller, callable_operand)?;
        let function_address = self.temp();
        self.line(&format!(
            "  %{function_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 1"
        ));
        let target = self.temp();
        self.line(&format!("  %{target} = load ptr, ptr %{function_address}"));
        let capture_address = self.temp();
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 2"
        ));
        let capture = self.temp();
        self.line(&format!("  %{capture} = load ptr, ptr %{capture_address}"));

        let mut arguments = Vec::with_capacity(args.len() + 1);
        if receiver_mode == 2 {
            let capture_ty = self.llvm_type(capture_type)?;
            let receiver = self.temp();
            self.line(&format!(
                "  %{receiver} = load {capture_ty}, ptr %{capture}"
            ));
            self.line(&format!("  call void @free(ptr %{capture})"));
            self.line(&format!("  call void @free(ptr {callable})"));
            arguments.push(format!("{capture_ty} %{receiver}"));
        } else {
            arguments.push(format!("ptr %{capture}"));
        }
        for (operand, expected) in args.iter().zip(&signature.params) {
            let runtime_ty = self.register_runtime_type(caller, operand.register)?;
            if runtime_ty != *expected {
                return Err(vec![unsupported(
                    caller,
                    "indirect call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(runtime_ty, &value, caller)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let arguments = arguments.join(", ");
        let result_ty = self.llvm_return_type(signature.result)?;
        let call = if result_ty == "void" {
            self.line(&format!("  call void %{target}({arguments})"));
            None
        } else {
            let value = self.temp();
            self.line(&format!(
                "  %{value} = call {result_ty} %{target}({arguments})"
            ));
            Some(value)
        };
        if receiver_mode != 2 && (requested_mode == 2 || cleanup_callable) {
            self.emit_destroy(callable_type, &callable, caller)?;
        }
        if let Some(normal) = normal {
            if let (Some(dst), Some(value)) = (result, call) {
                self.line(&format!("  store {result_ty} %{value}, ptr %r{dst}"));
            }
            self.emit_edge_with_preassigned(caller, normal, result.into_iter().collect())
        } else {
            if let Some(value) = call {
                self.line(&format!("  ret {result_ty} %{value}"));
            } else {
                self.line("  ret void");
            }
            Ok(())
        }
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
                Type::BindingPack { payload_type, .. } => self
                    .type_contains_byte_object(*payload_type, visiting)
                    .unwrap_or(true),
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

    fn type_contains_array(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<bool, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(false);
        }
        let contains = match self.runtime_type(ty)? {
            Type::Array { .. } => true,
            Type::Tuple { fields, .. } => fields
                .iter()
                .any(|field| self.type_contains_array(*field, visiting).unwrap_or(true)),
            Type::Struct { fields, .. } => fields
                .iter()
                .any(|field| self.type_contains_array(field.ty, visiting).unwrap_or(true)),
            Type::BindingPack { payload_type, .. } => self
                .type_contains_array(*payload_type, visiting)
                .unwrap_or(true),
            Type::Enum { variants, .. } => variants
                .iter()
                .flat_map(|variant| &variant.fields)
                .any(|field| self.type_contains_array(field.ty, visiting).unwrap_or(true)),
            _ => false,
        };
        visiting.remove(&ty);
        Ok(contains)
    }

    fn type_contains_callable(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<bool, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(false);
        }
        let contains =
            match self.runtime_type(ty)? {
                Type::Callable { .. } => true,
                Type::Tuple { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_callable(*field, visiting)
                        .unwrap_or(true)
                }),
                Type::Struct { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_callable(field.ty, visiting)
                        .unwrap_or(true)
                }),
                Type::BindingPack { payload_type, .. } => self
                    .type_contains_callable(*payload_type, visiting)
                    .unwrap_or(true),
                Type::Enum { variants, .. } => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| {
                        self.type_contains_callable(field.ty, visiting)
                            .unwrap_or(true)
                    }),
                _ => false,
            };
        visiting.remove(&ty);
        Ok(contains)
    }

    fn ensure_plain_array_element(
        &self,
        ty: TypeId,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        match self.runtime_type(ty)? {
            Type::Callable { .. }
            | Type::Handler { .. }
            | Type::Resumption { .. }
            | Type::BindingPack { .. }
            | Type::Available { .. } => {
                return Err(vec![unsupported(
                    function,
                    "Array elements with callable or effect runtime state",
                )]);
            }
            Type::Array { element } => self.ensure_plain_array_element(*element, function)?,
            Type::Tuple { fields, .. } => {
                for field in fields {
                    self.ensure_plain_array_element(*field, function)?;
                }
            }
            Type::Struct { fields, .. } => {
                for field in fields {
                    self.ensure_plain_array_element(field.ty, function)?;
                }
            }
            Type::Enum { variants, .. } => {
                for field in variants.iter().flat_map(|variant| &variant.fields) {
                    self.ensure_plain_array_element(field.ty, function)?;
                }
            }
            _ => {}
        }
        self.llvm_type(ty)?;
        Ok(())
    }

    fn emit_retain(
        &mut self,
        ty: TypeId,
        value: &str,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        match self.runtime_type(ty)?.clone() {
            Type::Text | Type::Bytes => {
                self.line(&format!("  call void @g1_bytes_retain(ptr {value})"));
            }
            Type::Callable { .. } => {
                let count_address = self.temp();
                self.line(&format!(
                    "  %{count_address} = getelementptr inbounds %g1.callable, ptr {value}, i32 0, i32 0"
                ));
                let count = self.temp();
                self.line(&format!("  %{count} = load i64, ptr %{count_address}"));
                let next = self.temp();
                self.line(&format!("  %{next} = add i64 %{count}, 1"));
                self.line(&format!("  store i64 %{next}, ptr %{count_address}"));
            }
            Type::BindingPack { payload_type, .. } => {
                self.emit_retain(payload_type, value, function)?;
            }
            Type::Tuple { fields, .. } => {
                let aggregate_ty = self.llvm_type(ty)?;
                for (index, field) in fields.into_iter().enumerate() {
                    if self.type_contains_byte_object(field, &mut BTreeSet::new())?
                        || self.type_contains_callable(field, &mut BTreeSet::new())?
                    {
                        let extracted = self.temp();
                        self.line(&format!(
                            "  %{extracted} = extractvalue {aggregate_ty} {value}, {index}"
                        ));
                        self.emit_retain(field, &format!("%{extracted}"), function)?;
                    }
                }
            }
            Type::Struct { fields, .. } => {
                let aggregate_ty = self.llvm_type(ty)?;
                for (index, field) in fields.into_iter().enumerate() {
                    if self.type_contains_byte_object(field.ty, &mut BTreeSet::new())?
                        || self.type_contains_callable(field.ty, &mut BTreeSet::new())?
                    {
                        let extracted = self.temp();
                        self.line(&format!(
                            "  %{extracted} = extractvalue {aggregate_ty} {value}, {index}"
                        ));
                        self.emit_retain(field.ty, &format!("%{extracted}"), function)?;
                    }
                }
            }
            Type::Enum { .. } if self.type_contains_array(ty, &mut BTreeSet::new())? => {
                return Err(vec![unsupported(
                    function,
                    "copying enum values that contain Array",
                )]);
            }
            Type::Enum { .. }
                if self.type_contains_byte_object(ty, &mut BTreeSet::new())?
                    || self.type_contains_callable(ty, &mut BTreeSet::new())? =>
            {
                self.emit_visit_enum_payloads(ty, value, true, function)?;
            }
            Type::Array { .. } if self.type_contains_array(ty, &mut BTreeSet::new())? => {
                return Err(vec![unsupported(function, "copying Array values")]);
            }
            _ => {}
        }
        Ok(())
    }

    fn emit_destroy(
        &mut self,
        ty: TypeId,
        value: &str,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let value = if let Some(glue) = self
            .phases
            .artifact
            .drop_glue
            .iter()
            .find(|glue| glue.ty == ty)
        {
            let hook = self
                .phases
                .mir
                .functions
                .get(glue.function as usize)
                .ok_or_else(|| vec![unsupported(function, "missing custom drop hook")])?;
            if hook.params.len() != 1
                || !matches!(
                    self.runtime_type(hook.params[0])?,
                    Type::RefUnique { referent } if *referent == ty
                )
                || !matches!(self.runtime_type(hook.result)?, Type::Unit)
            {
                return Err(vec![unsupported(
                    function,
                    "custom drop hook with an incompatible signature",
                )]);
            }
            let llvm_ty = self.llvm_type(ty)?;
            let slot = self.temp();
            self.line(&format!("  %{slot} = alloca {llvm_ty}"));
            self.line(&format!("  store {llvm_ty} {value}, ptr %{slot}"));
            self.line(&format!("  call void @g1_f{}(ptr %{slot})", glue.function));
            let reloaded = self.temp();
            self.line(&format!("  %{reloaded} = load {llvm_ty}, ptr %{slot}"));
            format!("%{reloaded}")
        } else {
            value.to_owned()
        };
        match self.runtime_type(ty)?.clone() {
            Type::Text | Type::Bytes => {
                self.line(&format!("  call void @g1_bytes_release(ptr {value})"));
            }
            Type::Callable { capture_type, .. } => {
                self.emit_destroy_callable(&value, capture_type, function)?;
            }
            Type::BindingPack { payload_type, .. } => {
                self.emit_destroy(payload_type, &value, function)?;
            }
            Type::Array { element } => {
                self.ensure_plain_array_element(element, function)?;
                self.emit_destroy_array_elements(&value, element, function)?;
                self.line(&format!("  call void @g1_array_free(ptr {value})"));
            }
            Type::Tuple { fields, .. } => {
                let aggregate_ty = self.llvm_type(ty)?;
                for (index, field) in fields.into_iter().enumerate().rev() {
                    if self.type_contains_byte_object(field, &mut BTreeSet::new())?
                        || self.type_contains_array(field, &mut BTreeSet::new())?
                        || self.type_contains_callable(field, &mut BTreeSet::new())?
                    {
                        let extracted = self.temp();
                        self.line(&format!(
                            "  %{extracted} = extractvalue {aggregate_ty} {value}, {index}"
                        ));
                        self.emit_destroy(field, &format!("%{extracted}"), function)?;
                    }
                }
            }
            Type::Struct { fields, .. } => {
                let aggregate_ty = self.llvm_type(ty)?;
                for (index, field) in fields.into_iter().enumerate().rev() {
                    if self.type_contains_byte_object(field.ty, &mut BTreeSet::new())?
                        || self.type_contains_array(field.ty, &mut BTreeSet::new())?
                        || self.type_contains_callable(field.ty, &mut BTreeSet::new())?
                    {
                        let extracted = self.temp();
                        self.line(&format!(
                            "  %{extracted} = extractvalue {aggregate_ty} {value}, {index}"
                        ));
                        self.emit_destroy(field.ty, &format!("%{extracted}"), function)?;
                    }
                }
            }
            Type::Enum { .. }
                if self.type_contains_byte_object(ty, &mut BTreeSet::new())?
                    || self.type_contains_array(ty, &mut BTreeSet::new())?
                    || self.type_contains_callable(ty, &mut BTreeSet::new())? =>
            {
                self.emit_visit_enum_payloads(ty, &value, false, function)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn emit_destroy_callable(
        &mut self,
        callable: &str,
        capture_type: TypeId,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 0"
        ));
        let count = self.temp();
        self.line(&format!("  %{count} = load i64, ptr %{count_address}"));
        let last = self.temp();
        self.line(&format!("  %{last} = icmp eq i64 %{count}, 1"));
        let destroy_label = self.temp();
        let decrement_label = self.temp();
        let done_label = self.temp();
        self.line(&format!(
            "  br i1 %{last}, label %callable.destroy{destroy_label}, label %callable.decrement{decrement_label}"
        ));
        self.line(&format!("callable.decrement{decrement_label}:"));
        let next = self.temp();
        self.line(&format!("  %{next} = sub i64 %{count}, 1"));
        self.line(&format!("  store i64 %{next}, ptr %{count_address}"));
        self.line(&format!("  br label %callable.done{done_label}"));
        self.line(&format!("callable.destroy{destroy_label}:"));
        let capture_address = self.temp();
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 2"
        ));
        let capture = self.temp();
        self.line(&format!("  %{capture} = load ptr, ptr %{capture_address}"));
        let capture_ty = self.llvm_type(capture_type)?;
        let capture_value = self.temp();
        self.line(&format!(
            "  %{capture_value} = load {capture_ty}, ptr %{capture}"
        ));
        self.emit_destroy(capture_type, &format!("%{capture_value}"), function)?;
        self.line(&format!("  call void @free(ptr %{capture})"));
        self.line(&format!("  call void @free(ptr {callable})"));
        self.line(&format!("  br label %callable.done{done_label}"));
        self.line(&format!("callable.done{done_label}:"));
        Ok(())
    }

    fn emit_visit_enum_payloads(
        &mut self,
        ty: TypeId,
        value: &str,
        retain: bool,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let Type::Enum { variants, .. } = self.runtime_type(ty)?.clone() else {
            return Err(vec![unsupported(
                function,
                "owned enum traversal on a non-enum value",
            )]);
        };
        let enum_ty = self.llvm_type(ty)?;
        let tag = self.temp();
        self.line(&format!("  %{tag} = extractvalue {enum_ty} {value}, 0"));
        let traversal = self.temp();
        let trap = self.temp();
        let done = self.temp();
        let cases = (0..variants.len()).map(|_| self.temp()).collect::<Vec<_>>();
        self.line(&format!(
            "  switch i32 %{tag}, label %enum.owned.trap{trap} ["
        ));
        for (variant, label) in cases.iter().enumerate() {
            self.line(&format!(
                "    i32 {variant}, label %enum.owned.case{traversal}.{label}"
            ));
        }
        self.line("  ]");
        self.line(&format!("enum.owned.trap{trap}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        for (variant, label) in variants.iter().zip(cases) {
            self.line(&format!("enum.owned.case{traversal}.{label}:"));
            let fields = if retain {
                variant.fields.iter().enumerate().collect::<Vec<_>>()
            } else {
                variant.fields.iter().enumerate().rev().collect::<Vec<_>>()
            };
            for (field_index, field) in fields {
                let owned = self.type_contains_byte_object(field.ty, &mut BTreeSet::new())?
                    || self.type_contains_array(field.ty, &mut BTreeSet::new())?
                    || self.type_contains_callable(field.ty, &mut BTreeSet::new())?;
                if !owned {
                    continue;
                }
                let field_value =
                    self.emit_unpack_enum_field(ty, value, field_index as u32, field.ty)?;
                if retain {
                    self.emit_retain(field.ty, &field_value, function)?;
                } else {
                    self.emit_destroy(field.ty, &field_value, function)?;
                }
            }
            self.line(&format!("  br label %enum.owned.done{done}"));
        }
        self.line(&format!("enum.owned.done{done}:"));
        Ok(())
    }

    fn emit_unpack_enum_field(
        &mut self,
        enum_type: TypeId,
        value: &str,
        field: u32,
        field_type: TypeId,
    ) -> Result<String, Vec<Diagnostic>> {
        let enum_ty = self.llvm_type(enum_type)?;
        let words = self.enum_slot_words(enum_type, field)?;
        let slot_ty = format!("[{words} x i128]");
        let packed = self.temp();
        self.line(&format!(
            "  %{packed} = extractvalue {enum_ty} {value}, {}",
            field + 1
        ));
        let slot = self.temp();
        self.line(&format!("  %{slot} = alloca {slot_ty}"));
        self.line(&format!(
            "  store {slot_ty} %{packed}, ptr %{slot}, align 1"
        ));
        let field_ty = self.llvm_type(field_type)?;
        let unpacked = self.temp();
        self.line(&format!(
            "  %{unpacked} = load {field_ty}, ptr %{slot}, align 1"
        ));
        Ok(format!("%{unpacked}"))
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

    fn array_element(&self, array: TypeId) -> Result<TypeId, Vec<Diagnostic>> {
        match self.runtime_type(array)? {
            Type::Array { element } => Ok(*element),
            other => Err(vec![backend_error(format!(
                "LLVM Array operation requires an Array type, found {other:?}"
            ))]),
        }
    }

    fn referenced_array_element(
        &self,
        function: &mir::Function,
        reference_register: u32,
    ) -> Result<TypeId, Vec<Diagnostic>> {
        let reference = self.register_runtime_type(function, reference_register)?;
        let array = match self.runtime_type(reference)? {
            Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
            other => {
                return Err(vec![unsupported(
                    function,
                    format!("Array operation through non-reference {other:?}"),
                )]);
            }
        };
        let element = self.array_element(array)?;
        self.ensure_plain_array_element(element, function)?;
        Ok(element)
    }

    fn emit_array_element_size(&mut self, element_ty: &str) -> String {
        let usize_ty = format!("i{}", self.pointer_width());
        let end = self.temp();
        let size = self.temp();
        self.line(&format!(
            "  %{end} = getelementptr {element_ty}, ptr null, {usize_ty} 1"
        ));
        self.line(&format!("  %{size} = ptrtoint ptr %{end} to {usize_ty}"));
        format!("%{size}")
    }

    fn emit_array_from_reference(&mut self, reference: &str) -> String {
        let array = self.temp();
        self.line(&format!("  %{array} = load ptr, ptr {reference}"));
        format!("%{array}")
    }

    fn emit_checked_array_slot(
        &mut self,
        array: &str,
        index_ty: &str,
        index: &str,
        element_ty: &str,
        require_initialized: bool,
    ) -> (String, String) {
        let length_address = self.temp();
        let length = self.temp();
        let out_of_bounds = self.temp();
        let initialized_address_address = self.temp();
        let initialized = self.temp();
        let initialized_slot = self.temp();
        let state = self.temp();
        let wrong_state = self.temp();
        let invalid = self.temp();
        self.line(&format!(
            "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{length} = load {index_ty}, ptr %{length_address}"
        ));
        self.line(&format!(
            "  %{out_of_bounds} = icmp uge {index_ty} {index}, %{length}"
        ));
        self.line(&format!(
            "  %{initialized_address_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
        ));
        self.line(&format!(
            "  %{initialized} = load ptr, ptr %{initialized_address_address}"
        ));
        self.line(&format!(
            "  %{initialized_slot} = getelementptr inbounds i8, ptr %{initialized}, {index_ty} {index}"
        ));
        self.line(&format!("  %{state} = load i8, ptr %{initialized_slot}"));
        self.line(&format!(
            "  %{wrong_state} = icmp {} i8 %{state}, 0",
            if require_initialized { "eq" } else { "ne" }
        ));
        self.line(&format!(
            "  %{invalid} = or i1 %{out_of_bounds}, %{wrong_state}"
        ));
        self.emit_trap_if(invalid);
        let data_address = self.temp();
        let data = self.temp();
        let slot = self.temp();
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 3"
        ));
        self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
        self.line(&format!(
            "  %{slot} = getelementptr inbounds {element_ty}, ptr %{data}, {index_ty} {index}"
        ));
        (format!("%{slot}"), format!("%{initialized_slot}"))
    }

    fn emit_array_dense_check(&mut self, array: &str, length: &str, usize_ty: &str) {
        let empty = self.temp();
        let loop_id = self.temp();
        let index_address = self.temp();
        self.line(&format!("  %{empty} = icmp eq {usize_ty} {length}, 0"));
        self.line(&format!("  %{index_address} = alloca {usize_ty}"));
        self.line(&format!("  store {usize_ty} 0, ptr %{index_address}"));
        self.line(&format!(
            "  br i1 %{empty}, label %array.dense.done{loop_id}, label %array.dense.check{loop_id}"
        ));
        self.line(&format!("array.dense.check{loop_id}:"));
        let index = self.temp();
        let initialized_address = self.temp();
        let initialized = self.temp();
        let slot = self.temp();
        let state = self.temp();
        let empty_slot = self.temp();
        self.line(&format!(
            "  %{index} = load {usize_ty}, ptr %{index_address}"
        ));
        self.line(&format!(
            "  %{initialized_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
        ));
        self.line(&format!(
            "  %{initialized} = load ptr, ptr %{initialized_address}"
        ));
        self.line(&format!(
            "  %{slot} = getelementptr inbounds i8, ptr %{initialized}, {usize_ty} %{index}"
        ));
        self.line(&format!("  %{state} = load i8, ptr %{slot}"));
        self.line(&format!("  %{empty_slot} = icmp eq i8 %{state}, 0"));
        let trap_label = self.temp();
        let continue_label = self.temp();
        self.line(&format!(
            "  br i1 %{empty_slot}, label %array.dense.trap{trap_label}, label %array.dense.continue{continue_label}"
        ));
        self.line(&format!("array.dense.trap{trap_label}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        self.line(&format!("array.dense.continue{continue_label}:"));
        let next = self.temp();
        let more = self.temp();
        self.line(&format!("  %{next} = add {usize_ty} %{index}, 1"));
        self.line(&format!("  store {usize_ty} %{next}, ptr %{index_address}"));
        self.line(&format!(
            "  %{more} = icmp ult {usize_ty} %{next}, {length}"
        ));
        self.line(&format!(
            "  br i1 %{more}, label %array.dense.check{loop_id}, label %array.dense.done{loop_id}"
        ));
        self.line(&format!("array.dense.done{loop_id}:"));
    }

    fn emit_destroy_array_elements(
        &mut self,
        array: &str,
        element: TypeId,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        if !self.type_contains_byte_object(element, &mut BTreeSet::new())?
            && !self.type_contains_array(element, &mut BTreeSet::new())?
        {
            return Ok(());
        }
        let usize_ty = format!("i{}", self.pointer_width());
        let element_ty = self.llvm_type(element)?;
        let length_address = self.temp();
        let length = self.temp();
        let empty = self.temp();
        let loop_id = self.temp();
        let index_address = self.temp();
        self.line(&format!(
            "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{length} = load {usize_ty}, ptr %{length_address}"
        ));
        self.line(&format!("  %{empty} = icmp eq {usize_ty} %{length}, 0"));
        self.line(&format!("  %{index_address} = alloca {usize_ty}"));
        self.line(&format!("  store {usize_ty} 0, ptr %{index_address}"));
        self.line(&format!(
            "  br i1 %{empty}, label %array.destroy.done{loop_id}, label %array.destroy.check{loop_id}"
        ));
        self.line(&format!("array.destroy.check{loop_id}:"));
        let index = self.temp();
        let initialized_address = self.temp();
        let initialized = self.temp();
        let initialized_slot = self.temp();
        let state = self.temp();
        let occupied = self.temp();
        let destroy_label = self.temp();
        let continue_label = self.temp();
        self.line(&format!(
            "  %{index} = load {usize_ty}, ptr %{index_address}"
        ));
        self.line(&format!(
            "  %{initialized_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
        ));
        self.line(&format!(
            "  %{initialized} = load ptr, ptr %{initialized_address}"
        ));
        self.line(&format!(
            "  %{initialized_slot} = getelementptr inbounds i8, ptr %{initialized}, {usize_ty} %{index}"
        ));
        self.line(&format!("  %{state} = load i8, ptr %{initialized_slot}"));
        self.line(&format!("  %{occupied} = icmp ne i8 %{state}, 0"));
        self.line(&format!(
            "  br i1 %{occupied}, label %array.destroy.value{destroy_label}, label %array.destroy.continue{continue_label}"
        ));
        self.line(&format!("array.destroy.value{destroy_label}:"));
        let data_address = self.temp();
        let data = self.temp();
        let slot = self.temp();
        let value = self.temp();
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 3"
        ));
        self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
        self.line(&format!(
            "  %{slot} = getelementptr inbounds {element_ty}, ptr %{data}, {usize_ty} %{index}"
        ));
        self.line(&format!("  %{value} = load {element_ty}, ptr %{slot}"));
        self.emit_destroy(element, &format!("%{value}"), function)?;
        self.line(&format!(
            "  br label %array.destroy.continue{continue_label}"
        ));
        self.line(&format!("array.destroy.continue{continue_label}:"));
        let next = self.temp();
        let more = self.temp();
        self.line(&format!("  %{next} = add {usize_ty} %{index}, 1"));
        self.line(&format!("  store {usize_ty} %{next}, ptr %{index_address}"));
        self.line(&format!(
            "  %{more} = icmp ult {usize_ty} %{next}, %{length}"
        ));
        self.line(&format!(
            "  br i1 %{more}, label %array.destroy.check{loop_id}, label %array.destroy.done{loop_id}"
        ));
        self.line(&format!("array.destroy.done{loop_id}:"));
        Ok(())
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
            Type::Text
            | Type::Bytes
            | Type::Array { .. }
            | Type::Callable { .. }
            | Type::RefShared { .. }
            | Type::RefUnique { .. } => usize::from(self.pointer_width() / 8),
            Type::BindingPack { payload_type, .. } => self.storage_size(*payload_type, visiting)?,
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
            Type::BindingPack { payload_type, .. } => {
                return self.aggregate_field_type(*payload_type, field);
            }
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
            Type::Text
            | Type::Bytes
            | Type::Array { .. }
            | Type::Callable { .. }
            | Type::RefShared { .. }
            | Type::RefUnique { .. } => "ptr".into(),
            Type::BindingPack { payload_type, .. } => self.llvm_type(*payload_type)?,
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
