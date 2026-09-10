use super::{
    CandidateVmProgram, DefKey, Digest, LlvmAbiDescriptor, LlvmError, LlvmTarget, NativeTypeLayout,
    VmType, layout,
};
use crate::vm_backend::{
    VmCompare, VmFunction, VmInstruction as I, VmPattern,
    native_memory::{NativeFields, NativeLayout, NativeShape},
};
use grandiose_runtime::memory::MemoryLayout;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write,
    sync::Arc,
};

#[path = "memory_emit.rs"]
mod memory;
#[path = "scalar.rs"]
mod scalar;

const MAX_FRAME_BYTES: u64 = 64 * 1024;
const MAX_INIT_PATHS: usize = 16 * 1024;

#[derive(Clone, Debug)]
pub(in crate::vm_backend) struct FunctionPlan {
    pub(in crate::vm_backend) layouts: Vec<Arc<NativeLayout>>,
    pub(in crate::vm_backend) paths: Vec<Vec<Vec<u32>>>,
    pub(in crate::vm_backend) result: Arc<NativeLayout>,
}

pub(super) struct Plan<'a> {
    program: &'a CandidateVmProgram,
    vm_functions: &'a BTreeSet<DefKey>,
    pub(super) layouts: BTreeMap<Vec<u8>, NativeTypeLayout>,
    pub(super) functions: Vec<DefKey>,
    pub(super) plans: Vec<FunctionPlan>,
    packet_offsets: Vec<Vec<u64>>,
    packet_init_offsets: Vec<Vec<u64>>,
    packet_bytes: u64,
    packet_alignment: u64,
    max_arguments: usize,
    pub(super) frame_bytes: u64,
}

impl<'a> Plan<'a> {
    pub(super) fn new(
        program: &'a CandidateVmProgram,
        target: &LlvmTarget,
        vm_functions: &'a BTreeSet<DefKey>,
    ) -> Result<Self, LlvmError> {
        target.validate_host()?;
        let functions = program.functions.keys().copied().collect::<Vec<_>>();
        let mut result = Self {
            program,
            vm_functions,
            layouts: BTreeMap::new(),
            functions,
            plans: vec![],
            packet_offsets: vec![],
            packet_init_offsets: vec![],
            packet_bytes: 1,
            packet_alignment: 1,
            max_arguments: 0,
            frame_bytes: 0,
        };
        for key in &result.functions {
            let function = &program.functions[key];
            let unsupported = |instruction, reason: &str| LlvmError::Unsupported {
                function: *key,
                instruction,
                reason: reason.into(),
            };
            if !vm_functions.is_empty() && function.captures != 0 {
                return Err(unsupported(0, "mixed-engine capture loans are not implemented"));
            }
            let descriptors = function.nominal_copy_descriptors.clone().into();
            let mut layouts = vec![];
            let mut paths: Vec<Vec<Vec<u32>>> = vec![];
            let mut frame_bytes = 0u64;
            let mut path_count = 0usize;
            for (register, ty) in function.registers.iter().enumerate() {
                let layout = layout::concrete_layout(ty, &descriptors).map_err(|_| {
                        unsupported(
                            0,
                            &format!("no shared native layout for register {register}: {ty:?}"),
                        )
                    })?;
                if !layout.supports_resident(&descriptors) {
                    return Err(unsupported(0, "native register contains an unsupported resident layout"));
                }
                result.layouts.insert(layout::type_key(ty), NativeTypeLayout::from_native(&layout));
                let mut resident_paths = BTreeSet::new();
                collect_paths(&layout, &mut vec![], &mut resident_paths)?;
                path_count = path_count
                    .checked_add(resident_paths.len())
                    .ok_or_else(|| unsupported(0, "native initialization metadata overflow"))?;
                if path_count > MAX_INIT_PATHS {
                    return Err(unsupported(
                        0,
                        "native initialization metadata exceeds the finite body limit",
                    ));
                }
                frame_bytes = frame_bytes
                    .checked_add(
                        layout.memory.size() as u64
                            + layout.memory.alignment() as u64
                            + resident_paths.len() as u64
                            + if layout.owns_callable() { 4 * std::mem::size_of::<usize>() as u64 } else { 0 },
                    )
                    .ok_or_else(|| unsupported(0, "native activation layout overflow"))?;
                layouts.push(layout);
                paths.push(resident_paths.into_iter().collect());
            }
            let Some(I::DeclareResult {
                result: result_type,
                ..
            }) = function.instructions.first()
            else {
                return Err(unsupported(
                    0,
                    "native function requires a declared result ABI",
                ));
            };
            for instruction in &function.instructions {
                if let I::Leave { arguments, .. } = instruction {
                    for argument in arguments {
                        let layout = &layouts[*argument as usize];
                        frame_bytes = frame_bytes
                            .checked_add(
                                layout.memory.size() as u64 + layout.memory.alignment() as u64
                                    + paths[*argument as usize].len() as u64
                                    + if layout.owns_callable() { 4 * std::mem::size_of::<usize>() as u64 } else { 0 },
                            )
                            .ok_or_else(|| {
                                unsupported(0, "native parallel-transfer storage overflow")
                            })?;
                    }
                }
            }
            let result_layout = layout::concrete_layout(result_type, &descriptors)
                .map_err(|_| unsupported(0, "native result has an unsupported shared layout"))?;
            if !result_layout.supports_resident(&descriptors) {
                return Err(unsupported(0, "native result contains an unsupported resident layout"));
            }
            result.layouts.insert(
                layout::type_key(result_type),
                NativeTypeLayout::from_native(&result_layout),
            );
            let mut packet = MemoryLayout::of::<()>();
            let mut offsets = vec![];
            for layout in layouts.iter().take(function.parameters as usize) {
                let (next, offset) = packet.extend(layout.memory).map_err(|error| {
                    LlvmError::InvalidNativeGraph(format!("tail packet: {error:?}"))
                })?;
                packet = next;
                offsets.push(offset as u64);
            }
            let mut init_offsets = vec![];
            for paths in paths.iter().take(function.parameters as usize) {
                let flags = MemoryLayout::new(paths.len(), 1)
                    .map_err(|_| unsupported(0, "invalid tail initialization sidecar"))?;
                let (next, offset) = packet
                    .extend(flags)
                    .map_err(|_| unsupported(0, "tail initialization sidecar overflow"))?;
                packet = next;
                init_offsets.push(offset as u64);
            }
            result.max_arguments = result.max_arguments.max(function.parameters as usize);
            result.packet_bytes = result
                .packet_bytes
                .max(packet.pad_to_alignment().size() as u64);
            result.packet_alignment = result.packet_alignment.max(packet.alignment() as u64);
            result.packet_offsets.push(offsets);
            result.packet_init_offsets.push(init_offsets);
            result.frame_bytes = result.frame_bytes.max(frame_bytes);
            if frame_bytes > MAX_FRAME_BYTES {
                return Err(unsupported(
                    0,
                    "native activation exceeds the 64 KiB initial stack-frame limit",
                ));
            }
            result.plans.push(FunctionPlan {
                layouts,
                paths,
                result: result_layout,
            });
        }
        // Validate every instruction before publishing any executable IR.
        for (index, key) in result.functions.iter().enumerate() {
            let mut body = Body::new(&result, index);
            for (pc, instruction) in program.functions[key].instructions.iter().enumerate() {
                if vm_functions.contains(key) {
                    // The user explicitly chose this bytecode body. Do not
                    // require a second native implementation of its local
                    // operations; continue to reject control whose dynamic
                    // destination could escape a synchronous engine boundary.
                    if matches!(
                        instruction,
                        I::Perform { .. }
                            | I::PerformOwned { .. }
                            | I::InstallHandler { .. }
                            | I::InstallHandlerOwned { .. }
                            | I::UninstallHandler
                            | I::CompleteHandler { .. }
                            | I::Resume { .. }
                            | I::ResumeReturn { .. }
                            | I::ResumeSnapshot { .. }
                            | I::MakeLabel { .. }
                            | I::CallIndirect { .. }
                            | I::CallIndirectOwned { .. }
                            | I::HostCall { .. }
                            | I::HostCallOwned { .. }
                    ) || matches!(instruction, I::MakeCallable { captures, environment, .. }
                            if !captures.is_empty() || environment.is_some())
                    {
                        return Err(LlvmError::Unsupported { function: *key, instruction: pc,
                            reason: "VM partition contains unsupported mixed control or external authority".into() });
                    }
                    continue;
                }
                body.pc = pc;
                body.instruction(instruction)?;
            }
        }
        Ok(result)
    }

    pub(super) fn layout_identity(&self) -> Digest {
        let mut bytes = b"grandiose-selected-native-layouts-v1".to_vec();
        for layout in self.layouts.values() {
            layout.identity_bytes(&mut bytes);
        }
        for function in self.program.functions.values() {
            for descriptor in &function.nominal_copy_descriptors {
                bytes.extend_from_slice(&descriptor.source_contract.as_bytes());
            }
        }
        Digest::of_bytes(&bytes)
    }

    pub(super) fn tail_packets(&self) -> Vec<super::TailPacketLayout> {
        self.packet_offsets
            .iter()
            .zip(&self.packet_init_offsets)
            .map(|(data, flags)| super::TailPacketLayout {
                data_offsets: data.iter().map(|offset| *offset as usize).collect(),
                initialization_offsets: flags.iter().map(|offset| *offset as usize).collect(),
            })
            .collect()
    }

    pub(super) fn emit(&self, descriptor: &LlvmAbiDescriptor) -> Result<String, LlvmError> {
        let mut ir = format!(
            "; LLVM-generated Glorious: verified scalar/control graph, no interpreter fallback.\nsource_filename = \"grandiose-native\"\ntarget triple = \"{}\"\ntarget datalayout = \"{}\"\n",
            descriptor.target.triple, descriptor.target.data_layout
        );
        writeln!(
            ir,
            "@g1_native_abi = constant [32 x i8] c\"{}\", align 1",
            descriptor
                .fingerprint()
                .as_bytes()
                .iter()
                .map(|byte| format!("\\{byte:02X}"))
                .collect::<String>()
        )
        .unwrap();
        // One immutable native allocation per source literal site. Omitting
        // unnamed_addr preserves site identity where raw addresses are observed.
        for (index, key) in self.functions.iter().enumerate() {
            if self.vm_functions.contains(key) { continue; }
            for (pc, instruction) in self.program.functions[key].instructions.iter().enumerate() {
                if let I::ConstStaticData { bytes, .. } = instruction {
                    let data = if bytes.is_empty() { "\\00".into() } else {
                        bytes.iter().map(|byte| format!("\\{byte:02X}")).collect::<String>()
                    };
                    writeln!(ir, "@g1_static_{index}_{pc} = private constant [{} x i8] c\"{data}\", align 1", bytes.len().max(1)).unwrap();
                }
            }
        }
        ir.push_str(include_str!("runtime.ll"));
        let mut declarations = BTreeSet::new();
        for index in 0..self.functions.len() {
            if self.vm_functions.contains(&self.functions[index]) {
                writeln!(ir, "define internal i32 @g1_body_{index}(ptr %ctx, ptr %args, ptr %result, ptr %tail_args, ptr %tail_storage, ptr %tail_next) {{\nentry:\n  %callback_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 10\n  %callback = load ptr, ptr %callback_at, align 8\n  %present = icmp ne ptr %callback, null\n  br i1 %present, label %invoke, label %reject\ninvoke:\n  %status = call i32 %callback(ptr %ctx, i32 {index}, ptr %args, ptr %result, ptr %tail_args, ptr %tail_storage, ptr %tail_next)\n  ret i32 %status\nreject:\n  %failed = call i32 @g1_fault(ptr %ctx, i32 7)\n  ret i32 %failed\n}}").unwrap();
                continue;
            }
            let mut body = Body::new(self, index);
            body.emit()?;
            ir.push_str(&body.output);
            declarations.extend(body.declarations);
        }
        for declaration in declarations {
            ir.push_str(&declaration);
            ir.push('\n');
        }
        self.dispatch(&mut ir);
        Ok(ir)
    }

    fn dispatch(&self, ir: &mut String) {
        let packet_bytes = self.packet_bytes.max(1);
        // Every argument is one data pointer plus one logical-initialization
        // sidecar pointer. Null sidecars mean completely initialized.
        let argc = 2 * self.max_arguments.max(1);
        let charge = 2 * packet_bytes + 3 * argc as u64 * 8 + self.frame_bytes + 160;
        let alignment = self.packet_alignment;
        writeln!(ir, r#"define internal i32 @g1_dispatch(ptr %ctx, i32 %function, ptr %args, ptr %result) {{
entry:
  %admitted = call i1 @g1_enter(ptr %ctx, i64 {charge})
  br i1 %admitted, label %allocate, label %rejected
rejected:
  ret i32 1
allocate:
  %packet0 = alloca [{packet_bytes} x i8], align {alignment}
  %packet1 = alloca [{packet_bytes} x i8], align {alignment}
  %args0 = alloca [{argc} x ptr], align 8
  %args1 = alloca [{argc} x ptr], align 8
  %next = alloca i32, align 4
  call void @g1_residents(ptr %ctx, i32 2, ptr null, ptr null, i64 0)
  call void @g1_residents(ptr %ctx, i32 4, ptr %packet0, ptr null, i64 {packet_bytes})
  call void @g1_residents(ptr %ctx, i32 4, ptr %packet1, ptr null, i64 {packet_bytes})
  br label %dispatch
dispatch:
  %selected = phi i32 [ %function, %allocate ], [ %next_function, %tail ]
  %incoming = phi ptr [ %args, %allocate ], [ %outgoing, %tail ]
  %outgoing = phi ptr [ %args0, %allocate ], [ %following_args, %tail ]
  %storage = phi ptr [ %packet0, %allocate ], [ %following_storage, %tail ]
  %second = phi i1 [ false, %allocate ], [ %next_second, %tail ]
  switch i32 %selected, label %invalid ["#).unwrap();
        for (index, _) in self.functions.iter().enumerate() {
            writeln!(ir, "    i32 {index}, label %function{index}").unwrap();
        }
        ir.push_str("  ]\n");
        for index in 0..self.functions.len() {
            writeln!(ir, "function{index}:\n  %status{index} = call i32 @g1_body_{index}(ptr %ctx, ptr %incoming, ptr %result, ptr %outgoing, ptr %storage, ptr %next)\n  br label %completed").unwrap();
        }
        ir.push_str("completed:\n  %status = phi i32 ");
        ir.push_str(
            &(0..self.functions.len())
                .map(|index| format!("[ %status{index}, %function{index} ]"))
                .collect::<Vec<_>>()
                .join(", "),
        );
        ir.push_str("\n  %is_tail = icmp eq i32 %status, 2\n  br i1 %is_tail, label %tail, label %return\ntail:\n  %next_function = load i32, ptr %next, align 4\n  %following_args = select i1 %second, ptr %args0, ptr %args1\n  %following_storage = select i1 %second, ptr %packet0, ptr %packet1\n  %next_second = xor i1 %second, true\n  call void @g1_tail_count(ptr %ctx)\n  br label %dispatch\nreturn:\n");
        writeln!(ir, "  call void @g1_residents(ptr %ctx, i32 3, ptr null, ptr null, i64 0)\n  call void @g1_exit(ptr %ctx, i64 {charge})\n  ret i32 %status\ninvalid:\n  %invalid_status = call i32 @g1_fault(ptr %ctx, i32 6)\n  call void @g1_residents(ptr %ctx, i32 3, ptr null, ptr null, i64 0)\n  call void @g1_exit(ptr %ctx, i64 {charge})\n  ret i32 %invalid_status\n}}").unwrap();
        for index in 0..self.functions.len() {
            writeln!(ir, "define i32 @g1_export_{index}(ptr %ctx, ptr %args, ptr %result) {{\nentry:\n  %status = call i32 @g1_dispatch(ptr %ctx, i32 {index}, ptr %args, ptr %result)\n  ret i32 %status\n}}").unwrap();
        }
    }
}

pub(super) fn collect_paths(
    layout: &NativeLayout,
    prefix: &mut Vec<u32>,
    paths: &mut BTreeSet<Vec<u32>>,
) -> Result<(), LlvmError> {
    paths.insert(prefix.clone());
    if paths.len() > MAX_INIT_PATHS {
        return Err(LlvmError::InvalidNativeGraph(
            "native resident tree exceeds the finite initialization-metadata limit".into(),
        ));
    }
    let mut visit = |fields: &NativeFields| -> Result<(), LlvmError> {
        if fields.len() > MAX_INIT_PATHS {
            return Err(LlvmError::InvalidNativeGraph(
                "native fixed-array initialization metadata exceeds the finite body limit".into(),
            ));
        }
        for (index, field) in fields.iter().enumerate() {
            prefix.push(index as u32);
            collect_paths(&field.layout, prefix, paths)?;
            prefix.pop();
        }
        Ok(())
    };
    match &layout.shape {
        NativeShape::Product(fields) => visit(fields)?,
        NativeShape::Enum { variants, .. } => {
            for fields in variants {
                visit(fields)?;
            }
        }
        _ => {}
    }
    Ok(())
}

pub(super) struct Body<'a, 'p> {
    plan: &'a Plan<'p>,
    index: usize,
    function: &'a VmFunction,
    data: &'a FunctionPlan,
    pc: usize,
    serial: u32,
    output: String,
    declarations: BTreeSet<String>,
}

impl<'a, 'p> Body<'a, 'p> {
    fn new(plan: &'a Plan<'p>, index: usize) -> Self {
        Self {
            plan,
            index,
            function: &plan.program.functions[&plan.functions[index]],
            data: &plan.plans[index],
            pc: 0,
            serial: 0,
            output: String::new(),
            declarations: BTreeSet::new(),
        }
    }
    fn unsupported(&self, reason: impl Into<String>) -> LlvmError {
        LlvmError::Unsupported {
            function: self.function.definition,
            instruction: self.pc,
            reason: reason.into(),
        }
    }
    fn line(&mut self, text: impl AsRef<str>) {
        writeln!(self.output, "  {}", text.as_ref()).unwrap();
    }
    fn value(&mut self, instruction: impl AsRef<str>) -> String {
        let name = format!("%v{}", self.serial);
        self.serial += 1;
        self.line(format!("{name} = {}", instruction.as_ref()));
        name
    }
    fn label(&mut self) -> String {
        let label = format!("branch{}", self.serial);
        self.serial += 1;
        label
    }
    fn block(&mut self, label: &str) {
        writeln!(self.output, "{label}:").unwrap();
    }
    fn guard(&mut self, condition: &str, fault: u32) {
        let ok = self.label();
        let failed = self.label();
        self.line(format!("br i1 {condition}, label %{ok}, label %{failed}"));
        self.block(&failed);
        let status = self.value(format!("call i32 @g1_fault(ptr %ctx, i32 {fault})"));
        self.line(format!("ret i32 {status}"));
        self.block(&ok);
    }
    fn pointer(&self, register: u32) -> String {
        format!("%r{register}")
    }
    fn load(&mut self, register: u32) -> Result<String, LlvmError> {
        let ty = layout::scalar_ir(&self.function.registers[register as usize])
            .ok_or_else(|| self.unsupported("scalar operation on a non-scalar resident"))?;
        let initialized = self.value(format!("load i8, ptr %init{register}, align 1"));
        let present = self.value(format!("icmp eq i8 {initialized}, 1"));
        self.guard(&present, 12);
        Ok(self.value(format!(
            "load {ty}, ptr %r{register}, align {}",
            self.data.layouts[register as usize].memory.alignment()
        )))
    }
    fn store_scalar(&mut self, register: u32, value: &str) -> Result<(), LlvmError> {
        let ty = layout::scalar_ir(&self.function.registers[register as usize])
            .ok_or_else(|| self.unsupported("scalar result has non-scalar layout"))?;
        self.line(format!(
            "store {ty} {value}, ptr %r{register}, align {}",
            self.data.layouts[register as usize].memory.alignment()
        ));
        self.mark(register, &[], true);
        Ok(())
    }
    fn flag(&mut self, register: u32, path: &[u32]) -> String {
        let index = self.data.paths[register as usize]
            .iter()
            .position(|candidate| candidate == path)
            .expect("planned resident path");
        self.value(format!(
            "getelementptr i8, ptr %init{register}, i64 {index}"
        ))
    }
    fn mark(&mut self, register: u32, path: &[u32], initialized: bool) {
        if !initialized && path.is_empty() && self.data.layouts[register as usize].owns_callable() {
            self.clear_bytes(&self.pointer(register), self.data.layouts[register as usize].memory.size());
        }
        let paths = self.data.paths[register as usize].clone();
        for (index, candidate) in paths
            .iter()
            .enumerate()
            .filter(|(_, candidate)| candidate.starts_with(path))
        {
            let _ = candidate;
            let pointer = self.value(format!(
                "getelementptr i8, ptr %init{register}, i64 {index}"
            ));
            self.line(format!(
                "store i8 {}, ptr {pointer}, align 1",
                u8::from(initialized)
            ));
        }
    }
    fn copy_flags(&mut self, dst: u32, src: u32, fields: &[u32]) {
        for (index, path) in self.data.paths[dst as usize].clone().iter().enumerate() {
            let source_path = fields.iter().chain(path).copied().collect::<Vec<_>>();
            let source = self.flag(src, &source_path);
            let value = self.value(format!("load i8, ptr {source}, align 1"));
            let destination = self.value(format!("getelementptr i8, ptr %init{dst}, i64 {index}"));
            self.line(format!("store i8 {value}, ptr {destination}, align 1"));
        }
    }
    fn copy_bytes(&mut self, dst: &str, src: &str, layout: &NativeLayout) {
        if layout.memory.size() != 0 {
            self.line(format!("call void @g1_residents(ptr %ctx, i32 0, ptr {dst}, ptr {src}, i64 {})", layout.memory.size()));
            self.line(format!(
                "call void @llvm.memmove.p0.p0.i64(ptr {dst}, ptr {src}, i64 {}, i1 false)",
                layout.memory.size()
            ));
        }
    }
    fn clear_bytes(&mut self, pointer: &str, bytes: usize) {
        self.line(format!("call void @g1_residents(ptr %ctx, i32 1, ptr {pointer}, ptr null, i64 {bytes})"));
    }
    fn track_bytes(&mut self, pointer: &str, bytes: usize) {
        self.line(format!("call void @g1_residents(ptr %ctx, i32 4, ptr {pointer}, ptr null, i64 {bytes})"));
    }
    fn checked_status(&mut self, status: &str) {
        let ok = self.value(format!("icmp eq i32 {status}, 0"));
        let next = self.label();
        let failed = self.label();
        self.line(format!("br i1 {ok}, label %{next}, label %{failed}"));
        self.block(&failed);
        self.line(format!("ret i32 {status}"));
        self.block(&next);
    }
    fn argument_slot(&mut self, index: usize, pointer: &str, flags: &str) {
        let slot = self.value(format!("getelementptr ptr, ptr %callargs, i64 {}", 2 * index));
        self.line(format!("store ptr {pointer}, ptr {slot}, align 8"));
        let slot = self.value(format!("getelementptr ptr, ptr %callargs, i64 {}", 2 * index + 1));
        self.line(format!("store ptr {flags}, ptr {slot}, align 8"));
    }
    fn callable_action(&mut self, operation: u32, register: u32, dst: &str) {
        let status = self.value(format!("call i32 @g1_callable(ptr %ctx, i32 {operation}, i32 {}, i32 {}, i32 {register}, ptr %callargs, ptr {dst})", self.index, self.pc));
        self.checked_status(&status);
    }
    fn copy_register(&mut self, dst: u32, src: u32, consume: bool) {
        if !consume && self.data.layouts[dst as usize].owns_callable() {
            self.argument_slot(0, &self.pointer(src), &format!("%init{src}"));
            self.callable_action(3, dst, &self.pointer(dst));
        } else {
            self.copy_bytes(&self.pointer(dst), &self.pointer(src), &self.data.layouts[dst as usize].clone());
        }
        self.copy_flags(dst, src, &[]);
        if consume {
            self.mark(src, &[], false);
        }
    }
    fn projection(
        &mut self,
        pointer: String,
        layout: Arc<NativeLayout>,
        fields: &[u32],
    ) -> Result<(String, Arc<NativeLayout>), LlvmError> {
        let Some((&first, rest)) = fields.split_first() else {
            return Ok((pointer, layout));
        };
        match &layout.shape {
            NativeShape::Product(items) => {
                let field = items
                    .get(first as usize)
                    .ok_or_else(|| self.unsupported("native field index has no selected layout"))?;
                let next = self.value(format!(
                    "getelementptr i8, ptr {pointer}, i64 {}",
                    field.offset
                ));
                self.projection(next, field.layout, rest)
            }
            NativeShape::Enum {
                payload_offset,
                variants,
            } => {
                let candidates = variants
                    .iter()
                    .filter_map(|items| items.get(first as usize))
                    .collect::<Vec<_>>();
                let field = candidates
                    .first()
                    .ok_or_else(|| self.unsupported("native enum field has no active payload"))?;
                if candidates.iter().any(|candidate| {
                    candidate.offset != field.offset || candidate.layout.ty != field.layout.ty
                }) {
                    return Err(self.unsupported(
                        "native enum projection requires unequal active-variant field layouts",
                    ));
                }
                let next = self.value(format!(
                    "getelementptr i8, ptr {pointer}, i64 {}",
                    payload_offset + field.offset
                ));
                self.projection(next, field.layout.clone(), rest)
            }
            _ => Err(self.unsupported("native projection does not name a structural resident")),
        }
    }

    /// The portable verifier admits any statically matching variant, while
    /// execution checks the actual discriminant before selecting its payload.
    /// Never choose an arbitrary same-index layout or bitcast a different type.
    fn typed_projection(
        &mut self,
        pointer: String,
        layout: Arc<NativeLayout>,
        fields: &[u32],
        expected: &VmType,
        field_count: Option<u32>,
    ) -> Result<String, LlvmError> {
        fn admits(layout: &NativeLayout, fields: &[u32], expected: &VmType) -> bool {
            let Some((&first, rest)) = fields.split_first() else { return &layout.ty == expected; };
            match &layout.shape {
                NativeShape::Product(items) => items.get(first as usize).is_some_and(|field| admits(&field.layout, rest, expected)),
                NativeShape::Enum { variants, .. } => variants.iter().any(|items|
                    items.get(first as usize).is_some_and(|field| admits(&field.layout, rest, expected))),
                _ => false,
            }
        }
        let Some((&first, rest)) = fields.split_first() else {
            return if &layout.ty == expected { Ok(pointer) }
                else { Err(self.unsupported("native projection result has a different concrete layout")) };
        };
        match &layout.shape {
            NativeShape::Product(items) => {
                if field_count.is_some_and(|count| count as usize != items.len()) {
                    return Err(self.unsupported("native projection field count differs from the concrete product"));
                }
                let field = items.get(first as usize)
                    .ok_or_else(|| self.unsupported("native projection index is outside its product"))?;
                let next = self.value(format!("getelementptr i8, ptr {pointer}, i64 {}", field.offset));
                self.typed_projection(next, field.layout, rest, expected, None)
            }
            NativeShape::Enum { payload_offset, variants } => {
                let alternatives = variants.iter().enumerate().filter_map(|(tag, items)| {
                    if field_count.is_some_and(|count| count as usize != items.len()) { return None; }
                    let field = items.get(first as usize)?;
                    admits(&field.layout, rest, expected).then_some((tag, field))
                }).collect::<Vec<_>>();
                if alternatives.is_empty() { return Err(self.unsupported("native enum has no variant matching the exact projection type")); }
                let tag = self.value(format!("load i32, ptr {pointer}, align 4"));
                let rejected = self.label();
                let join = self.label();
                let branches = alternatives.iter().map(|_| self.label()).collect::<Vec<_>>();
                self.line(format!("switch i32 {tag}, label %{rejected} ["));
                for ((tag, _), branch) in alternatives.iter().zip(&branches) {
                    self.line(format!("  i32 {tag}, label %{branch}"));
                }
                self.line("]");
                self.block(&rejected);
                let failure = self.value("call i32 @g1_fault(ptr %ctx, i32 14)");
                self.line(format!("ret i32 {failure}"));
                let mut incoming = Vec::new();
                for ((_, field), branch) in alternatives.into_iter().zip(branches) {
                    self.block(&branch);
                    let next = self.value(format!("getelementptr i8, ptr {pointer}, i64 {}", payload_offset + field.offset));
                    let selected = self.typed_projection(next, field.layout, rest, expected, None)?;
                    let end = self.label();
                    self.line(format!("br label %{end}"));
                    self.block(&end);
                    self.line(format!("br label %{join}"));
                    incoming.push(format!("[ {selected}, %{end} ]"));
                }
                self.block(&join);
                Ok(self.value(format!("phi ptr {}", incoming.join(", "))))
            }
            _ => Err(self.unsupported("native projection requires a structural resident")),
        }
    }

    fn emit(&mut self) -> Result<(), LlvmError> {
        writeln!(self.output, "define internal i32 @g1_body_{}(ptr %ctx, ptr %args, ptr %result, ptr %tail_args, ptr %tail_storage, ptr %tail_next) {{\nentry:\n  call void @g1_residents(ptr %ctx, i32 2, ptr null, ptr null, i64 0)\n  %status = call i32 @g1_frame_{}(ptr %ctx, ptr %args, ptr %result, ptr %tail_args, ptr %tail_storage, ptr %tail_next)\n  call void @g1_residents(ptr %ctx, i32 3, ptr null, ptr null, i64 0)\n  ret i32 %status\n}}\ndefine internal i32 @g1_frame_{}(ptr %ctx, ptr %args, ptr %result, ptr %tail_args, ptr %tail_storage, ptr %tail_next) {{\nentry:", self.index, self.index, self.index).unwrap();
        let maxargs = 2 * (self.plan.max_arguments + 1).max(1);
        self.line(format!("%callargs = alloca [{maxargs} x ptr], align 8"));
        for (pc, instruction) in self.function.instructions.iter().enumerate() {
            if let I::Leave { arguments, .. } = instruction {
                for (index, argument) in arguments.iter().enumerate() {
                    let layout = &self.data.layouts[*argument as usize];
                    self.line(format!(
                        "%leave_{pc}_{index} = alloca [{} x i8], align {}",
                        layout.memory.size().max(1),
                        layout.memory.alignment()
                    ));
                    self.line(format!("%leave_init_{pc}_{index} = alloca [{} x i8], align 1",
                        self.data.paths[*argument as usize].len()));
                    if layout.owns_callable() {
                        self.track_bytes(&format!("%leave_{pc}_{index}"), layout.memory.size());
                    }
                }
            }
        }
        for (register, layout) in self.data.layouts.iter().enumerate() {
            let capture = register < self.function.captures as usize;
            let alias_argument = capture || (register < self.function.parameters as usize
                && matches!(
                    self.function.registers[register],
                    VmType::Tuple(_) | VmType::FixedArray { .. } | VmType::Nominal { .. } | VmType::Callable { .. }
                ));
            if alias_argument {
                let slot = self.value(format!(
                    "getelementptr ptr, ptr %args, i64 {}",
                    2 * register
                ));
                self.line(format!("%r{register} = load ptr, ptr {slot}, align 8"));
            } else {
                self.line(format!(
                    "%r{register} = alloca [{} x i8], align {}",
                    layout.memory.size().max(1),
                    layout.memory.alignment()
                ));
            }
            if !capture && layout.owns_callable() {
                self.track_bytes(&format!("%r{register}"), layout.memory.size());
            }
            if capture {
                let slot = self.value(format!("getelementptr ptr, ptr %args, i64 {}", 2 * register + 1));
                self.line(format!("%init{register} = load ptr, ptr {slot}, align 8"));
            } else {
                self.line(format!("%init{register} = alloca [{} x i8], align 1", self.data.paths[register].len()));
                self.mark(register as u32, &[], register < self.function.parameters as usize);
            }
            if register < self.function.parameters as usize && !alias_argument {
                let slot = self.value(format!(
                    "getelementptr ptr, ptr %args, i64 {}",
                    2 * register
                ));
                let pointer = self.value(format!("load ptr, ptr {slot}, align 8"));
                self.copy_bytes(&format!("%r{register}"), &pointer, layout);
            }
            if register < self.function.parameters as usize && !capture {
                let slot = self.value(format!(
                    "getelementptr ptr, ptr %args, i64 {}",
                    2 * register + 1
                ));
                let flags = self.value(format!("load ptr, ptr {slot}, align 8"));
                let supplied = self.value(format!("icmp ne ptr {flags}, null"));
                let copy = self.label();
                let ready = self.label();
                self.line(format!("br i1 {supplied}, label %{copy}, label %{ready}"));
                self.block(&copy);
                self.line(format!("call void @llvm.memmove.p0.p0.i64(ptr %init{register}, ptr {flags}, i64 {}, i1 false)", self.data.paths[register].len()));
                self.line(format!("br label %{ready}"));
                self.block(&ready);
            }
        }
        self.line("br label %pc0");
        for (pc, instruction) in self.function.instructions.iter().enumerate() {
            self.pc = pc;
            self.block(&format!("pc{pc}"));
            let allowed = self.value("call i1 @g1_step(ptr %ctx)");
            self.guard(&allowed, 3);
            let terminal = self.instruction(instruction)?;
            if !terminal {
                if pc + 1 >= self.function.instructions.len() {
                    return Err(self.unsupported("native instruction falls off its function"));
                }
                self.line(format!("br label %pc{}", pc + 1));
            }
        }
        self.output.push_str("}\n");
        Ok(())
    }

    fn instruction(&mut self, instruction: &I) -> Result<bool, LlvmError> {
        if self.scalar(instruction)? {
            return Ok(false);
        }
        match instruction {
            I::MemoryIntrinsic {
                dst,
                primitive,
                types,
                arguments,
            } => {
                self.memory(*dst, *primitive, types, arguments)?;
            }
            I::DeclareResult { .. } | I::DeclareFrameCleanup { .. } => {}
            I::ConstUnit { dst } => self.mark(*dst, &[], true),
            I::ConstStaticData { dst, bytes, .. } => {
                self.line(format!("store ptr @g1_static_{}_{}, ptr %r{dst}, align 8", self.index, self.pc));
                let length_slot = self.value(format!("getelementptr i8, ptr %r{dst}, i64 8"));
                self.line(format!("store i64 {}, ptr {length_slot}, align 8", bytes.len()));
                self.mark(*dst, &[], true);
            }
            I::StaticLen { dst, value } => {
                let length = self.static_data_word(*value, true);
                self.store_scalar(*dst, &length)?;
            }
            I::MakeCallable { dst, captures, environment, .. } => {
                for (index, capture) in captures.iter().enumerate() {
                    self.argument_slot(index, &self.pointer(*capture), &format!("%init{capture}"));
                }
                self.callable_action(0, *dst, &self.pointer(*dst));
                for (index, capture) in captures.iter().enumerate() {
                    if environment.as_ref().is_some_and(|environment| matches!(environment.captures[index].mode,
                        crate::vm_backend::VmCaptureMode::Copy | crate::vm_backend::VmCaptureMode::Move)) {
                        self.mark(*capture, &[], false);
                    }
                }
                self.mark(*dst, &[], true);
            }
            I::DestroyCallable { dst, value } => {
                self.argument_slot(0, &self.pointer(*value), &format!("%init{value}"));
                self.callable_action(2, *value, &self.pointer(*dst));
                self.mark(*value, &[], false);
                self.mark(*dst, &[], true);
            }
            I::CallIndirect { dst, callee, arguments } | I::CallIndirectOwned { dst, callee, arguments } => {
                self.argument_slot(0, &self.pointer(*callee), &format!("%init{callee}"));
                for (index, argument) in arguments.iter().enumerate() {
                    self.argument_slot(index + 1, &self.pointer(*argument), &format!("%init{argument}"));
                }
                self.callable_action(1, *callee, &self.pointer(*dst));
                if matches!(instruction, I::CallIndirectOwned { .. }) {
                    for argument in arguments { self.mark(*argument, &[], false); }
                }
                self.mark(*dst, &[], true);
            }
            I::StorageLive { local, .. } | I::StorageDead { local, .. } => {
                self.mark(*local, &[], false)
            }
            I::SetDropFlag { flag, value } => {
                self.store_scalar(*flag, if *value { "1" } else { "0" })?
            }
            I::DestroyIf { local, flag } => {
                let flag = self.load(*flag)?;
                let condition = self.value(format!("icmp ne i8 {flag}, 0"));
                let destroy = self.label();
                let done = self.label();
                self.line(format!(
                    "br i1 {condition}, label %{destroy}, label %{done}"
                ));
                self.block(&destroy);
                self.mark(*local, &[], false);
                self.line(format!("br label %{done}"));
                self.block(&done);
            }
            I::Copy { dst, src } | I::Store { dst, src } => self.copy_register(*dst, *src, false),
            I::Move { dst, src } | I::StoreOwned { dst, src } => {
                self.copy_register(*dst, *src, true)
            }
            I::StoreUsize { dst, value } => self.copy_register(*dst, *value, false),
            I::ArrayLen { dst, value } => {
                let VmType::FixedArray { length, .. } = &self.function.registers[*value as usize]
                else {
                    return Err(
                        self.unsupported("native array extent requires a fixed-array resident")
                    );
                };
                self.store_scalar(*dst, &length.to_string())?;
            }
            I::ArrayElementIsInitialized { dst, value, index }
            | I::TakeArrayElement { dst, value, index } => {
                let VmType::FixedArray { element, length } =
                    &self.function.registers[*value as usize]
                else {
                    return Err(
                        self.unsupported("native indexed storage requires a fixed-array resident")
                    );
                };
                let element = layout::concrete_layout(
                    element,
                    &self.function.nominal_copy_descriptors.clone().into(),
                )?;
                let length = *length;
                let index = self.load(*index)?;
                let in_bounds = self.value(format!("icmp ult i64 {index}, {length}"));
                let fault_register =
                    self.value("getelementptr %G1Context, ptr %ctx, i32 0, i32 14");
                self.line(format!("store i32 {value}, ptr {fault_register}, align 4"));
                self.guard(&in_bounds, 11);
                let width = if length == 0 {
                    1
                } else {
                    (self.data.paths[*value as usize].len() - 1) / length as usize
                };
                let offset = self.value(format!("mul i64 {index}, {width}"));
                let first = self.value(format!("add i64 {offset}, 1"));
                let flags = self.value(format!("getelementptr i8, ptr %init{value}, i64 {first}"));
                if matches!(instruction, I::ArrayElementIsInitialized { .. }) {
                    let initialized = self.value(format!("load i8, ptr {flags}, align 1"));
                    self.store_scalar(*dst, &initialized)?;
                } else {
                    let initialized = self.value(format!("load i8, ptr {flags}, align 1"));
                    let present = self.value(format!("icmp ne i8 {initialized}, 0"));
                    self.guard(&present, 12);
                    let byte_offset = self.value(format!(
                        "mul i64 {index}, {}",
                        element.memory.pad_to_alignment().size()
                    ));
                    let source = self.value(format!(
                        "getelementptr i8, ptr %r{value}, i64 {byte_offset}"
                    ));
                    self.copy_bytes(&self.pointer(*dst), &source, &element);
                    if element.owns_callable() { self.clear_bytes(&source, element.memory.size()); }
                    for flag in 0..width {
                        let source =
                            self.value(format!("getelementptr i8, ptr {flags}, i64 {flag}"));
                        let initialized = self.value(format!("load i8, ptr {source}, align 1"));
                        let destination =
                            self.value(format!("getelementptr i8, ptr %init{dst}, i64 {flag}"));
                        self.line(format!(
                            "store i8 {initialized}, ptr {destination}, align 1"
                        ));
                        self.line(format!("store i8 0, ptr {source}, align 1"));
                    }
                }
            }
            I::IsInitialized { dst, base, fields } => {
                let flag = self.flag(*base, fields);
                let value = self.value(format!("load i8, ptr {flag}, align 1"));
                self.store_scalar(*dst, &value)?;
            }
            I::Borrow {
                dst,
                src,
                fields,
                reborrow,
                ..
            } => {
                let (pointer, layout) = if *reborrow {
                    let VmType::Reference { referent, .. } =
                        &self.function.registers[*src as usize]
                    else {
                        return Err(self.unsupported("native reborrow lacks a reference source"));
                    };
                    let layout = layout::concrete_layout(
                        referent,
                        &self.function.nominal_copy_descriptors.clone().into(),
                    )?;
                    (self.load(*src)?, layout)
                } else {
                    (self.pointer(*src), self.data.layouts[*src as usize].clone())
                };
                let VmType::Reference { referent, .. } = &self.function.registers[*dst as usize] else {
                    return Err(self.unsupported("native borrow destination has no reference layout"));
                };
                let pointer = self.typed_projection(pointer, layout, fields, referent, None)?;
                self.store_scalar(*dst, &pointer)?;
            }
            I::DerefCopy { dst, reference } => {
                let pointer = self.load(*reference)?;
                self.copy_bytes(&self.pointer(*dst), &pointer, &self.data.layouts[*dst as usize].clone());
                self.mark(*dst, &[], true);
            }
            I::DerefStore { reference, src } => {
                let pointer = self.load(*reference)?;
                self.copy_bytes(
                    &pointer,
                    &self.pointer(*src),
                    &self.data.layouts[*src as usize].clone(),
                );
            }
            I::ProjectRecord {
                dst, base, index, field_count, ..
            }
            | I::ProjectTuple {
                dst, base, index, field_count, ..
            }
            | I::ProjectArray {
                dst, base, index, field_count, ..
            } => {
                let layout = self.data.layouts[*dst as usize].clone();
                let pointer = self.typed_projection(
                    self.pointer(*base),
                    self.data.layouts[*base as usize].clone(),
                    &[*index],
                    &layout.ty,
                    Some(*field_count),
                )?;
                self.copy_bytes(&self.pointer(*dst), &pointer, &layout);
                self.copy_flags(*dst, *base, &[*index]);
            }
            I::TakeProjection { dst, base, fields } => {
                let layout = self.data.layouts[*dst as usize].clone();
                let pointer = self.typed_projection(
                    self.pointer(*base),
                    self.data.layouts[*base as usize].clone(),
                    fields,
                    &layout.ty,
                    None,
                )?;
                self.copy_bytes(&self.pointer(*dst), &pointer, &layout);
                self.copy_flags(*dst, *base, fields);
                if layout.owns_callable() { self.clear_bytes(&pointer, layout.memory.size()); }
                self.mark(*base, fields, false);
            }
            I::MakeTuple { dst, fields }
            | I::MakeTupleOwned { dst, fields }
            | I::MakeArray { dst, fields, .. }
            | I::MakeArrayOwned { dst, fields, .. }
            | I::MakeRecord { dst, fields, .. }
            | I::MakeRecordOwned { dst, fields, .. }
            | I::MakeEnum { dst, fields, .. }
            | I::MakeEnumOwned { dst, fields, .. } => {
                let layout = self.data.layouts[*dst as usize].clone();
                if layout.owns_callable() { self.clear_bytes(&self.pointer(*dst), layout.memory.size()); }
                let (offset, items) = match (&layout.shape, instruction) {
                    (NativeShape::Product(items), _) => (0, items.clone()),
                    (
                        NativeShape::Enum {
                            payload_offset,
                            variants,
                        },
                        I::MakeEnum { variant, .. } | I::MakeEnumOwned { variant, .. },
                    ) => {
                        self.line(format!("store i32 {variant}, ptr %r{dst}, align 4"));
                        (*payload_offset, variants[*variant as usize].clone())
                    }
                    _ => {
                        return Err(
                            self.unsupported("native constructor has no exact structural layout")
                        );
                    }
                };
                for (source, field) in fields.iter().zip(items.iter()) {
                    let target = self.value(format!(
                        "getelementptr i8, ptr %r{dst}, i64 {}",
                        offset + field.offset
                    ));
                    self.copy_bytes(&target, &self.pointer(*source), &field.layout);
                }
                self.mark(*dst, &[], true);
                if let Some(consumed) = instruction.consumed_arguments() {
                    for source in consumed {
                        self.mark(*source, &[], false);
                    }
                }
            }
            I::PatternTest {
                dst,
                subject,
                pattern,
            } => {
                let matched = self.pattern(
                    self.pointer(*subject),
                    self.data.layouts[*subject as usize].clone(),
                    pattern,
                )?;
                let value = self.value(format!("zext i1 {matched} to i8"));
                self.store_scalar(*dst, &value)?;
            }
            I::CallOwned {
                dst,
                callee,
                arguments,
            }
            | I::Call {
                dst,
                callee,
                arguments,
            } => {
                if matches!(instruction, I::Call { .. })
                    && arguments.iter().any(|argument| {
                        matches!(
                            self.function.registers[*argument as usize],
                            VmType::Tuple(_) | VmType::FixedArray { .. } | VmType::Nominal { .. }
                        )
                    })
                {
                    return Err(self.unsupported(
                        "native aggregate parameters require an explicit owned call",
                    ));
                }
                let index = self
                    .plan
                    .functions
                    .iter()
                    .position(|key| key == callee)
                    .ok_or_else(|| self.unsupported("native direct callee is absent"))?;
                for (index, argument) in arguments.iter().enumerate() {
                    let slot = self.value(format!(
                        "getelementptr ptr, ptr %callargs, i64 {}",
                        2 * index
                    ));
                    self.line(format!("store ptr %r{argument}, ptr {slot}, align 8"));
                    let slot = self.value(format!(
                        "getelementptr ptr, ptr %callargs, i64 {}",
                        2 * index + 1
                    ));
                    self.line(format!("store ptr %init{argument}, ptr {slot}, align 8"));
                }
                let status = self.value(format!(
                    "call i32 @g1_dispatch(ptr %ctx, i32 {index}, ptr %callargs, ptr %r{dst})"
                ));
                let ok = self.value(format!("icmp eq i32 {status}, 0"));
                let next = self.label();
                let failed = self.label();
                self.line(format!("br i1 {ok}, label %{next}, label %{failed}"));
                self.block(&failed);
                self.line(format!("ret i32 {status}"));
                self.block(&next);
                self.mark(*dst, &[], true);
                if matches!(instruction, I::CallOwned { .. }) {
                    for argument in arguments {
                        self.mark(*argument, &[], false);
                    }
                }
            }
            I::TailCallOwned { callee, arguments } => {
                let target = self
                    .plan
                    .functions
                    .iter()
                    .position(|key| key == callee)
                    .ok_or_else(|| self.unsupported("native tail callee is absent"))?;
                for (index, argument) in arguments.iter().enumerate() {
                    let pointer = self.value(format!(
                        "getelementptr i8, ptr %tail_storage, i64 {}",
                        self.plan.packet_offsets[target][index]
                    ));
                    self.copy_bytes(
                        &pointer,
                        &self.pointer(*argument),
                        &self.data.layouts[*argument as usize].clone(),
                    );
                    let slot = self.value(format!(
                        "getelementptr ptr, ptr %tail_args, i64 {}",
                        2 * index
                    ));
                    self.line(format!("store ptr {pointer}, ptr {slot}, align 8"));
                    let flags = self.value(format!(
                        "getelementptr i8, ptr %tail_storage, i64 {}",
                        self.plan.packet_init_offsets[target][index]
                    ));
                    self.line(format!("call void @llvm.memmove.p0.p0.i64(ptr {flags}, ptr %init{argument}, i64 {}, i1 false)", self.data.paths[*argument as usize].len()));
                    let slot = self.value(format!(
                        "getelementptr ptr, ptr %tail_args, i64 {}",
                        2 * index + 1
                    ));
                    self.line(format!("store ptr {flags}, ptr {slot}, align 8"));
                }
                self.line(format!("store i32 {target}, ptr %tail_next, align 4"));
                self.line("ret i32 2");
                return Ok(true);
            }
            I::Leave {
                handler_depth: 0,
                target,
                arguments,
                destinations,
                ..
            } => {
                // Prepare every carrier before writing block parameters.
                for (index, argument) in arguments.iter().enumerate() {
                    let layout = self.data.layouts[*argument as usize].clone();
                    let temporary = format!("%leave_{}_{}", self.pc, index);
                    self.copy_bytes(&temporary, &self.pointer(*argument), &layout);
                    self.line(format!("call void @llvm.memmove.p0.p0.i64(ptr %leave_init_{}_{index}, ptr %init{argument}, i64 {}, i1 false)",
                        self.pc, self.data.paths[*argument as usize].len()));
                }
                for argument in arguments { self.mark(*argument, &[], false); }
                for (index, destination) in destinations.iter().enumerate() {
                    self.copy_bytes(
                        &self.pointer(*destination),
                        &format!("%leave_{}_{}", self.pc, index),
                        &self.data.layouts[*destination as usize].clone(),
                    );
                    self.line(format!("call void @llvm.memmove.p0.p0.i64(ptr %init{destination}, ptr %leave_init_{}_{index}, i64 {}, i1 false)",
                        self.pc, self.data.paths[*destination as usize].len()));
                }
                self.line(format!("br label %pc{target}"));
                return Ok(true);
            }
            I::Jump { target } => {
                self.line(format!("br label %pc{target}"));
                return Ok(true);
            }
            I::BranchBool {
                condition,
                then_target,
                else_target,
            } => {
                let value = self.load(*condition)?;
                let condition = self.value(format!("icmp ne i8 {value}, 0"));
                self.line(format!(
                    "br i1 {condition}, label %pc{then_target}, label %pc{else_target}"
                ));
                return Ok(true);
            }
            I::Return { value } => {
                // The ordinary result slot is a complete source value. A
                // partial owner belongs only to compiler cleanup arguments;
                // never silently relabel its holes as an initialized result.
                let mut initialized = "true".to_owned();
                for index in 0..self.data.paths[*value as usize].len() {
                    let flag =
                        self.value(format!("getelementptr i8, ptr %init{value}, i64 {index}"));
                    let flag = self.value(format!("load i8, ptr {flag}, align 1"));
                    let present = self.value(format!("icmp eq i8 {flag}, 1"));
                    initialized = self.value(format!("and i1 {initialized}, {present}"));
                }
                self.guard(&initialized, 13);
                self.copy_bytes("%result", &self.pointer(*value), &self.data.result.clone());
                self.line("ret i32 0");
                return Ok(true);
            }
            I::Trap => {
                let status = self.value("call i32 @g1_fault(ptr %ctx, i32 6)");
                self.line(format!("ret i32 {status}"));
                return Ok(true);
            }
            _ => {
                return Err(self.unsupported(format!(
                    "native instruction/control contract is not implemented: {instruction:?}"
                )));
            }
        }
        Ok(false)
    }

    fn pattern(
        &mut self,
        pointer: String,
        layout: Arc<NativeLayout>,
        pattern: &VmPattern,
    ) -> Result<String, LlvmError> {
        if !matches!(pattern, VmPattern::Any)
            && let NativeShape::Reference {
                referent,
                descriptors,
                ..
            } = &layout.shape
        {
            let target = layout::concrete_layout(referent, descriptors)?;
            let pointer = self.value(format!("load ptr, ptr {pointer}, align 8"));
            return self.pattern(pointer, target, pattern);
        }
        match pattern {
            VmPattern::Any => Ok("true".into()),
            VmPattern::Literal(value) => {
                let ty = layout::scalar_ir(&layout.ty).ok_or_else(|| {
                    self.unsupported("native literal pattern has unsupported type")
                })?;
                let literal = match (&layout.ty, value.as_str()) {
                    (VmType::Bool, "true") => "1".into(),
                    (VmType::Bool, "false") => "0".into(),
                    _ => value.replace('_', ""),
                };
                if !matches!(ty, "i8" | "i16" | "i32" | "i64" | "i128")
                    || (literal.parse::<i128>().is_err() && literal.parse::<u128>().is_err())
                {
                    return Err(
                        self.unsupported("native non-integer literal pattern is not implemented")
                    );
                }
                let loaded = self.value(format!(
                    "load {ty}, ptr {pointer}, align {}",
                    layout.memory.alignment()
                ));
                Ok(self.value(format!("icmp eq {ty} {loaded}, {literal}")))
            }
            VmPattern::Tuple(patterns) => {
                let mut matched = "true".to_owned();
                for (index, pattern) in patterns.iter().enumerate() {
                    let (field, layout) =
                        self.projection(pointer.clone(), layout.clone(), &[index as u32])?;
                    let item = self.pattern(field, layout, pattern)?;
                    matched = self.value(format!("and i1 {matched}, {item}"));
                }
                Ok(matched)
            }
            VmPattern::Array { elements, rest, .. } => {
                let NativeShape::Product(fields) = &layout.shape else {
                    return Err(
                        self.unsupported("native array pattern requires a fixed-array layout")
                    );
                };
                if crate::pattern::ArrayPatternRest::length(*rest, elements.len())
                    != Some(fields.len())
                {
                    return Ok("false".into());
                }
                let mut matched = "true".to_owned();
                for (index, pattern) in elements.iter().enumerate() {
                    let index = crate::pattern::ArrayPatternRest::index(*rest, index);
                    let (field, layout) =
                        self.projection(pointer.clone(), layout.clone(), &[index as u32])?;
                    let item = self.pattern(field, layout, pattern)?;
                    matched = self.value(format!("and i1 {matched}, {item}"));
                }
                Ok(matched)
            }
            VmPattern::Record { fields, .. } => {
                let mut matched = "true".to_owned();
                for field in fields {
                    let (pointer, layout) =
                        self.projection(pointer.clone(), layout.clone(), &[field.index])?;
                    let item = self.pattern(pointer, layout, &field.pattern)?;
                    matched = self.value(format!("and i1 {matched}, {item}"));
                }
                Ok(matched)
            }
            VmPattern::Enum {
                variant, fields, ..
            } => {
                let NativeShape::Enum {
                    payload_offset,
                    variants,
                } = &layout.shape
                else {
                    return Err(self.unsupported("native enum pattern has a non-enum layout"));
                };
                let active = variants[*variant as usize].clone();
                let offset = *payload_offset;
                let tag = self.value(format!("load i32, ptr {pointer}, align 4"));
                let correct = self.value(format!("icmp eq i32 {tag}, {variant}"));
                let yes = self.label();
                let no = self.label();
                let join = self.label();
                let matched_end = self.label();
                self.line(format!("br i1 {correct}, label %{yes}, label %{no}"));
                self.block(&no);
                self.line(format!("br label %{join}"));
                self.block(&yes);
                let mut matched = "true".to_owned();
                for field in fields {
                    let field_layout = active
                        .get(field.index as usize)
                        .expect("verified pattern field");
                    let field_pointer = self.value(format!(
                        "getelementptr i8, ptr {pointer}, i64 {}",
                        offset + field_layout.offset
                    ));
                    let item = self.pattern(field_pointer, field_layout.layout, &field.pattern)?;
                    matched = self.value(format!("and i1 {matched}, {item}"));
                }
                self.line(format!("br label %{matched_end}"));
                self.block(&matched_end);
                self.line(format!("br label %{join}"));
                self.block(&join);
                Ok(self.value(format!(
                    "phi i1 [ false, %{no} ], [ {matched}, %{matched_end} ]"
                )))
            }
        }
    }
}
