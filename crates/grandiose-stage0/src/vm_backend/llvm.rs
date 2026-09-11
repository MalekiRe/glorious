//! LLVM-generated Glorious code over the verified, concrete VM-LIR contract.
//!
//! This is a second execution engine, not a Rust compiler setting and not an
//! interpreter wrapper. Admission is whole-graph and fail-closed. Unsupported
//! control must never become an ordinary native call by accident.

mod emit;
pub(super) mod callables;
mod layout;
mod load;
mod execution;
pub(super) mod memory;

use super::{
    CandidateVmProgram, DefKey, Digest, VerifiedVmProgram, VmArtifactError, VmExecutionLimits,
    VmNativeAbi, VmType,
};
use crate::{CompilationRequest, StageZeroCompiler};
use std::collections::{BTreeMap, BTreeSet};

pub use layout::{LlvmTarget, NativeTypeLayout, NativeTypeShape};
pub use load::{LlvmCompileOptions, LlvmNativeModule};

/// New native-module format. It is independent of portable bytecode encoding.
pub const LLVM_NATIVE_ABI_GENERATION: u32 = 19;
pub const LLVM_CONTROL_CONVENTION: &str = "grandiose:shared-resumable-frames-v1";
/// Initial stack-backed native activations impose this additional explicit
/// resident-storage ceiling until the shared heap-frame convention is enabled.
pub const LLVM_NATIVE_STACK_BYTES: u64 = 1024 * 1024;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmAbiDescriptor {
    pub generation: u32,
    pub target: LlvmTarget,
    pub layout_identity: Digest,
    pub source_identity: Digest,
    pub code_identity: Digest,
    pub execution_partition: Digest,
    pub runtime_manifest: Option<Digest>,
    pub control_convention: String,
    pub allocation_domain: String,
}

impl LlvmAbiDescriptor {
    pub fn fingerprint(&self) -> Digest {
        // No host pointers enter this identity. Length-prefixed strings keep
        // independent descriptor fields from sharing an ambiguous encoding.
        let mut bytes = b"grandiose-llvm-native-abi-v1".to_vec();
        bytes.extend_from_slice(&self.generation.to_le_bytes());
        for value in [
            &self.target.triple,
            &self.target.data_layout,
            &self.control_convention,
            &self.allocation_domain,
        ] {
            bytes.extend_from_slice(&(value.len() as u64).to_le_bytes());
            bytes.extend_from_slice(value.as_bytes());
        }
        bytes.extend_from_slice(&self.target.pointer_bits.to_le_bytes());
        bytes.push(u8::from(self.target.little_endian));
        for digest in [
            self.layout_identity,
            self.source_identity,
            self.code_identity,
            self.execution_partition,
        ] {
            bytes.extend_from_slice(&digest.as_bytes());
        }
        bytes.push(u8::from(self.runtime_manifest.is_some()));
        if let Some(digest) = self.runtime_manifest {
            bytes.extend_from_slice(&digest.as_bytes());
        }
        Digest::of_bytes(&bytes)
    }
}

#[derive(Debug)]
pub enum LlvmError {
    Source(crate::ServiceError),
    InvalidInput(crate::InputError),
    VerifiedCode(VmArtifactError),
    UnsupportedTarget(String),
    Unsupported {
        function: DefKey,
        instruction: usize,
        reason: String,
    },
    AbiMismatch(&'static str),
    InvalidNativeGraph(String),
    Tool(String),
    Io(std::io::Error),
    Runtime(VmArtifactError),
}

impl std::fmt::Display for LlvmError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}
impl std::error::Error for LlvmError {}
impl From<std::io::Error> for LlvmError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}
impl From<VmArtifactError> for LlvmError {
    fn from(error: VmArtifactError) -> Self {
        Self::VerifiedCode(error)
    }
}

/// A compiler-produced native plan. IR and its exact ABI witness are immutable
/// together; loading an unrelated shared object is not an API on this type.
#[derive(Clone, Debug)]
pub struct LlvmIrProgram {
    pub(super) program: VerifiedVmProgram,
    descriptor: LlvmAbiDescriptor,
    ir: String,
    layouts: BTreeMap<Vec<u8>, NativeTypeLayout>,
    pub(super) functions: Vec<DefKey>,
    pub(super) vm_functions: BTreeSet<DefKey>,
    pub(super) frame_layouts: std::sync::Arc<[emit::FunctionPlan]>,
}

impl LlvmIrProgram {
    pub fn ir(&self) -> &str {
        &self.ir
    }
    pub fn abi(&self) -> &LlvmAbiDescriptor {
        &self.descriptor
    }
    pub fn vm_program(&self) -> &VerifiedVmProgram {
        &self.program
    }
    pub fn layout_of(&self, ty: &VmType) -> Option<&NativeTypeLayout> {
        self.layouts.get(&layout::type_key(ty))
    }
    pub fn function_keys(&self) -> &[DefKey] {
        &self.functions
    }
    pub fn entry_key(&self) -> DefKey {
        self.program.program.entry
    }

    pub fn function(&self, key: DefKey) -> Option<&super::VmFunction> {
        self.program.program.functions.get(&key)
    }

    /// Select bytecode bodies within this same sealed source compilation.
    /// Unselected bodies remain generated LLVM. A same-shaped function from
    /// another source compilation cannot be installed through this API.
    pub fn with_vm_functions(
        &self,
        functions: impl IntoIterator<Item = DefKey>,
    ) -> Result<Self, LlvmError> {
        let vm_functions = functions.into_iter().collect::<BTreeSet<_>>();
        if vm_functions
            .iter()
            .any(|key| !self.program.program.functions.contains_key(key))
        {
            return Err(LlvmError::AbiMismatch(
                "mixed partition names a function outside its source graph",
            ));
        }
        Self::lower_partitioned(
            self.program.clone(),
            self.descriptor.source_identity,
            self.descriptor.target.clone(),
            vm_functions,
        )
    }

    /// A native link checks every field, including source/type identities and
    /// allocator/control conventions, before resolving an executable entry.
    pub fn validate_abi(&self, supplied: &LlvmAbiDescriptor) -> Result<(), LlvmError> {
        supplied.target.validate_host()?;
        if supplied != &self.descriptor {
            return Err(LlvmError::AbiMismatch(
                "native module target, layout, source, runtime, or control contract mismatch",
            ));
        }
        Ok(())
    }

    fn lower_partitioned(
        program: VerifiedVmProgram,
        source_identity: Digest,
        target: LlvmTarget,
        vm_functions: BTreeSet<DefKey>,
    ) -> Result<Self, LlvmError> {
        target.validate_host()?;
        let plan = emit::Plan::new(&program.program, &target, &vm_functions)?;
        let mut partition = b"grandiose-llvm-engine-partition-v1".to_vec();
        for key in &vm_functions {
            partition.extend_from_slice(&key.0.as_bytes());
        }
        let descriptor = LlvmAbiDescriptor {
            generation: LLVM_NATIVE_ABI_GENERATION,
            target,
            layout_identity: plan.layout_identity(),
            source_identity,
            code_identity: program.fingerprint(),
            execution_partition: Digest::of_bytes(&partition),
            runtime_manifest: program.program.runtime_manifest,
            control_convention: LLVM_CONTROL_CONVENTION.into(),
            allocation_domain: VmNativeAbi::current().allocation_domain,
        };
        let ir = plan.emit(&descriptor)?;
        Ok(Self {
            descriptor,
            ir,
            layouts: plan.layouts.clone(),
            functions: plan.functions.clone(),
            frame_layouts: plan.plans.clone().into(),
            program,
            vm_functions,
        })
    }
}

/// One source compilation supplies both engines. The source identity is sealed
/// before region/effect details become runtime representations; same-shaped
/// machine types do not substitute for the original source contract.
impl StageZeroCompiler {
    pub fn compile_llvm(
        &self,
        request: CompilationRequest,
        target: LlvmTarget,
    ) -> Result<LlvmIrProgram, LlvmError> {
        self.compile_llvm_partitioned(request, target, |_| false)
    }

    /// Choose VM bodies before native admission. VM-only instructions are
    /// permitted in those bodies, but unsupported cross-engine control is not.
    /// The selection is sealed into the emitted module's ABI identity.
    pub fn compile_llvm_partitioned(
        &self,
        request: CompilationRequest,
        target: LlvmTarget,
        use_vm: impl Fn(&super::VmFunction) -> bool,
    ) -> Result<LlvmIrProgram, LlvmError> {
        let environment = super::float_env::FloatEnvironment::enter()?;
        let result = self.compile_llvm_partitioned_in_profile(request, target, use_vm);
        environment.restore()?;
        result
    }

    fn compile_llvm_partitioned_in_profile(
        &self,
        request: CompilationRequest,
        target: LlvmTarget,
        use_vm: impl Fn(&super::VmFunction) -> bool,
    ) -> Result<LlvmIrProgram, LlvmError> {
        target.validate_host()?;
        let source_identity = request
            .clone()
            .normalize()
            .map_err(LlvmError::InvalidInput)?
            .fingerprint;
        let outcome = self.compile(request).map_err(LlvmError::Source)?;
        let program = outcome.artifact.ok_or_else(|| {
            LlvmError::InvalidNativeGraph(
                "native emission requires an executable compilation mode".into(),
            )
        })?;
        let vm_functions = program
            .program
            .functions
            .iter()
            .map(|(key, function)| {
                // Partition policy is host code. Restore the compiler's
                // profile even when it changes controls or unwinds.
                let environment = super::float_env::FloatEnvironment::enter()?;
                let selected = use_vm(function);
                environment.restore()?;
                Ok(selected.then_some(*key))
            })
            .collect::<Result<Vec<_>, super::VmArtifactError>>()?
            .into_iter()
            .flatten()
            .collect();
        LlvmIrProgram::lower_partitioned(program, source_identity, target, vm_functions)
    }
}

/// C-layout execution record used by generated code, not a serialized address.
/// Every generated invocation shares finite instruction/call/byte budgets.
#[repr(C)]
#[derive(Debug)]
pub(super) struct NativeContext {
    pub(super) instructions: u64,
    pub(super) instruction_limit: u64,
    pub(super) live_bytes: u64,
    pub(super) byte_limit: u64,
    pub(super) depth: u32,
    pub(super) depth_limit: u32,
    pub(super) peak_depth: u32,
    pub(super) fault: u32,
    pub(super) tail_calls: u64,
    pub(super) mixed_context: *mut std::ffi::c_void,
    pub(super) invoke_vm: Option<
        unsafe extern "C" fn(
            *mut NativeContext,
            u32,
            *const *const u8,
            *mut u8,
            *mut *const u8,
            *mut u8,
            *mut u32,
        ) -> u32,
    >,
    pub(super) allocation_limit: u64,
    pub(super) allocation_context: *mut std::ffi::c_void,
    pub(super) allocate: Option<
        unsafe extern "C" fn(*mut NativeContext, u32, *mut u8, u64, u64, u64, *mut *mut u8) -> u32,
    >,
    pub(super) fault_register: u32,
    pub(super) callable_context: *mut std::ffi::c_void,
    pub(super) callable: Option<unsafe extern "C" fn(*mut NativeContext, u32, u32, u32, u32, *const *const u8, *mut u8) -> u32>,
    pub(super) residents: Option<unsafe extern "C" fn(*mut NativeContext, u32, *mut u8, *const u8, u64)>,
}

impl NativeContext {
    pub(super) fn new(limits: VmExecutionLimits) -> Self {
        Self {
            instructions: 0,
            instruction_limit: limits.max_instructions,
            live_bytes: 0,
            byte_limit: limits.max_native_bytes.min(LLVM_NATIVE_STACK_BYTES),
            depth: 0,
            depth_limit: limits.max_call_depth,
            peak_depth: 0,
            fault: 0,
            tail_calls: 0,
            mixed_context: std::ptr::null_mut(),
            invoke_vm: None,
            allocation_limit: limits.max_native_allocation_bytes,
            allocation_context: std::ptr::null_mut(),
            allocate: None,
            fault_register: 0,
            callable_context: std::ptr::null_mut(),
            callable: None,
            residents: None,
        }
    }
    pub(super) fn result(&self, status: u32) -> Result<(), LlvmError> {
        let error = match self.fault {
            0 if status == 0 => return Ok(()),
            1 => VmArtifactError::ArithmeticOverflow,
            2 => VmArtifactError::DivisionByZero,
            3 => VmArtifactError::InstructionLimit {
                limit: self.instruction_limit,
            },
            4 => VmArtifactError::CallDepthLimit {
                limit: self.depth_limit,
            },
            5 => VmArtifactError::NativeAbi {
                message: "native activation exceeds the requested memory budget or the 1 MiB native stack-resident ceiling",
            },
            9 => VmArtifactError::NativeMemory {
                message: "native layout size overflow",
            },
            10 => VmArtifactError::NativeMemory {
                message: "native reference requires a non-null aligned pointer",
            },
            11 => VmArtifactError::InvalidRegister {
                register: self.fault_register,
            },
            12 => VmArtifactError::NativeMemory {
                message: "native storage resident was moved out",
            },
            13 => VmArtifactError::NativeAbi {
                message: "native result requires a fully initialized source resident",
            },
            14 => VmArtifactError::NativeMemory {
                message: "native enum projection does not match the active variant layout",
            },
            15 => VmArtifactError::Trap,
            16 => VmArtifactError::NativeAbi {
                message: "cannot establish or restore the native floating-point environment",
            },
            17 => VmArtifactError::NativeAbi {
                message: "generated invocation lacks its bound execution-domain runtime",
            },
            6 => VmArtifactError::NativeAbi {
                message: "native execution reached a verified terminal trap",
            },
            _ => VmArtifactError::NativeAbi {
                message: "invalid generated native status/fault pair",
            },
        };
        Err(LlvmError::Runtime(error))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LlvmExecutionProfile {
    pub instructions: u64,
    pub peak_call_depth: u32,
    pub recycled_tail_calls: u64,
    /// Actual shared-domain backing extents and resident entry transport.
    /// This is not a census of Rust metadata allocations or native stack bytes.
    pub native_memory: super::VmNativeMemoryProfile,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm_backend::{VmFunction, VmInstruction as I, VmNominalCopyDescriptor, verify_program};

    #[test]
    fn native_tail_callable_variance_preserves_nested_arguments_and_results() {
        let key = |name: &str| DefKey(Digest::of_bytes(name.as_bytes()));
        let entry = key("native-tail-variance-entry");
        let relay = key("native-tail-variance-relay");
        let forward = key("native-tail-variance-forward");
        let answer = key("native-tail-variance-answer");
        let callable = |capable| VmType::Callable {
            shared_receiver: capable, unique_receiver: capable, safety: crate::Safety::Safe,
            parameters: vec![], result: Box::new(VmType::I64), effects: Default::default(),
        };
        let strong = callable(true);
        let weak = callable(false);
        let product = |value| VmType::Tuple(vec![value]);
        let reference = |value| VmType::Reference { unique: false, referent: Box::new(product(value)) };
        let function = |definition, parameters, registers, instructions| VmFunction {
            definition, parameters, registers, instructions, safety: crate::Safety::Safe,
            unsafe_execution: false, nominal_copy_descriptors: vec![], captures: 0,
        };
        let mut candidate = CandidateVmProgram {
            schema: crate::STAGE0_VM_SCHEMA, runtime_manifest: None, host_capabilities: vec![], entry,
            callable_environments: Default::default(), fingerprint: Digest::of_bytes(b"unsealed-tail-variance"),
            functions: BTreeMap::from([
                (entry, function(entry, 0,
                    vec![strong.clone(), product(strong.clone()), reference(strong.clone()), weak.clone(), VmType::I64],
                    vec![
                        I::DeclareResult { result: VmType::I64, returns: true },
                        I::MakeCallable { dst: 0, callee: answer, captures: vec![], environment: None },
                        I::MakeTupleOwned { dst: 1, fields: vec![0] },
                        I::Borrow { dst: 2, src: 1, fields: vec![], unique: false, reborrow: false },
                        I::CallOwned { dst: 3, callee: relay, arguments: vec![2] },
                        I::CallIndirectOwned { dst: 4, callee: 3, arguments: vec![] },
                        I::Return { value: 4 },
                    ])),
                (relay, function(relay, 1, vec![reference(strong.clone())], vec![
                    I::DeclareResult { result: weak.clone(), returns: true },
                    // One edge weakens nested argument capabilities and the
                    // returned callable in opposite directions. The actual
                    // payload is read by the destination, not just forwarded.
                    I::TailCallOwned { callee: forward, arguments: vec![0] },
                ])),
                (forward, function(forward, 1,
                    vec![reference(weak.clone()), product(weak.clone()), weak.clone(), VmType::I64, strong.clone(),
                        VmType::Reference { unique: false, referent: Box::new(weak.clone()) }, weak, VmType::I64],
                    vec![
                        I::DeclareResult { result: strong, returns: true },
                        I::DerefCopy { dst: 1, reference: 0 },
                        I::TakeProjection { dst: 2, base: 1, fields: vec![0] },
                        I::CallIndirectOwned { dst: 3, callee: 2, arguments: vec![] },
                        I::Borrow { dst: 5, src: 0, fields: vec![0], unique: false, reborrow: true },
                        I::DerefCopy { dst: 6, reference: 5 },
                        I::CallIndirectOwned { dst: 7, callee: 6, arguments: vec![] },
                        I::MakeCallable { dst: 4, callee: answer, captures: vec![], environment: None },
                        I::Return { value: 4 },
                    ])),
                (answer, function(answer, 0, vec![VmType::I64], vec![
                    I::DeclareResult { result: VmType::I64, returns: true },
                    I::ConstI64 { dst: 0, value: 42 }, I::Return { value: 0 },
                ])),
            ]),
        };
        candidate.fingerprint = candidate.computed_fingerprint();
        let verified = verify_program(candidate).unwrap();
        assert_eq!(verified.run_i64().unwrap(), 42);
        assert_eq!(crate::decode_and_verify_program(&verified.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        for vm_functions in [BTreeSet::new(), BTreeSet::from([forward])] {
            let ir = LlvmIrProgram::lower_partitioned(verified.clone(), Digest::of_bytes(b"native-tail-variance"),
                LlvmTarget::host().unwrap(), vm_functions).unwrap();
            for optimization in [0, 2] {
                // SAFETY: only this locally authored and verified graph is executed.
                let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
                assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
            }
        }
    }

    #[test]
    fn native_reference_probes_observe_holes_in_distinct_zero_sized_fields() {
        let entry = DefKey(Digest::of_bytes(b"native-reference-initialization-probes"));
        let tuple = VmType::Tuple(vec![VmType::Unit, VmType::Unit]);
        let reference = VmType::Reference { unique: true, referent: Box::new(VmType::Unit) };
        let function = VmFunction {
            definition: entry, safety: crate::Safety::Safe, unsafe_execution: false,
            nominal_copy_descriptors: vec![], captures: 0, parameters: 0,
            registers: vec![VmType::Unit, VmType::Unit, tuple, reference.clone(), reference,
                VmType::Unit, VmType::Bool, VmType::Bool, VmType::Bool, VmType::I64],
            instructions: vec![
                I::DeclareResult { result: VmType::I64, returns: true },
                I::ConstUnit { dst: 0 }, I::ConstUnit { dst: 1 },
                I::MakeTupleOwned { dst: 2, fields: vec![0,1] },
                I::Borrow { dst: 3, src: 2, fields: vec![0], unique: true, reborrow: false },
                I::Borrow { dst: 4, src: 2, fields: vec![1], unique: true, reborrow: false },
                I::DerefMove { dst: 5, reference: 3 },
                I::DerefIsInitialized { dst: 6, reference: 3 },
                I::BranchBool { condition: 6, then_target: 16, else_target: 9 },
                I::DerefIsInitialized { dst: 7, reference: 4 },
                I::BranchBool { condition: 7, then_target: 11, else_target: 16 },
                I::DerefStore { reference: 3, src: 5 },
                I::DerefIsInitialized { dst: 8, reference: 3 },
                I::BranchBool { condition: 8, then_target: 14, else_target: 16 },
                I::ConstI64 { dst: 9, value: 42 }, I::Return { value: 9 }, I::Trap,
            ],
        };
        let mut candidate = CandidateVmProgram { schema: crate::STAGE0_VM_SCHEMA,
            runtime_manifest: None, host_capabilities: vec![], entry, functions: [(entry,function)].into(),
            callable_environments: Default::default(), fingerprint: Digest::of_bytes(b"unsealed") };
        candidate.fingerprint = candidate.computed_fingerprint();
        let verified = verify_program(candidate).unwrap();
        assert_eq!(verified.run_i64().unwrap(), 42);
        assert_eq!(crate::decode_and_verify_program(&verified.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        let ir = LlvmIrProgram::lower_partitioned(verified, Digest::of_bytes(b"native-reference-initialization-test"),
            LlvmTarget::host().unwrap(), Default::default()).unwrap();
        for optimization in [0,2] {
            // SAFETY: execute only this locally authored and verified graph.
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
        }
    }

    #[test]
    fn native_leave_transfers_initialization_without_reviving_moved_fields() {
        let entry = DefKey(Digest::of_bytes(b"native-owned-leave-initialization"));
        let tuple = VmType::Tuple(vec![VmType::I64, VmType::I64]);
        let function = VmFunction {
            definition: entry, safety: crate::Safety::Safe, unsafe_execution: false,
            nominal_copy_descriptors: vec![], captures: 0, parameters: 0,
            registers: vec![VmType::I64, VmType::I64, tuple.clone(), VmType::I64, tuple, VmType::Bool, VmType::Bool, VmType::I64],
            instructions: vec![
                I::DeclareResult { result: VmType::I64, returns: true },
                I::ConstI64 { dst: 0, value: 17 }, I::ConstI64 { dst: 1, value: 42 },
                I::MakeTupleOwned { dst: 2, fields: vec![0,1] },
                I::TakeProjection { dst: 3, base: 2, fields: vec![0] },
                I::Leave { brand_owner: entry, brand_label: 0, handler_depth: 0, target: 6,
                    arguments: vec![2], destinations: vec![4], cleanup: super::super::VmCleanupProof {
                        moved_places: vec![], active_loans: vec![],
                        storage_erasure: super::super::VmStorageErasureWitness::without_source_storage(),
                    } },
                I::IsInitialized { dst: 5, base: 2, fields: vec![] },
                I::BranchBool { condition: 5, then_target: 12, else_target: 8 },
                I::IsInitialized { dst: 6, base: 4, fields: vec![0] },
                I::BranchBool { condition: 6, then_target: 12, else_target: 10 },
                I::TakeProjection { dst: 7, base: 4, fields: vec![1] },
                I::Return { value: 7 }, I::Trap,
            ],
        };
        let mut candidate = CandidateVmProgram { schema: crate::STAGE0_VM_SCHEMA,
            runtime_manifest: None, host_capabilities: vec![], entry, functions: [(entry,function)].into(),
            callable_environments: Default::default(), fingerprint: Digest::of_bytes(b"unsealed") };
        candidate.fingerprint = candidate.computed_fingerprint();
        let verified = verify_program(candidate).unwrap();
        assert_eq!(verified.run_i64().unwrap(), 42);
        let ir = LlvmIrProgram::lower_partitioned(verified, Digest::of_bytes(b"native-leave-initialization-test"),
            LlvmTarget::host().unwrap(), Default::default()).unwrap();
        for optimization in [0,2] {
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
        }
    }

    #[test]
    fn native_patterns_observe_initialization_before_reading_moved_payloads() {
        use super::super::{VmPattern, VmPatternField};
        for borrow_position in [None, Some(4), Some(5)] {
        let borrowed = borrow_position.is_some();
        for case in 0..5 {
            let entry = DefKey(Digest::of_bytes(format!("native-pattern-holes-{case}-{borrow_position:?}").as_bytes()));
            let nominal = DefKey(Digest::of_bytes(b"native-pattern-hole-enum"));
            let is_tuple = matches!(case, 0 | 3);
            let is_array = case == 4;
            let expected = matches!(case, 1 | 3);
            let product = if is_tuple { VmType::Tuple(vec![VmType::I64,VmType::I64]) }
                else if is_array { VmType::FixedArray { element: Box::new(VmType::I64), length: 2 } }
                else { VmType::Nominal { definition: nominal, arguments: vec![] } };
            let descriptor = VmNominalCopyDescriptor { definition: nominal,
                source_contract: Digest::of_bytes(b"native-pattern-hole-descriptor"), is_enum: true,
                arguments: vec![], variants: vec![vec![VmType::I64,VmType::I64]] };
            let pattern = if case == 0 { VmPattern::Tuple(vec![VmPattern::Literal("17".into()),VmPattern::Any]) }
                else if case == 3 { VmPattern::Tuple(vec![VmPattern::Any,VmPattern::Any]) }
                else if is_array { VmPattern::Array { element: VmType::I64, elements: vec![VmPattern::Literal("42".into())],
                    rest: Some(crate::pattern::ArrayPatternRest { prefix: 0, omitted: 1 }) } }
                else { VmPattern::Enum { definition: nominal, variant: 0, field_count: 2,
                    field_types: vec![VmType::I64,VmType::I64],
                    fields: if case == 1 { vec![] } else { vec![VmPatternField { index: 0, ty: VmType::I64, pattern: VmPattern::Any }] } } };
            let mut function = VmFunction { definition: entry, safety: crate::Safety::Safe, unsafe_execution: false,
                nominal_copy_descriptors: if is_tuple || is_array { vec![] } else { vec![descriptor] },
                captures: 0, parameters: 0,
                registers: vec![VmType::I64,VmType::I64,product.clone(),VmType::I64,VmType::Bool,VmType::I64],
                instructions: vec![I::DeclareResult { result: VmType::I64, returns: true },
                    I::ConstI64 { dst: 0, value: 17 }, I::ConstI64 { dst: 1, value: 42 },
                    if is_tuple { I::MakeTupleOwned { dst: 2, fields: vec![0,1] } }
                    else if is_array { I::MakeArrayOwned { dst: 2, element_type: VmType::I64, fields: vec![0,1] } }
                    else { I::MakeEnumOwned { dst: 2, definition: nominal, variant: 0,
                        field_types: vec![VmType::I64,VmType::I64], fields: vec![0,1] } },
                    I::TakeProjection { dst: 3, base: 2, fields: vec![0] },
                    I::PatternTest { dst: 4, subject: 2, pattern },
                    I::BranchBool { condition: 4, then_target: if expected { 8 } else { 7 },
                        else_target: if expected { 7 } else { 8 } },
                    I::Trap, I::TakeProjection { dst: 5, base: 2, fields: vec![1] }, I::Return { value: 5 }],
            };
            if let Some(position) = borrow_position {
                function.registers.push(VmType::Reference { unique: true, referent: Box::new(product) });
                function.instructions.insert(position, I::Borrow { dst: 6, src: 2, fields: vec![], unique: true, reborrow: false });
                if let I::PatternTest { subject, .. } = &mut function.instructions[6] { *subject = 6; }
                if let I::BranchBool { then_target, else_target, .. } = &mut function.instructions[7] {
                    *then_target += 1;
                    *else_target += 1;
                }
            }
            let mut candidate = CandidateVmProgram { schema: crate::STAGE0_VM_SCHEMA,
                runtime_manifest: None, host_capabilities: vec![], entry, functions: [(entry,function)].into(),
                callable_environments: Default::default(), fingerprint: Digest::of_bytes(b"unsealed") };
            candidate.fingerprint = candidate.computed_fingerprint();
            let verified = verify_program(candidate).unwrap();
            assert_eq!(verified.run_i64().unwrap(), 42, "VM case {case}, borrowed={borrowed}");
            assert_eq!(super::super::decode_and_verify_program(&verified.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
            let ir = LlvmIrProgram::lower_partitioned(verified, Digest::of_bytes(b"native-pattern-initialization-test"),
                LlvmTarget::host().unwrap(), Default::default()).unwrap();
            for optimization in [0,2] {
                let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
                assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42, "native case {case}, borrowed={borrowed}, O{optimization}");
            }
        }
        }
    }

    #[test]
    fn native_enum_projection_checks_the_active_type_and_field_count() {
        for count_mismatch in [false, true] {
            let definition = DefKey(Digest::of_bytes(b"native-projection-type"));
            let entry = DefKey(Digest::of_bytes(b"native-projection-entry"));
            let nominal = VmType::Nominal { definition, arguments: vec![] };
            let descriptor = VmNominalCopyDescriptor {
                definition, source_contract: Digest::of_bytes(b"native-projection-source"),
                is_enum: true, arguments: vec![],
                variants: if count_mismatch { vec![vec![VmType::I64,VmType::I64],vec![VmType::I64]] }
                    else { vec![vec![VmType::I64],vec![VmType::Bool]] },
            };
            let function = VmFunction {
                definition: entry, safety: crate::Safety::Safe, unsafe_execution: false,
                nominal_copy_descriptors: vec![descriptor], captures: 0, parameters: 0,
                registers: vec![VmType::I64,VmType::Bool,nominal,VmType::I64],
                instructions: vec![
                    I::DeclareResult { result: VmType::I64, returns: true },
                    I::ConstI64 { dst: 0, value: 42 }, I::ConstBool { dst: 1, value: true },
                    I::MakeEnumOwned { dst: 2, definition, variant: 1,
                        fields: vec![if count_mismatch { 0 } else { 1 }],
                        field_types: vec![if count_mismatch { VmType::I64 } else { VmType::Bool }] },
                    if count_mismatch {
                        I::ProjectRecord { dst: 3, base: 2, index: 0, field_count: 2, field_type: VmType::I64 }
                    } else { I::TakeProjection { dst: 3, base: 2, fields: vec![0] } },
                    I::Return { value: 3 },
                ],
            };
            let mut candidate = CandidateVmProgram {
                schema: crate::STAGE0_VM_SCHEMA, runtime_manifest: None, host_capabilities: vec![],
                entry, functions: [(entry,function)].into(), callable_environments: Default::default(),
                fingerprint: Digest::of_bytes(b"pending"),
            };
            candidate.fingerprint = candidate.computed_fingerprint();
            let verified = verify_program(candidate).unwrap();
            assert!(verified.run_i64().is_err(), "VM must reject the wrong active payload");
            let ir = LlvmIrProgram::lower_partitioned(verified, Digest::of_bytes(b"projection-runtime-test"),
                LlvmTarget::host().unwrap(), Default::default()).unwrap();
            for optimization in [0,2] {
                let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
                assert!(matches!(native.run_i64_with_limits(Default::default()),
                    Err(LlvmError::Runtime(VmArtifactError::NativeMemory {
                        message: "native enum projection does not match the active variant layout",
                    }))));
            }
        }
    }
}

#[cfg(test)]
#[path = "llvm/float_tests.rs"]
mod float_tests;
