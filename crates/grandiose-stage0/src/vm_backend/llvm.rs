//! LLVM-generated Glorious code over the verified, concrete VM-LIR contract.
//!
//! This is a second execution engine, not a Rust compiler setting and not an
//! interpreter wrapper. Admission is whole-graph and fail-closed. Unsupported
//! control must never become an ordinary native call by accident.

mod emit;
mod layout;
mod load;
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
pub const LLVM_NATIVE_ABI_GENERATION: u32 = 7;
pub const LLVM_CONTROL_CONVENTION: &str = "grandiose:native-slot-dispatch:mixed-tail-v5";
/// Initial stack-backed native activations impose this additional explicit
/// resident-storage ceiling until the shared heap-frame convention is enabled.
pub const LLVM_NATIVE_STACK_BYTES: u64 = 1024 * 1024;

pub(super) fn initialization_paths(
    layout: &super::native_memory::NativeLayout,
) -> Result<Vec<Vec<u32>>, LlvmError> {
    let mut paths = BTreeSet::new();
    emit::collect_paths(layout, &mut vec![], &mut paths)?;
    Ok(paths.into_iter().collect())
}

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
    pub(super) tail_packets: Vec<TailPacketLayout>,
}

#[derive(Clone, Debug)]
pub(super) struct TailPacketLayout {
    pub(super) data_offsets: Vec<usize>,
    pub(super) initialization_offsets: Vec<usize>,
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
            tail_packets: plan.tail_packets(),
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm_backend::{VmFunction, VmInstruction as I, VmNominalCopyDescriptor, verify_program};

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
