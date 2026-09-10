//! Capability-bound native calls over the existing host-layout storage.
//!
//! This is a locally compiled, explicitly unsafe embedding path. A binding is
//! not authenticated by its symbol, and bytes cannot install native code. The
//! adapter must implement its exact source contract, including loans and uses.
//! Scalar/reference arguments use ABI slots; aggregates must already have a
//! native home and are borrowed or transferred through genuine pointers, never
//! rebuilt at the boundary. Owned results use caller-provided native slots.

use super::native_memory::{NativeLayout, NativeShape, native_layout};
use super::codec::encode_type;
use super::{
    CandidateVmProgram, DefKey, Digest, ExecutionBudget, NativeMemory, ReferenceTarget,
    RuntimeCaptureEnvironment, RuntimeRegisters, VerifiedVmProgram, VmArtifactError, VmExecutionLimits, VmInstruction,
    VmNativeResident, VmNominalCopyDescriptor, VmType, VmValue,
    execute_with_arguments, expect_i64,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::c_void,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::Arc,
};

#[path = "llvm/bridge.rs"]
pub(super) mod generated;

fn error(message: &'static str) -> VmArtifactError {
    VmArtifactError::NativeAbi { message }
}

/// Target-specific in-process ABI. This does not redefine portable G1 scalar
/// widths or claim compatibility with Rust's private aggregate layouts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmNativeAbi {
    pub generation: u32,
    pub architecture: String,
    pub operating_system: String,
    pub pointer_bits: u32,
    pub little_endian: bool,
    /// Raw backing belongs to this execution-domain protocol, not arbitrary
    /// Rust/C allocations with the same address or provider. Callback re-entry
    /// shares the invoking VM's live allocation domain.
    pub allocation_domain: String,
}

impl VmNativeAbi {
    pub fn current() -> Self {
        Self {
            generation: 4,
            architecture: std::env::consts::ARCH.into(),
            operating_system: std::env::consts::OS.into(),
            pointer_bits: usize::BITS,
            little_endian: cfg!(target_endian = "little"),
            allocation_domain: "grandiose-vm:execution-native-heap:v1".into(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmNativeLayoutField {
    pub offset: usize,
    pub layout: VmNativeLayout,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmNativeLayoutShape {
    Scalar,
    /// Callee digest at zero; execution-domain environment identity at 32.
    Callable,
    Reference,
    /// Immutable byte pointer at offset zero, followed by a usize extent.
    /// Backing remains pinned for the complete execution data domain.
    StaticData,
    Product(Vec<VmNativeLayoutField>),
    Repeated { element: Box<VmNativeLayout>, count: usize, stride: usize },
    Enum {
        payload_offset: usize,
        variants: Vec<Vec<VmNativeLayoutField>>,
    },
}

/// Inspectable layout for a host's explicitly declared concrete fixture.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmNativeLayout {
    pub ty: VmType,
    pub size: usize,
    pub alignment: usize,
    pub shape: VmNativeLayoutShape,
}

impl From<&NativeLayout> for VmNativeLayout {
    fn from(layout: &NativeLayout) -> Self {
        let fields = |fields: &super::native_memory::NativeFields| {
            fields
                .iter()
                .map(|field| VmNativeLayoutField {
                    offset: field.offset,
                    layout: Self::from(field.layout.as_ref()),
                })
                .collect()
        };
        Self {
            ty: layout.ty.clone(),
            size: layout.memory.size(),
            alignment: layout.memory.alignment(),
            shape: match &layout.shape {
                NativeShape::Scalar => VmNativeLayoutShape::Scalar,
                NativeShape::Callable => VmNativeLayoutShape::Callable,
                NativeShape::Reference { .. } => VmNativeLayoutShape::Reference,
                NativeShape::StaticData => VmNativeLayoutShape::StaticData,
                NativeShape::Product(super::native_memory::NativeFields::Repeated { element, count, stride }) =>
                    VmNativeLayoutShape::Repeated { element: Box::new(Self::from(element.as_ref())), count: *count, stride: *stride },
                NativeShape::Product(items) => VmNativeLayoutShape::Product(fields(items)),
                NativeShape::Enum {
                    payload_offset,
                    variants,
                } => VmNativeLayoutShape::Enum {
                    payload_offset: *payload_offset,
                    variants: variants.iter().map(|variant| fields(variant)).collect(),
                },
            },
        }
    }
}

/// A host implementation must match all fields, not just argument sizes.
/// `source_contract` binds the declaration's safety, lifetimes, effects, uses,
/// and generic evidence before VM representation erases those distinctions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmNativeImport {
    pub abi: VmNativeAbi,
    pub capability: String,
    pub symbol: String,
    pub source_contract: Digest,
    pub parameters: Vec<VmType>,
    pub result: VmType,
    pub nominals: Vec<VmNominalCopyDescriptor>,
    pub residents: Vec<VmNativeResidentContract>,
}

/// A concrete source resident and the emitted code implementing its selected
/// destruction closure. This is executable identity, not a native function
/// pointer or permission to use a same-shaped unrelated type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmNativeResidentContract {
    pub resident: VmNativeResident,
    pub destruction_code: Option<Digest>,
}

fn destruction_code_identity(
    program: &CandidateVmProgram,
    entry: DefKey,
) -> Result<Digest, VmArtifactError> {
    let mut pending = vec![entry];
    let mut seen = BTreeSet::new();
    while let Some(definition) = pending.pop() {
        if !seen.insert(definition) {
            continue;
        }
        let function = program
            .functions
            .get(&definition)
            .ok_or(VmArtifactError::MissingFunction { definition })?;
        for instruction in &function.instructions {
            match instruction {
                VmInstruction::MakeCallable { callee, environment, .. } => {
                    pending.push(*callee);
                    pending.extend(environment.as_ref().and_then(|environment| environment.destructor));
                }
                VmInstruction::CallOwned { callee, .. } | VmInstruction::Call { callee, .. }
                | VmInstruction::TailCallOwned { callee, .. } => {
                    pending.push(*callee)
                }
                VmInstruction::DeclareFrameCleanup { actions } => {
                    pending.extend(actions.iter().map(|action| action.destructor));
                }
                VmInstruction::HostCallOwned { resident_operations, .. }
                | VmInstruction::HostCall {
                    resident_operations,
                    ..
                } => pending.extend(
                    resident_operations
                        .iter()
                        .filter_map(|resident| resident.destructor),
                ),
                _ => {}
            }
        }
    }
    let mut bytes = b"grandiose-native-destruction-code-v1".to_vec();
    bytes.extend_from_slice(&entry.0.as_bytes());
    bytes.extend_from_slice(&(seen.len() as u64).to_le_bytes());
    for definition in seen {
        super::codec::encode_function(&program.functions[&definition], &mut bytes);
    }
    Ok(Digest::of_bytes(&bytes))
}

impl VmNativeImport {
    pub fn layout_of(&self, ty: &VmType) -> Result<VmNativeLayout, VmArtifactError> {
        if self.abi != VmNativeAbi::current() {
            return Err(error("native ABI target/generation mismatch"));
        }
        Ok(VmNativeLayout::from(&native_layout(
            ty,
            &self.nominals.clone().into(),
            &mut vec![],
        )?))
    }
}

fn nominal_key(ty: &VmType) -> Vec<u8> {
    let mut bytes = vec![];
    encode_type(ty, &mut bytes);
    bytes
}

fn collect_nominals(
    parameters: &[VmType],
    result: &VmType,
    available: &[VmNominalCopyDescriptor],
) -> Result<Vec<VmNominalCopyDescriptor>, VmArtifactError> {
    Ok(collect_layout_closure(parameters, result, available)?.0)
}

fn collect_layout_closure(
    parameters: &[VmType],
    result: &VmType,
    available: &[VmNominalCopyDescriptor],
) -> Result<(Vec<VmNominalCopyDescriptor>, BTreeSet<Vec<u8>>), VmArtifactError> {
    let mut pending = parameters.to_vec();
    pending.push(result.clone());
    let mut seen = BTreeSet::new();
    let mut found = BTreeMap::new();
    let mut residents = BTreeSet::new();
    while let Some(ty) = pending.pop() {
        let key = nominal_key(&ty);
        if !seen.insert(key.clone()) {
            continue;
        }
        if owned_resident(&ty) {
            residents.insert(key.clone());
        }
        match ty {
            VmType::Nominal {
                definition,
                arguments,
            } => {
                let descriptor = available
                    .iter()
                    .find(|descriptor| {
                        descriptor.definition == definition && descriptor.arguments == arguments
                    })
                    .ok_or_else(|| error("native import has no concrete nominal descriptor"))?;
                pending.extend(arguments.into_iter().filter_map(|argument| match argument {
                    super::VmGenericArgument::Type(ty) => Some(ty), _ => None,
                }));
                pending.extend(descriptor.variants.iter().flatten().cloned());
                found.insert(key, descriptor.clone());
            }
            VmType::Tuple(types) => pending.extend(types),
            VmType::RawPointer { pointee, .. }
            | VmType::Reference {
                referent: pointee, ..
            }
            | VmType::Array(pointee)
            | VmType::FixedArray { element: pointee, .. }
            | VmType::StaticData {
                element: pointee, ..
            } => pending.push(*pointee),
            VmType::Callable {
                parameters, result, ..
            } => {
                pending.extend(parameters);
                pending.push(*result);
            }
            _ => {}
        }
    }
    Ok((found.into_values().collect(), residents))
}

pub(super) fn validate_resident_operations(
    program: &CandidateVmProgram,
) -> Result<(), VmArtifactError> {
    for function in program.functions.values() {
        for instruction in &function.instructions {
            let (VmInstruction::HostCallOwned { parameters, result, resident_operations, .. }
            | VmInstruction::HostCall {
                parameters,
                result,
                resident_operations,
                ..
            }) = instruction
            else {
                continue;
            };
            if resident_operations
                .windows(2)
                .any(|pair| pair[0].source_type >= pair[1].source_type)
            {
                return Err(error("native resident operations are not canonical"));
            }
            let (_, expected) =
                collect_layout_closure(parameters, result, &function.nominal_copy_descriptors)?;
            let actual = resident_operations
                .iter()
                .map(|resident| nominal_key(&resident.ty))
                .collect::<BTreeSet<_>>();
            if actual != expected {
                return Err(error(
                    "native resident operations do not match the import layout closure",
                ));
            }
            for resident in resident_operations {
                if let Some(destructor) = resident.destructor {
                    let target = program.functions.get(&destructor).ok_or(
                        VmArtifactError::MissingFunction {
                            definition: destructor,
                        },
                    )?;
                    if target.captures != 0
                        || target.parameters != 1
                        || target.registers.first() != Some(&resident.ty)
                        || target.safety != super::Safety::Safe
                        || super::return_type(target)? != VmType::Unit
                    {
                        return Err(error("native resident destructor has an incompatible ABI"));
                    }
                }
            }
        }
    }
    Ok(())
}

fn imports(program: &CandidateVmProgram) -> Result<Vec<VmNativeImport>, VmArtifactError> {
    imports_from_roots(program, vec![program.entry])
}

fn imports_from_roots(program: &CandidateVmProgram, mut pending: Vec<DefKey>) -> Result<Vec<VmNativeImport>, VmArtifactError> {
    let mut seen = BTreeSet::new();
    let mut imports = BTreeMap::new();
    let mut destruction_codes = BTreeMap::new();
    while let Some(definition) = pending.pop() {
        if !seen.insert(definition) {
            continue;
        }
        let function = program
            .functions
            .get(&definition)
            .ok_or(VmArtifactError::MissingFunction { definition })?;
        for instruction in &function.instructions {
            match instruction {
                VmInstruction::MakeCallable { callee, environment, .. } => {
                    pending.push(*callee);
                    pending.extend(environment.as_ref().and_then(|environment| environment.destructor));
                }
                VmInstruction::CallOwned { callee, .. } | VmInstruction::Call { callee, .. }
                | VmInstruction::TailCallOwned { callee, .. } => {
                    pending.push(*callee)
                }
                VmInstruction::DeclareFrameCleanup { actions } => {
                    pending.extend(actions.iter().map(|action| action.destructor));
                }
                VmInstruction::HostCallOwned { capability, symbol, source_contract, parameters, result, resident_operations, .. }
                | VmInstruction::HostCall {
                    capability,
                    symbol,
                    source_contract,
                    parameters,
                    result,
                    resident_operations,
                    ..
                } => {
                    let mut residents = Vec::with_capacity(resident_operations.len());
                    for resident in resident_operations {
                        let destruction_code = if let Some(destructor) = resident.destructor {
                            pending.push(destructor);
                            Some(if let Some(code) = destruction_codes.get(&destructor) {
                                *code
                            } else {
                                let code = destruction_code_identity(program, destructor)?;
                                destruction_codes.insert(destructor, code);
                                code
                            })
                        } else {
                            None
                        };
                        residents.push(VmNativeResidentContract {
                            resident: resident.clone(),
                            destruction_code,
                        });
                    }
                    let import = VmNativeImport {
                        abi: VmNativeAbi::current(),
                        capability: capability.clone(),
                        symbol: symbol.clone(),
                        source_contract: *source_contract,
                        parameters: parameters.clone(),
                        result: result.clone(),
                        nominals: collect_nominals(
                            parameters,
                            result,
                            &function.nominal_copy_descriptors,
                        )?,
                        residents,
                    };
                    let key = (capability.clone(), symbol.clone());
                    if let Some(previous) = imports.insert(key, import.clone())
                        && previous != import
                    {
                        return Err(error("native symbol has conflicting source contracts"));
                    }
                }
                _ => {}
            }
        }
    }
    Ok(imports.into_values().collect())
}

type NativeFunction = dyn for<'a> Fn(&mut VmNativeCall<'a>) -> Result<(), VmArtifactError>;

#[derive(Clone)]
struct Binding {
    contract: VmNativeImport,
    function: Arc<NativeFunction>,
    /// Private compiler-owned slot extension. Public registration cannot opt in.
    generated: Option<Arc<generated::SlotContract>>,
}

/// Explicit native authority. Registration does not grant execution to any
/// ordinary/safe runner, and linking happens before the first VM instruction.
#[derive(Clone, Default)]
pub struct VmNativeImports {
    bindings: BTreeMap<(String, String), Binding>,
}

impl VmNativeImports {
    /// # Safety
    /// The implementation must satisfy this exact source contract and concrete
    /// ABI, including all reference lifetimes, alias/use/ownership obligations,
    /// allocator domains and callback multiplicities. It must not retain a
    /// borrowed pointer or callback past the declared call, unwind through C,
    /// or invoke a callback concurrently. Native re-entry uses shared host
    /// adapters: do not hold a conflicting host-side mutable loan across it.
    pub unsafe fn insert<F>(
        &mut self,
        contract: VmNativeImport,
        function: F,
    ) -> Result<(), VmArtifactError>
    where
        F: for<'a> Fn(&mut VmNativeCall<'a>) -> Result<(), VmArtifactError> + 'static,
    {
        if contract.abi != VmNativeAbi::current() {
            return Err(error("native ABI target/generation mismatch"));
        }
        let key = (contract.capability.clone(), contract.symbol.clone());
        if self.bindings.contains_key(&key) {
            return Err(error("duplicate native import binding"));
        }
        self.bindings.insert(
            key,
            Binding {
                contract,
                function: Arc::new(function),
                generated: None,
            },
        );
        Ok(())
    }

    fn link(
        &self,
        program: &CandidateVmProgram,
    ) -> Result<Arc<BoundNativeImports>, VmArtifactError> {
        self.link_contracts(imports(program)?)
    }

    fn link_contracts(&self, contracts: Vec<VmNativeImport>) -> Result<Arc<BoundNativeImports>, VmArtifactError> {
        let mut linked: BTreeMap<String, BTreeMap<String, Arc<BoundImport>>> = BTreeMap::new();
        for contract in contracts {
            let key = (contract.capability.clone(), contract.symbol.clone());
            let binding = self.bindings.get(&key).ok_or_else(|| {
                VmArtifactError::HostCallRequiresAuthority {
                    capability: contract.capability.clone(),
                    symbol: contract.symbol.clone(),
                }
            })?;
            if binding.contract != contract {
                return Err(error(
                    "native import source contract or concrete layout mismatch",
                ));
            }
            let descriptors: Arc<[VmNominalCopyDescriptor]> = contract.nominals.clone().into();
            let parameters = if let Some(slots) = &binding.generated {
                if slots.parameters.iter().map(|layout| &layout.ty).ne(contract.parameters.iter())
                    || slots.result.ty != contract.result || slots.captures > contract.parameters.len() {
                    return Err(error("generated slot contract differs from its bound source ABI"));
                }
                slots.parameters.iter().enumerate().map(|(index, layout)| {
                    if index < slots.captures { ArgumentPlan::Capture(layout.clone()) }
                    else if generated::resident(&layout.ty) {
                        ArgumentPlan::Owned(layout.clone())
                    } else { ArgumentPlan::Value(layout.clone()) }
                }).collect()
            } else { contract
                .parameters
                .iter()
                .map(|ty| argument_plan(ty, &descriptors))
                .collect::<Result<Vec<_>, _>>()? };
            let result = if let Some(slots) = &binding.generated { slots.result.clone() }
                else { value_plan(&contract.result, &descriptors)? };
            let destructors = contract
                .residents
                .iter()
                .map(|contract| {
                    contract
                        .resident
                        .destructor
                        .map(|callee| {
                            Ok((
                                callee,
                                Arc::new(CallbackPlan {
                                    parameters: vec![value_plan(
                                        &contract.resident.ty,
                                        &descriptors,
                                    )?],
                                    result: value_plan(&VmType::Unit, &descriptors)?,
                                }),
                            ))
                        })
                        .transpose()
                })
                .collect::<Result<Vec<_>, VmArtifactError>>()?;
            linked.entry(contract.capability).or_default().insert(
                contract.symbol,
                Arc::new(BoundImport {
                    function: binding.function.clone(),
                    parameters,
                    result,
                    destructors,
                    generated: binding.generated.clone(),
                }),
            );
        }
        Ok(Arc::new(BoundNativeImports { imports: linked }))
    }
}

enum ArgumentPlan {
    Value(Arc<NativeLayout>),
    Owned(Arc<NativeLayout>),
    Capture(Arc<NativeLayout>),
    Callback(Arc<CallbackPlan>),
}
struct CallbackPlan {
    parameters: Vec<Arc<NativeLayout>>,
    result: Arc<NativeLayout>,
}
struct BoundImport {
    function: Arc<NativeFunction>,
    parameters: Vec<ArgumentPlan>,
    result: Arc<NativeLayout>,
    destructors: Vec<Option<(DefKey, Arc<CallbackPlan>)>>,
    generated: Option<Arc<generated::SlotContract>>,
}
pub(super) struct BoundNativeImports {
    imports: BTreeMap<String, BTreeMap<String, Arc<BoundImport>>>,
}

impl BoundNativeImports {
    /// Published generated binding requirements, never inferred from a host
    /// symbol or from a Callable type used by the public callback ABI.
    pub(super) fn generated_resident_slot(&self, capability: &str, symbol: &str, parameter: Option<usize>) -> Option<Arc<NativeLayout>> {
        let binding = self.imports.get(capability)?.get(symbol)?;
        binding.generated.as_ref()?;
        match parameter {
            Some(index) => match binding.parameters.get(index)? {
                ArgumentPlan::Owned(layout) | ArgumentPlan::Capture(layout) => Some(layout.clone()),
                _ => None,
            },
            None => generated::resident(&binding.result.ty).then(|| binding.result.clone()),
        }
    }
}

fn value_plan(
    ty: &VmType,
    descriptors: &Arc<[VmNominalCopyDescriptor]>,
) -> Result<Arc<NativeLayout>, VmArtifactError> {
    if matches!(ty, VmType::Array(_) | VmType::Callable { .. }) {
        return Err(error(
            "native private array/callable layout is not supported",
        ));
    }
    let layout = native_layout(ty, descriptors, &mut vec![])?;
    if !layout.supports_resident(descriptors) {
        return Err(error(
            "native value contains an unsupported resident layout",
        ));
    }
    Ok(Arc::new(layout))
}

fn argument_plan(
    ty: &VmType,
    descriptors: &Arc<[VmNominalCopyDescriptor]>,
) -> Result<ArgumentPlan, VmArtifactError> {
    if let VmType::Callable {
        parameters,
        result,
        effects,
        ..
    } = ty
    {
        if !effects.effects.is_empty() || !effects.projections.is_empty() || !effects.tails.is_empty()
        {
            return Err(error(
                "native callback cannot carry outward effects across this boundary",
            ));
        }
        return Ok(ArgumentPlan::Callback(Arc::new(CallbackPlan {
            parameters: parameters
                .iter()
                .map(|ty| value_plan(ty, descriptors))
                .collect::<Result<_, _>>()?,
            result: value_plan(result, descriptors)?,
        })));
    }
    let layout = value_plan(ty, descriptors)?;
    Ok(if owned_resident(ty) {
        ArgumentPlan::Owned(layout)
    } else {
        ArgumentPlan::Value(layout)
    })
}

fn owned_resident(ty: &VmType) -> bool {
    matches!(ty, VmType::Tuple(_) | VmType::FixedArray { .. } | VmType::Nominal { .. })
}

impl VerifiedVmProgram {
    /// Inspect requirements; this does not approve them or install host code.
    pub fn native_imports(&self) -> Result<Vec<VmNativeImport>, VmArtifactError> {
        imports(&self.program)
    }

    /// # Safety
    /// All obligations of `run_i64_with_unsafe` apply, together with each native
    /// binding's exact contract. The whole execution, including callbacks,
    /// shares one memory domain and one set of finite VM budgets.
    pub unsafe fn run_i64_with_native(
        &self,
        imports: &VmNativeImports,
        limits: VmExecutionLimits,
    ) -> Result<i64, VmArtifactError> {
        let linked = imports.link(&self.program)?;
        let mut native_memory = NativeMemory::default();
        native_memory.imports = Some(linked);
        let mut budget = ExecutionBudget {
            native_memory,
            unsafe_execution: true,
            limits,
            instructions: 0,
            allocated_elements: 0,
        };
        expect_i64(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
}

/// C-compatible, synchronously borrowed callback. The context is not a guest
/// integer, code address or durable handle. Its lifetime ends with the call to
/// `with_callback`; the native implementation must not retain or share it.
#[repr(C)]
pub struct VmNativeCallback {
    pub context: *mut c_void,
    /// Each argument slot points to one initialized ABI value (a reference
    /// slot contains the actual referent pointer). The result slot is writable
    /// uninitialized storage with the declared result's alignment and extent.
    /// Aggregate argument slots must also be writable: bytecode receives the
    /// owned resident in that storage and may move from or mutate it. The
    /// native caller keeps each slot allocated until invocation returns and
    /// relinquishes its resident obligation when bytecode accepts the call.
    pub invoke:
        unsafe extern "C" fn(*mut c_void, *const *const u8, usize, *mut u8) -> VmNativeStatus,
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VmNativeStatus {
    Ok = 0,
    Failed = 1,
}

/// One synchronous native invocation; no private VmValue or frame handle is
/// exposed. ABI slots convey scalar bits and genuine reference/pointer values.
pub struct VmNativeCall<'a> {
    program: &'a CandidateVmProgram,
    binding: Arc<BoundImport>,
    registers: &'a mut RuntimeRegisters,
    arguments: &'a [u32],
    budget: &'a mut ExecutionBudget,
    depth: u32,
    result: Option<VmValue>,
    result_home: Option<Arc<super::native_storage::NativeHome>>,
    callback_failure: Option<VmArtifactError>,
}

fn check_slot(layout: &NativeLayout, pointer: *const u8) -> Result<(), VmArtifactError> {
    if layout.memory.size() != 0
        && (pointer.is_null() || pointer.addr() % layout.memory.alignment() != 0)
    {
        return Err(error("native ABI slot is null or misaligned"));
    }
    Ok(())
}

impl VmNativeCall<'_> {
    /// Transfer an aggregate argument to the native callee without moving its
    /// resident bytes. Each argument is taken once. The slot lasts through this
    /// native invocation; the callee must discharge or transfer the resident's
    /// source ownership obligations before returning, not retain the slot.
    ///
    /// # Safety
    /// Use the linked concrete layout and source quantity/drop contract. Native
    /// code must preserve allocator identity and may re-enter source operations
    /// through callbacks; it must not access the caller's disarmed owner.
    pub unsafe fn take_argument(&mut self, index: usize) -> Result<*mut u8, VmArtifactError> {
        let Some(ArgumentPlan::Owned(layout)) = self.binding.parameters.get(index) else {
            return Err(error("native argument is not an owned aggregate resident"));
        };
        let register = self.arguments[index];
        let Some(VmValue::Resident(home)) = self.registers[register as usize].as_ref() else {
            return Err(error(
                "owned native argument is absent or was already taken",
            ));
        };
        if home.ty() != &layout.ty || !home.is_fully_initialized(&[]) {
            return Err(error(
                "owned native argument has an invalid resident layout or initialization",
            ));
        }
        home.expose_address();
        let pointer = home.project(&[])?.0;
        self.registers[register as usize] = None;
        Ok(pointer)
    }

    /// Obtain the caller's preallocated, uninitialized aggregate result slot.
    /// No resident transport allocation or field conversion occurs here.
    ///
    /// # Safety
    /// Write exactly the linked result layout, then call `finish_result` once.
    /// The pointer is not a durable allocation or a loan beyond this invocation.
    pub unsafe fn result_pointer(&self) -> Result<*mut u8, VmArtifactError> {
        if self.result.is_some() {
            return Err(error("native result was already initialized"));
        }
        let home = self
            .result_home
            .as_ref()
            .ok_or_else(|| error("native result is not an owned aggregate resident"))?;
        home.expose_address();
        Ok(home.project(&[])?.0)
    }

    /// Commit an aggregate written directly into the caller's result slot.
    ///
    /// # Safety
    /// Every active field must be initialized with valid bits, references and
    /// ownership; inactive enum payloads and padding need not be initialized.
    pub unsafe fn finish_result(&mut self) -> Result<(), VmArtifactError> {
        if self.result.is_some() {
            return Err(error("native result was already initialized"));
        }
        let home = self
            .result_home
            .as_ref()
            .ok_or_else(|| error("native result is not an owned aggregate resident"))?
            .clone();
        home.expose_address();
        unsafe {
            if self.binding.generated.is_some() {
                home.initialize_native_with_holes(self.budget, None)?;
            } else {
                home.initialize_native(self.budget)?;
            }
        }
        self.result = Some(VmValue::Resident(home));
        Ok(())
    }

    /// # Safety
    /// `destination` must name writable storage for the linked parameter's
    /// exact native layout, without overlapping active arguments or loans.
    pub unsafe fn write_argument(
        &mut self,
        index: usize,
        destination: *mut u8,
    ) -> Result<(), VmArtifactError> {
        let Some(ArgumentPlan::Value(layout)) = self.binding.parameters.get(index) else {
            return Err(error(
                "native argument is absent or requires the callback trampoline",
            ));
        };
        check_slot(layout, destination)?;
        let value = self.registers[self.arguments[index] as usize]
            .as_ref()
            .ok_or_else(|| error("native argument is not initialized"))?;
        unsafe { layout.write(destination, value.clone(), self.budget) }
    }

    /// # Safety
    /// `source` must contain one initialized result with the exact linked ABI,
    /// valid pointer provenance and the source declaration's loan/ownership
    /// contract. Reference results borrow existing residents, never new copies.
    pub unsafe fn set_result_from(&mut self, source: *const u8) -> Result<(), VmArtifactError> {
        if self.result.is_some() {
            return Err(error("native result was already initialized"));
        }
        if self.result_home.is_some() {
            return Err(error(
                "owned native result must be initialized directly in its caller slot",
            ));
        }
        check_slot(&self.binding.result, source)?;
        self.result = Some(unsafe { self.binding.result.read_with_reference_admission(source, self.budget,
            if self.binding.generated.is_some() { super::native_memory::ReferenceRead::Resident } else { super::native_memory::ReferenceRead::External })? });
        Ok(())
    }

    /// Lend a real native entry trampoline for one bytecode callable. Errors
    /// are sticky: ignoring a Failed status cannot resume source execution.
    /// Native code may call it synchronously according to the frozen source
    /// multiplicity; unsafe registration owns those semantic obligations.
    pub fn with_callback<R>(
        &mut self,
        index: usize,
        native: impl FnOnce(VmNativeCallback) -> R,
    ) -> Result<R, VmArtifactError> {
        if let Some(failure) = &self.callback_failure {
            return Err(failure.clone());
        }
        let Some(ArgumentPlan::Callback(plan)) = self.binding.parameters.get(index) else {
            return Err(error("native argument is not a callback"));
        };
        let plan = plan.clone();
        let value = self.registers[self.arguments[index] as usize].as_ref()
            .ok_or_else(|| error("native callback argument is not initialized"))?;
        let value = match value { VmValue::Resident(home) => home.load(&[], self.budget)?, value => value.clone() };
        let VmValue::Callable { callee, captures, .. } = value else {
            return Err(error(
                "native callbacks cannot be labels or resumption tokens",
            ));
        };
        self.with_callback_plan(callee, captures, plan, native)
    }

    /// Lend the selected source destructor for `contract.residents[index]`.
    /// Its native callback ABI is one owned resident argument and a unit
    /// result. Invoking it consumes that resident and runs ordinary bytecode
    /// glue, including source-owned collection/element release operations.
    ///
    /// The native caller must already own the exact source resident and keep
    /// its argument slot live for the synchronous invocation. A missing hook
    /// is not permission to discard a linear value; no destructor is invented.
    pub fn with_destructor<R>(
        &mut self,
        index: usize,
        native: impl FnOnce(VmNativeCallback) -> R,
    ) -> Result<R, VmArtifactError> {
        if let Some(failure) = &self.callback_failure {
            return Err(failure.clone());
        }
        let Some(Some((callee, plan))) = self.binding.destructors.get(index) else {
            return Err(error("native resident has no selected source destructor"));
        };
        let (callee, plan) = (*callee, plan.clone());
        self.with_callback_plan(callee, RuntimeCaptureEnvironment::new(vec![]), plan, native)
    }

    fn with_callback_plan<R>(
        &mut self,
        callee: DefKey,
        captures: Arc<RuntimeCaptureEnvironment>,
        plan: Arc<CallbackPlan>,
        native: impl FnOnce(VmNativeCallback) -> R,
    ) -> Result<R, VmArtifactError> {
        let mut context = CallbackContext {
            call: self,
            callee,
            captures,
            plan,
            additional_depth: 0,
            argument_holes: None,
        };
        let result = native(VmNativeCallback {
            context: (&mut context as *mut CallbackContext<'_, '_>).cast(),
            invoke: callback_entry,
        });
        if let Some(failure) = &context.call.callback_failure {
            return Err(failure.clone());
        }
        Ok(result)
    }
}

struct CallbackContext<'call, 'vm> {
    call: &'call mut VmNativeCall<'vm>,
    callee: DefKey,
    captures: Arc<RuntimeCaptureEnvironment>,
    plan: Arc<CallbackPlan>,
    /// Generated LLVM frames between the invoking VM and this callback.
    additional_depth: u32,
    /// Only compiler-sealed generated callbacks may carry partial owners.
    argument_holes: Option<&'call [BTreeSet<Vec<u32>>]>,
}

impl CallbackContext<'_, '_> {
    unsafe fn invoke(
        &mut self,
        slots: *const *const u8,
        count: usize,
        result: *mut u8,
    ) -> Result<(), VmArtifactError> {
        if unsafe { self.invoke_with_tail_boundary(slots, count, result, None)? } {
            return Err(error("ordinary native callback unexpectedly transferred a tail"));
        }
        Ok(())
    }

    /// A true result means a private generated boundary accepted a mandatory
    /// tail packet. No result resident has been initialized in that case.
    unsafe fn invoke_with_tail_boundary(
        &mut self,
        slots: *const *const u8,
        count: usize,
        result: *mut u8,
        tail_boundary: Option<&mut dyn super::RuntimeTailBoundary>,
    ) -> Result<bool, VmArtifactError> {
        if let Some(failure) = &self.call.callback_failure {
            return Err(failure.clone());
        }
        if count != self.plan.parameters.len() {
            return Err(error("native callback argument count mismatch"));
        }
        if count != 0 && (slots.is_null() || slots.addr() % std::mem::align_of::<*const u8>() != 0)
        {
            return Err(error(
                "native callback argument table is null or misaligned",
            ));
        }
        check_slot(&self.plan.result, result)?;
        // Check all placements before accepting any owned resident obligation.
        for (index, layout) in self.plan.parameters.iter().enumerate() {
            check_slot(layout, unsafe { slots.add(index).read() })?;
        }
        let depth = self
            .call
            .depth
            .checked_add(self.additional_depth)
            .ok_or_else(|| error("native callback depth overflow"))?
            .checked_add(1)
            .ok_or_else(|| error("native callback depth overflow"))?;
        if depth >= self.call.budget.limits.max_call_depth {
            return Err(VmArtifactError::CallDepthLimit {
                limit: self.call.budget.limits.max_call_depth,
            });
        }
        // Rust/C re-entry has a real native stack even though ordinary VM
        // calls use an explicit frame stack. Bound that separate resource.
        if self.call.budget.native_memory.callback_depth >= 32 {
            return Err(error("native callback re-entry limit"));
        }
        let count = count
            .checked_add(self.captures.len())
            .ok_or_else(|| error("native callback argument count overflow"))?;
        self.call
            .budget
            .reserve_value("native callback arguments", count)?;
        let mut arguments = Vec::with_capacity(count);
        arguments.extend(self.captures.lend_to_invocation());
        for (index, layout) in self.plan.parameters.iter().enumerate() {
            let slot = unsafe { slots.add(index).read() };
            arguments.push(if owned_resident(&layout.ty)
                || (self.argument_holes.is_some() && generated::resident(&layout.ty)) {
                VmValue::Resident(unsafe {
                    if let Some(holes) = self.argument_holes {
                        super::native_storage::NativeHome::external_argument_with_holes(
                            layout.clone(), slot.cast_mut(), self.call.budget, Some(&holes[index]))?
                    } else {
                        super::native_storage::NativeHome::external_argument(
                            layout.clone(), slot.cast_mut(), self.call.budget)?
                    }
                })
            } else {
                unsafe { layout.read_with_reference_admission(slot, self.call.budget,
                    if self.argument_holes.is_some() { super::native_memory::ReferenceRead::Resident } else { super::native_memory::ReferenceRead::External })? }
            });
        }
        self.call.budget.native_memory.callback_depth += 1;
        let value = super::execute_program_with_tail_boundary(
            self.call.program,
            self.callee,
            &arguments,
            depth,
            self.call.budget,
            &mut None,
            None,
            owned_resident(&self.plan.result.ty)
                || (self.argument_holes.is_some() && generated::resident(&self.plan.result.ty)),
            (self.captures.len() != 0).then(|| self.captures.clone()),
            None,
            tail_boundary,
        );
        self.call.budget.native_memory.callback_depth -= 1;
        let value = match value? {
            super::RuntimeExecutionOutcome::Returned(value) => value,
            super::RuntimeExecutionOutcome::TailTransferred => return Ok(true),
        };
        if (owned_resident(&self.plan.result.ty)
            || (self.argument_holes.is_some() && generated::resident(&self.plan.result.ty)))
            && !matches!(&value, VmValue::Resident(_)) {
            return Err(error(
                "owned callback result lacks its native producer storage",
            ));
        }
        unsafe { self.plan.result.write(result, value, self.call.budget)?; }
        Ok(false)
    }
}

unsafe extern "C" fn callback_entry(
    context: *mut c_void,
    slots: *const *const u8,
    count: usize,
    result: *mut u8,
) -> VmNativeStatus {
    // SAFETY: the registered native implementation may use only this live
    // invocation's context, synchronously and without retaining it.
    let context = unsafe { &mut *context.cast::<CallbackContext<'_, '_>>() };
    let outcome = super::float_env::with_profile(|| {
        catch_unwind(AssertUnwindSafe(|| unsafe {
            context.invoke(slots, count, result)
        }))
        .unwrap_or_else(|_| Err(error("bytecode callback panicked")))
    });
    match outcome {
        Ok(()) => VmNativeStatus::Ok,
        Err(failure) => {
            if context.call.callback_failure.is_none() {
                context.call.callback_failure = Some(failure);
            }
            VmNativeStatus::Failed
        }
    }
}

pub(super) fn execute(
    program: &CandidateVmProgram,
    imports: Arc<BoundNativeImports>,
    capability: &str,
    symbol: &str,
    registers: &mut RuntimeRegisters,
    arguments: &[u32],
    destination: u32,
    budget: &mut ExecutionBudget,
    depth: u32,
    consumes_arguments: bool,
) -> Result<VmValue, VmArtifactError> {
    let binding = imports
        .imports
        .get(capability)
        .and_then(|imports| imports.get(symbol))
        .cloned()
        .ok_or_else(|| VmArtifactError::HostCallRequiresAuthority {
            capability: capability.into(),
            symbol: symbol.into(),
        })?;
    if arguments.len() != binding.parameters.len() {
        return Err(error("native import argument count mismatch"));
    }
    let mut owned_arguments = BTreeSet::new();
    for (register, plan) in arguments.iter().zip(&binding.parameters) {
        let value = registers[*register as usize]
            .as_ref()
            .ok_or_else(|| error("native argument is not initialized"))?;
        match (plan, value) {
            (ArgumentPlan::Owned(layout) | ArgumentPlan::Capture(layout), VmValue::Resident(home)) => {
                let initialized = if matches!(plan, ArgumentPlan::Capture(_)) { true }
                    else if binding.generated.is_some() { home.is_initialized(&[]) }
                    else { home.is_fully_initialized(&[]) };
                if home.ty() != &layout.ty || !initialized {
                    return Err(error(
                        "owned native argument has an invalid resident layout or initialization",
                    ));
                }
                if matches!(plan, ArgumentPlan::Owned(_)) && !owned_arguments.insert(*register) {
                    return Err(error(
                        "owned native arguments require distinct resident slots",
                    ));
                }
            }
            (ArgumentPlan::Owned(_) | ArgumentPlan::Capture(_), _) => {
                return Err(error(
                    "owned native argument requires an existing native home",
                ));
            }
            (ArgumentPlan::Value(layout), VmValue::Reference { target, .. })
                if matches!(layout.ty, VmType::Reference { .. }) =>
            {
                if !matches!(
                    target,
                    ReferenceTarget::Native(_) | ReferenceTarget::Home(_)
                ) {
                    return Err(error(
                        "native argument requires an existing addressable resident",
                    ));
                }
            }
            (ArgumentPlan::Callback(_), VmValue::Callable { .. }) => {}
            (ArgumentPlan::Callback(_), VmValue::Resident(home))
                if matches!(home.ty(), VmType::Callable { .. }) && home.is_fully_initialized(&[]) => {}
            (ArgumentPlan::Callback(_), _) => {
                return Err(error(
                    "native callbacks cannot be labels or resumption tokens",
                ));
            }
            _ => {}
        }
    }
    let result_home = if owned_resident(&binding.result.ty)
        || (binding.generated.is_some() && generated::resident(&binding.result.ty)) {
        let home = registers
            .native_homes
            .get(&destination)
            .cloned()
            .ok_or_else(|| error("owned native result requires a preallocated caller slot"))?;
        if home.ty() != &binding.result.ty {
            return Err(error("owned native result has a different layout"));
        }
        registers[destination as usize] = None;
        home.clear(&[]);
        Some(home)
    } else {
        None
    };
    let mut call = VmNativeCall {
        program,
        binding: binding.clone(),
        registers,
        arguments,
        budget,
        depth,
        result: None,
        result_home,
        callback_failure: None,
    };
    let outcome = super::float_env::with_profile(|| {
        catch_unwind(AssertUnwindSafe(|| (binding.function)(&mut call)))
            .unwrap_or_else(|_| Err(error("native implementation panicked")))
    });
    if let Some(failure) = call.callback_failure {
        return Err(failure);
    }
    outcome?;
    for register in owned_arguments {
        if call.registers[register as usize].is_some() {
            return Err(error(
                "native implementation did not take its owned argument",
            ));
        }
        if let Some(home) = call.registers.native_homes.get(&register) {
            home.clear(&[]);
        }
    }
    if consumes_arguments {
        for (register, plan) in arguments.iter().zip(&binding.parameters) {
            if !matches!(plan, ArgumentPlan::Capture(_)) {
                call.registers.retire_call_arguments(&[*register]);
            }
        }
    }
    match call.result {
        Some(value) => Ok(value),
        None if binding.result.ty == VmType::Unit => Ok(VmValue::Unit),
        None => Err(error("native implementation did not initialize its result")),
    }
}
