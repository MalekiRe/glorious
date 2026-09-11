//! Native homes for addressable VM locals. A home is established by ordinary
//! value initialization, not by a native call. Resident bytes are authoritative;
//! the separate state records only initialization and checked-reference origins.

use super::native_memory::{GeneratedInitialization, NativeFields, NativeLayout, NativeShape, ReferenceRead};
use super::native_profile::{AllocationKind, NativeAllocation, NativeMemoryMeasurements};
use super::{
    ExecutionBudget, VmArtifactError, VmFunction, VmInstruction,
    VmNominalCopyDescriptor, VmType, VmValue,
};
use grandiose_runtime::memory::{MemoryLayout, RawAllocation};
use std::{
    cell::{Cell, Ref, RefCell, RefMut},
    collections::{BTreeMap, BTreeSet, HashMap},
    ops::{Deref, DerefMut},
    rc::Rc,
    sync::{Arc, Weak},
};

fn error(message: &'static str) -> VmArtifactError {
    VmArtifactError::NativeMemory { message }
}

/// Allocations support explicit unsafe address adoption. Generated capture
/// inputs instead name the exact lent slot by its initialization sidecar; byte
/// equality cannot distinguish zero-sized owners or establish a capture loan.
#[derive(Debug, Default)]
pub(super) struct RegisteredHomes {
    pub(super) allocations: BTreeMap<usize, Weak<NativeHome>>,
    // Removal retains empty bucket backing, never an expired input authority.
    native_inputs: HashMap<usize, Weak<NativeHome>>,
}

pub(super) type HomeRegistry = Rc<RefCell<RegisteredHomes>>;

// One result slot per ordinary producing instruction. Handler payload tables
// are installed explicitly by the control engine.
pub(super) fn instruction_result(instruction: &VmInstruction) -> Option<u32> {
    match instruction {
        VmInstruction::ConstUnit { dst, .. }
        | VmInstruction::ConstI64 { dst, .. }
        | VmInstruction::ConstU8 { dst, .. }
        | VmInstruction::ConstU16 { dst, .. }
        | VmInstruction::ConstU32 { dst, .. }
        | VmInstruction::ConstU64 { dst, .. }
        | VmInstruction::ConstUsize { dst, .. }
        | VmInstruction::ConstU128 { dst, .. }
        | VmInstruction::ConstI8 { dst, .. }
        | VmInstruction::ConstI16 { dst, .. }
        | VmInstruction::ConstI32 { dst, .. }
        | VmInstruction::ConstIsize { dst, .. }
        | VmInstruction::ConstI128 { dst, .. }
        | VmInstruction::ConstF64 { dst, .. }
        | VmInstruction::ConstF32 { dst, .. }
        | VmInstruction::FloatIntrinsic { dst, .. }
        | VmInstruction::MemoryIntrinsic { dst, .. }
        | VmInstruction::IntIntrinsic { dst, .. }
        | VmInstruction::ConstBool { dst, .. }
        | VmInstruction::ConstChar { dst, .. }
        | VmInstruction::ConstText { dst, .. }
        | VmInstruction::ConstStaticData { dst, .. }
        | VmInstruction::StaticLen { dst, .. }
        | VmInstruction::TextByteLen { dst, .. }
        | VmInstruction::TextConcat { dst, .. }
        | VmInstruction::TextEq { dst, .. }
        | VmInstruction::TextFromUtf8Checked { dst, .. }
        | VmInstruction::TextAsBytes { dst, .. }
        | VmInstruction::CharFromU32Checked { dst, .. }
        | VmInstruction::CharToU32 { dst, .. }
        | VmInstruction::BytesLen { dst, .. }
        | VmInstruction::BytesConcat { dst, .. }
        | VmInstruction::BytesGet { dst, .. }
        | VmInstruction::BytesSlice { dst, .. }
        | VmInstruction::BytesFromArrayMove { dst, .. }
        | VmInstruction::BytesToArray { dst, .. }
        | VmInstruction::BytesUtf8ValidUpTo { dst, .. }
        | VmInstruction::Blake3 { dst, .. }
        | VmInstruction::StoreUsize { dst, .. }
        | VmInstruction::ArrayLen { dst, .. }
        | VmInstruction::ArrayElementIsInitialized { dst, .. }
        | VmInstruction::TakeArrayElement { dst, .. }
        | VmInstruction::ArrayGetBorrowShared { dst, .. }
        | VmInstruction::ArrayEmpty { dst, .. }
        | VmInstruction::U32CheckedAdd { dst, .. }
        | VmInstruction::U32CheckedSub { dst, .. }
        | VmInstruction::U32CheckedMul { dst, .. }
        | VmInstruction::U32CheckedDiv { dst, .. }
        | VmInstruction::U32CheckedRem { dst, .. }
        | VmInstruction::U32WrappingAdd { dst, .. }
        | VmInstruction::U32WrappingSub { dst, .. }
        | VmInstruction::U32WrappingMul { dst, .. }
        | VmInstruction::U32WrappingShl { dst, .. }
        | VmInstruction::U32WrappingShr { dst, .. }
        | VmInstruction::U32CheckedShl { dst, .. }
        | VmInstruction::U32CheckedShr { dst, .. }
        | VmInstruction::U32Eq { dst, .. }
        | VmInstruction::U32Lt { dst, .. }
        | VmInstruction::U32Le { dst, .. }
        | VmInstruction::U32ToUsize { dst, .. }
        | VmInstruction::UsizeToU32Checked { dst, .. }
        | VmInstruction::I64ToU32Checked { dst, .. }
        | VmInstruction::I64ToU32Wrapping { dst, .. }
        | VmInstruction::I64ToUsizeChecked { dst, .. }
        | VmInstruction::I64ToUsizeWrapping { dst, .. }
        | VmInstruction::I64ToU8Checked { dst, .. }
        | VmInstruction::I64ToU8Wrapping { dst, .. }
        | VmInstruction::I64ToU16Checked { dst, .. }
        | VmInstruction::I64ToU16Wrapping { dst, .. }
        | VmInstruction::I64ToI16Checked { dst, .. }
        | VmInstruction::I64ToI16Wrapping { dst, .. }
        | VmInstruction::I64ToI32Checked { dst, .. }
        | VmInstruction::I64ToI32Wrapping { dst, .. }
        | VmInstruction::I64ToI8Checked { dst, .. }
        | VmInstruction::I64ToI8Wrapping { dst, .. }
        | VmInstruction::I64ToU64Checked { dst, .. }
        | VmInstruction::I64ToU64Wrapping { dst, .. }
        | VmInstruction::I64ToIsizeChecked { dst, .. }
        | VmInstruction::I64ToIsizeWrapping { dst, .. }
        | VmInstruction::I64ToU128Checked { dst, .. }
        | VmInstruction::I64ToU128Wrapping { dst, .. }
        | VmInstruction::I64ToI128Checked { dst, .. }
        | VmInstruction::I64ToI128Wrapping { dst, .. }
        | VmInstruction::MakeTuple { dst, .. }
        | VmInstruction::MakeTupleOwned { dst, .. } | VmInstruction::MakeArrayOwned { dst, .. }
        | VmInstruction::MakeRecordOwned { dst, .. } | VmInstruction::MakeEnumOwned { dst, .. }
        | VmInstruction::MakeArray { dst, .. }
        | VmInstruction::MakeRecord { dst, .. }
        | VmInstruction::MakeEnum { dst, .. }
        | VmInstruction::ProjectRecord { dst, .. }
        | VmInstruction::TakeProjection { dst, .. }
        | VmInstruction::IsInitialized { dst, .. }
        | VmInstruction::DestroyCallable { dst, .. }
        | VmInstruction::ProjectTuple { dst, .. }
        | VmInstruction::ProjectArray { dst, .. }
        | VmInstruction::UpdateRecord { dst, .. }
        | VmInstruction::PatternTest { dst, .. }
        | VmInstruction::Perform { dst, .. } | VmInstruction::PerformOwned { dst, .. }
        | VmInstruction::ResumeReturn { dst, .. }
        | VmInstruction::CaptureResumption { dst, .. }
        | VmInstruction::Copy { dst, .. }
        | VmInstruction::RetainResumption { dst, .. }
        | VmInstruction::PrepareInvocation { dst, .. }
        | VmInstruction::CallPrepared { dst, .. }
        | VmInstruction::Store { dst, .. } | VmInstruction::StoreOwned { dst, .. }
        | VmInstruction::Move { dst, .. }
        | VmInstruction::Borrow { dst, .. }
        | VmInstruction::DerefCopy { dst, .. }
        | VmInstruction::DerefMove { dst, .. }
        | VmInstruction::DerefIsInitialized { dst, .. }
        | VmInstruction::NotBool { dst, .. }
        | VmInstruction::AddI64 { dst, .. }
        | VmInstruction::WrappingAddI64 { dst, .. }
        | VmInstruction::WrappingSubI64 { dst, .. }
        | VmInstruction::WrappingMulI64 { dst, .. }
        | VmInstruction::IntEqualI64 { dst, .. }
        | VmInstruction::IntLessI64 { dst, .. }
        | VmInstruction::IntGreaterI64 { dst, .. }
        | VmInstruction::BitAndI64 { dst, .. }
        | VmInstruction::BitAndU32 { dst, .. }
        | VmInstruction::BitAndU64 { dst, .. }
        | VmInstruction::BitXorI64 { dst, .. }
        | VmInstruction::IntShrI64 { dst, .. }
        | VmInstruction::BitOrI64 { dst, .. }
        | VmInstruction::BitNotI64 { dst, .. }
        | VmInstruction::ShlI64 { dst, .. }
        | VmInstruction::SubI64 { dst, .. }
        | VmInstruction::MulI64 { dst, .. }
        | VmInstruction::DivI64 { dst, .. }
        | VmInstruction::RemI64 { dst, .. }
        | VmInstruction::AddF64 { dst, .. }
        | VmInstruction::ConcatText { dst, .. }
        | VmInstruction::SubF64 { dst, .. }
        | VmInstruction::MulF64 { dst, .. }
        | VmInstruction::DivF64 { dst, .. }
        | VmInstruction::RemF64 { dst, .. }
        | VmInstruction::CompareI64 { dst, .. }
        | VmInstruction::CompareU32 { dst, .. }
        | VmInstruction::CompareU64 { dst, .. }
        | VmInstruction::CompareF64 { dst, .. }
        | VmInstruction::EqBool { dst, .. }
        | VmInstruction::NeBool { dst, .. }
        | VmInstruction::EqText { dst, .. }
        | VmInstruction::NeText { dst, .. }
        | VmInstruction::CompareChar { dst, .. }
        | VmInstruction::CallOwned { dst, .. }
        | VmInstruction::CallIndirectOwned { dst, .. }
        | VmInstruction::HostCallOwned { dst, .. }
        | VmInstruction::Call { dst, .. }
        | VmInstruction::HostCall { dst, .. }
        | VmInstruction::MakeCallable { dst, .. }
        | VmInstruction::MakeLabel { dst, .. }
        | VmInstruction::CallIndirect { dst, .. } => Some(*dst),
        _ => None,
    }
}

/// Visit runtime operand and result locals, including deferred control payloads.
/// Literal field indices, jump targets, and declaration metadata are not locals.
pub(super) fn visit_locals(instruction: &VmInstruction, mut visit: impl FnMut(u32)) {
    match instruction {
        VmInstruction::TailCallOwned { arguments, .. } => {
            for argument in arguments { visit(*argument); }
        }
        VmInstruction::DestroyCallable { dst, value } => { visit(*dst); visit(*value); }
        VmInstruction::DeclareResult { .. }
        | VmInstruction::DeclareFrameCleanup { .. }
        | VmInstruction::Jump { .. }
        | VmInstruction::UninstallHandler
        | VmInstruction::Forward
        | VmInstruction::Cancel
        | VmInstruction::Trap => {}
        VmInstruction::ConstUnit { dst, .. }
        | VmInstruction::ConstI64 { dst, .. }
        | VmInstruction::ConstU8 { dst, .. }
        | VmInstruction::ConstU16 { dst, .. }
        | VmInstruction::ConstU32 { dst, .. }
        | VmInstruction::ConstU64 { dst, .. }
        | VmInstruction::ConstUsize { dst, .. }
        | VmInstruction::ConstU128 { dst, .. }
        | VmInstruction::ConstI8 { dst, .. }
        | VmInstruction::ConstI16 { dst, .. }
        | VmInstruction::ConstI32 { dst, .. }
        | VmInstruction::ConstIsize { dst, .. }
        | VmInstruction::ConstI128 { dst, .. }
        | VmInstruction::ConstF64 { dst, .. }
        | VmInstruction::ConstF32 { dst, .. }
        | VmInstruction::ConstBool { dst, .. }
        | VmInstruction::ConstChar { dst, .. }
        | VmInstruction::ConstText { dst, .. }
        | VmInstruction::ConstStaticData { dst, .. }
        | VmInstruction::ArrayEmpty { dst, .. }
        | VmInstruction::CaptureResumption { dst, .. } => {
            visit(*dst);
        }
        VmInstruction::FloatIntrinsic { dst, arguments, .. }
        | VmInstruction::MemoryIntrinsic { dst, arguments, .. }
        | VmInstruction::IntIntrinsic { dst, arguments, .. }
        | VmInstruction::Perform { dst, arguments, .. } | VmInstruction::PerformOwned { dst, arguments, .. }
        | VmInstruction::CallOwned { dst, arguments, .. }
        | VmInstruction::HostCallOwned { dst, arguments, .. }
        | VmInstruction::Call { dst, arguments, .. }
        | VmInstruction::HostCall { dst, arguments, .. } => {
            visit(*dst);
            for local in arguments {
                visit(*local);
            }
        }
        VmInstruction::StaticLen { dst, value, .. }
        | VmInstruction::TextByteLen { dst, value, .. }
        | VmInstruction::TextFromUtf8Checked { dst, value, .. }
        | VmInstruction::TextAsBytes { dst, value, .. }
        | VmInstruction::CharFromU32Checked { dst, value, .. }
        | VmInstruction::CharToU32 { dst, value, .. }
        | VmInstruction::BytesLen { dst, value, .. }
        | VmInstruction::BytesFromArrayMove { dst, value, .. }
        | VmInstruction::BytesToArray { dst, value, .. }
        | VmInstruction::BytesUtf8ValidUpTo { dst, value, .. }
        | VmInstruction::Blake3 { dst, value, .. }
        | VmInstruction::U32ToUsize { dst, value, .. }
        | VmInstruction::UsizeToU32Checked { dst, value, .. }
        | VmInstruction::I64ToU32Checked { dst, value, .. }
        | VmInstruction::I64ToU32Wrapping { dst, value, .. }
        | VmInstruction::I64ToUsizeChecked { dst, value, .. }
        | VmInstruction::I64ToUsizeWrapping { dst, value, .. }
        | VmInstruction::I64ToU8Checked { dst, value, .. }
        | VmInstruction::I64ToU8Wrapping { dst, value, .. }
        | VmInstruction::I64ToU16Checked { dst, value, .. }
        | VmInstruction::I64ToU16Wrapping { dst, value, .. }
        | VmInstruction::I64ToI16Checked { dst, value, .. }
        | VmInstruction::I64ToI16Wrapping { dst, value, .. }
        | VmInstruction::I64ToI32Checked { dst, value, .. }
        | VmInstruction::I64ToI32Wrapping { dst, value, .. }
        | VmInstruction::I64ToI8Checked { dst, value, .. }
        | VmInstruction::I64ToI8Wrapping { dst, value, .. }
        | VmInstruction::I64ToU64Checked { dst, value, .. }
        | VmInstruction::I64ToU64Wrapping { dst, value, .. }
        | VmInstruction::I64ToIsizeChecked { dst, value, .. }
        | VmInstruction::I64ToIsizeWrapping { dst, value, .. }
        | VmInstruction::I64ToU128Checked { dst, value, .. }
        | VmInstruction::I64ToU128Wrapping { dst, value, .. }
        | VmInstruction::I64ToI128Checked { dst, value, .. }
        | VmInstruction::I64ToI128Wrapping { dst, value, .. }
        | VmInstruction::ResumeReturn { dst, value, .. }
        | VmInstruction::NotBool { dst, value, .. }
        | VmInstruction::BitNotI64 { dst, value, .. } => {
            visit(*dst);
            visit(*value);
        }
        VmInstruction::TextConcat {
            dst, left, right, ..
        }
        | VmInstruction::TextEq {
            dst, left, right, ..
        }
        | VmInstruction::BytesConcat {
            dst, left, right, ..
        }
        | VmInstruction::U32CheckedAdd {
            dst, left, right, ..
        }
        | VmInstruction::U32CheckedSub {
            dst, left, right, ..
        }
        | VmInstruction::U32CheckedMul {
            dst, left, right, ..
        }
        | VmInstruction::U32CheckedDiv {
            dst, left, right, ..
        }
        | VmInstruction::U32CheckedRem {
            dst, left, right, ..
        }
        | VmInstruction::U32WrappingAdd {
            dst, left, right, ..
        }
        | VmInstruction::U32WrappingSub {
            dst, left, right, ..
        }
        | VmInstruction::U32WrappingMul {
            dst, left, right, ..
        }
        | VmInstruction::U32WrappingShl {
            dst, left, right, ..
        }
        | VmInstruction::U32WrappingShr {
            dst, left, right, ..
        }
        | VmInstruction::U32CheckedShl {
            dst, left, right, ..
        }
        | VmInstruction::U32CheckedShr {
            dst, left, right, ..
        }
        | VmInstruction::U32Eq {
            dst, left, right, ..
        }
        | VmInstruction::U32Lt {
            dst, left, right, ..
        }
        | VmInstruction::U32Le {
            dst, left, right, ..
        }
        | VmInstruction::AddI64 {
            dst, left, right, ..
        }
        | VmInstruction::WrappingAddI64 {
            dst, left, right, ..
        }
        | VmInstruction::WrappingSubI64 {
            dst, left, right, ..
        }
        | VmInstruction::WrappingMulI64 {
            dst, left, right, ..
        }
        | VmInstruction::IntEqualI64 {
            dst, left, right, ..
        }
        | VmInstruction::IntLessI64 {
            dst, left, right, ..
        }
        | VmInstruction::IntGreaterI64 {
            dst, left, right, ..
        }
        | VmInstruction::BitAndI64 {
            dst, left, right, ..
        }
        | VmInstruction::BitAndU32 {
            dst, left, right, ..
        }
        | VmInstruction::BitAndU64 {
            dst, left, right, ..
        }
        | VmInstruction::BitXorI64 {
            dst, left, right, ..
        }
        | VmInstruction::IntShrI64 {
            dst, left, right, ..
        }
        | VmInstruction::BitOrI64 {
            dst, left, right, ..
        }
        | VmInstruction::SubI64 {
            dst, left, right, ..
        }
        | VmInstruction::MulI64 {
            dst, left, right, ..
        }
        | VmInstruction::DivI64 {
            dst, left, right, ..
        }
        | VmInstruction::RemI64 {
            dst, left, right, ..
        }
        | VmInstruction::AddF64 {
            dst, left, right, ..
        }
        | VmInstruction::ConcatText {
            dst, left, right, ..
        }
        | VmInstruction::SubF64 {
            dst, left, right, ..
        }
        | VmInstruction::MulF64 {
            dst, left, right, ..
        }
        | VmInstruction::DivF64 {
            dst, left, right, ..
        }
        | VmInstruction::RemF64 {
            dst, left, right, ..
        }
        | VmInstruction::CompareI64 {
            dst, left, right, ..
        }
        | VmInstruction::CompareU32 {
            dst, left, right, ..
        }
        | VmInstruction::CompareU64 {
            dst, left, right, ..
        }
        | VmInstruction::CompareF64 {
            dst, left, right, ..
        }
        | VmInstruction::EqBool {
            dst, left, right, ..
        }
        | VmInstruction::NeBool {
            dst, left, right, ..
        }
        | VmInstruction::EqText {
            dst, left, right, ..
        }
        | VmInstruction::NeText {
            dst, left, right, ..
        }
        | VmInstruction::CompareChar {
            dst, left, right, ..
        } => {
            visit(*dst);
            visit(*left);
            visit(*right);
        }
        VmInstruction::BytesGet {
            dst, bytes, index, ..
        } => {
            visit(*dst);
            visit(*bytes);
            visit(*index);
        }
        VmInstruction::BytesSlice {
            dst,
            bytes,
            start,
            end,
            ..
        } => {
            visit(*dst);
            visit(*bytes);
            visit(*start);
            visit(*end);
        }
        VmInstruction::StoreUsize { dst, value }
        | VmInstruction::ArrayLen { dst, value } => { visit(*dst); visit(*value); }
        VmInstruction::ArrayElementIsInitialized { dst, value, index }
        | VmInstruction::TakeArrayElement { dst, value, index } => {
            visit(*dst); visit(*value); visit(*index);
        }
        VmInstruction::ArrayGetBorrowShared {
            dst, value, index, ..
        } => {
            visit(*dst);
            visit(*value);
            visit(*index);
        }
        VmInstruction::ArrayPushMove { value, item, .. } => {
            visit(*value);
            visit(*item);
        }
        VmInstruction::MakeTuple { dst, fields, .. }
        | VmInstruction::MakeTupleOwned { dst, fields } | VmInstruction::MakeArrayOwned { dst, fields, .. }
        | VmInstruction::MakeRecordOwned { dst, fields, .. } | VmInstruction::MakeEnumOwned { dst, fields, .. }
        | VmInstruction::MakeArray { dst, fields, .. }
        | VmInstruction::MakeRecord { dst, fields, .. }
        | VmInstruction::MakeEnum { dst, fields, .. } => {
            visit(*dst);
            for local in fields {
                visit(*local);
            }
        }
        VmInstruction::ProjectRecord { dst, base, .. }
        | VmInstruction::TakeProjection { dst, base, .. }
        | VmInstruction::IsInitialized { dst, base, .. }
        | VmInstruction::ProjectTuple { dst, base, .. } => {
            visit(*dst);
            visit(*base);
        }
        VmInstruction::ProjectArray {
            dst, base, index, ..
        } => {
            visit(*dst);
            visit(*base);
            visit(*index);
        }
        VmInstruction::UpdateRecord {
            dst,
            base,
            index,
            value,
            ..
        } => {
            visit(*dst);
            visit(*base);
            visit(*index);
            visit(*value);
        }
        VmInstruction::PatternTest { dst, subject, .. } => {
            visit(*dst);
            visit(*subject);
        }
        VmInstruction::ClaimEffectPayloads { payloads: payload_destinations } |
        VmInstruction::InstallHandlerOwned {
            payload_destinations,
            ..
        }
        | VmInstruction::InstallHandler {
            payload_destinations,
            ..
        } => {
            for local in payload_destinations {
                visit(*local);
            }
        }
        VmInstruction::Resume { value, .. }
        | VmInstruction::Return { value, .. }
        | VmInstruction::CompleteHandler { value, .. } => {
            visit(*value);
        }
        VmInstruction::ResumeSnapshot {
            snapshot, value, ..
        } => {
            visit(*snapshot);
            visit(*value);
        }
        VmInstruction::RetainResumption { dst, src, .. }
        | VmInstruction::PrepareInvocation { dst, src, .. }
        | VmInstruction::Copy { dst, src, .. }
        | VmInstruction::Store { dst, src, .. } | VmInstruction::StoreOwned { dst, src }
        | VmInstruction::Move { dst, src, .. }
        | VmInstruction::Borrow { dst, src, .. } => {
            visit(*dst);
            visit(*src);
        }
        VmInstruction::StorageLive { local, .. } | VmInstruction::StorageDead { local, .. } => {
            visit(*local);
        }
        VmInstruction::SetDropFlag { flag, .. } => {
            visit(*flag);
        }
        VmInstruction::DestroyIf { local, flag, .. } => {
            visit(*local);
            visit(*flag);
        }
        VmInstruction::DerefCopy { dst, reference, .. }
        | VmInstruction::DerefMove { dst, reference, .. }
        | VmInstruction::DerefIsInitialized { dst, reference, .. } => {
            visit(*dst);
            visit(*reference);
        }
        VmInstruction::DerefStore { reference, src, .. } => {
            visit(*reference);
            visit(*src);
        }
        VmInstruction::ShlI64 {
            dst, value, count, ..
        } => {
            visit(*dst);
            visit(*value);
            visit(*count);
        }
        VmInstruction::MakeCallable { dst, captures, .. } => {
            visit(*dst);
            for local in captures {
                visit(*local);
            }
        }
        VmInstruction::MakeLabel {
            dst, destination, ..
        } => {
            visit(*dst);
            visit(*destination);
        }
        VmInstruction::CallIndirectOwned { dst, callee, arguments }
        | VmInstruction::CallPrepared { dst, callee, arguments }
        | VmInstruction::CallIndirect {
            dst,
            callee,
            arguments,
            ..
        } => {
            visit(*dst);
            visit(*callee);
            for local in arguments {
                visit(*local);
            }
        }
        VmInstruction::Leave {
            arguments,
            destinations,
            ..
        } => {
            for local in arguments {
                visit(*local);
            }
            for local in destinations {
                visit(*local);
            }
        }
        VmInstruction::BranchBool { condition, .. } => {
            visit(*condition);
        }
    }
}

pub(super) struct NativeFramePlan {
    pub(super) layouts: Vec<Option<Arc<NativeLayout>>>,
    /// Only values owning callable environments need independent interpreter
    /// storage on Copy. Ordinary immutable aggregates retain their COW path.
    pub(super) copy_environments: Vec<bool>,
    pub(super) results: Vec<Option<u32>>,
    pub(super) read_projections: Vec<Option<(u32, u32)>>,
    /// Owned native results need an uninitialized caller slot before execution
    /// reaches the call. This is frame storage, not a boundary transport buffer.
    pub(super) native_results: Vec<u32>,
    pub(super) native_return: bool,
}

impl NativeFramePlan {
    pub(super) fn new(
        function: &VmFunction,
        descriptors: &Arc<[VmNominalCopyDescriptor]>,
        native_return: bool,
    ) -> Self {
        let mut layouts = vec![None; function.registers.len()];
        fn owns_callable(ty: &VmType, descriptors: &[VmNominalCopyDescriptor], active: &mut Vec<VmType>) -> bool {
            match ty {
                VmType::Callable { .. } => true,
                VmType::Tuple(fields) => fields.iter().any(|field| owns_callable(field, descriptors, active)),
                VmType::Array(element) | VmType::FixedArray { element, .. } => owns_callable(element, descriptors, active),
                VmType::Nominal { definition, arguments } => {
                    if active.contains(ty) { return false; }
                    let Some(descriptor) = descriptors.iter().find(|descriptor|
                        descriptor.definition == *definition && descriptor.arguments == *arguments) else { return false; };
                    active.push(ty.clone());
                    let result = descriptor.variants.iter().flatten().any(|field| owns_callable(field, descriptors, active));
                    active.pop();
                    result
                }
                // References and pointers do not own their referents.
                _ => false,
            }
        }
        let copy_environments = function.registers.iter()
            .map(|ty| owns_callable(ty, descriptors, &mut vec![])).collect();
        let mut native_results = vec![];
        let mut resident_demands = vec![];
        let mut capture_homes = vec![];
        for instruction in &function.instructions {
            if let VmInstruction::MakeCallable { captures, environment: Some(environment), .. } = instruction {
                capture_homes.extend(captures.iter().zip(&environment.captures)
                    .filter(|(_, capture)| matches!(capture.mode, super::VmCaptureMode::SharedBorrow | super::VmCaptureMode::UniqueBorrow))
                    .map(|(local, _)| *local));
            }
            if native_return && let VmInstruction::Return { value } = instruction {
                resident_demands.push(*value);
            }
            if let VmInstruction::Borrow {
                src,
                reborrow: false,
                ..
            } = instruction
            {
                let layout = super::native_memory::native_layout(
                    &function.registers[*src as usize],
                    descriptors,
                    &mut vec![],
                );
                if let Ok(layout) = layout
                    && layout.supports_resident(descriptors)
                {
                    layouts[*src as usize] = Some(Arc::new(layout));
                }
            }
            if let VmInstruction::HostCall { dst, arguments, .. }
                | VmInstruction::HostCallOwned { dst, arguments, .. } = instruction {
                for &local in arguments.iter().chain(std::iter::once(dst)) {
                    if matches!(
                        function.registers[local as usize],
                        VmType::Tuple(_) | VmType::FixedArray { .. } | VmType::Nominal { .. }
                    ) {
                        resident_demands.push(local);
                        if local == *dst {
                            native_results.push(local);
                        }
                    }
                }
            }
        }
        // A borrowed capture and its invocation parameter are views of the
        // same address-stable source slot, including scalar assignments.
        for local in capture_homes {
            if let Ok(layout) = super::native_memory::native_layout(
                &function.registers[local as usize], descriptors, &mut vec![])
                && layout.supports_resident(descriptors)
            {
                layouts[local as usize] = Some(Arc::new(layout));
            }
        }
        // Establish ABI-visible values at their ordinary value producers,
        // including copies/moves preceding a call, not inside the bridge.
        let mut predecessors = vec![Vec::new(); function.registers.len()];
        for instruction in &function.instructions {
            match instruction {
                VmInstruction::Copy { dst, src }
                | VmInstruction::Move { dst, src }
                | VmInstruction::Store { dst, src } | VmInstruction::StoreOwned { dst, src } => predecessors[*dst as usize].push(*src),
                VmInstruction::MakeTuple { dst, fields }
                | VmInstruction::MakeTupleOwned { dst, fields }
                | VmInstruction::MakeRecordOwned { dst, fields, .. }
                | VmInstruction::MakeEnumOwned { dst, fields, .. }
                | VmInstruction::MakeRecord { dst, fields, .. }
                | VmInstruction::MakeEnum { dst, fields, .. } => {
                    predecessors[*dst as usize].extend(fields)
                }
                VmInstruction::UpdateRecord {
                    dst, base, value, ..
                } => predecessors[*dst as usize].extend([*base, *value]),
                _ => {}
            }
        }
        let mut visited = BTreeSet::new();
        while let Some(local) = resident_demands.pop() {
            if !visited.insert(local) {
                continue;
            }
            let ty = &function.registers[local as usize];
            if !matches!(ty, VmType::Tuple(_) | VmType::FixedArray { .. } | VmType::Nominal { .. } | VmType::Callable { .. }) {
                continue;
            }
            if let Ok(layout) = super::native_memory::native_layout(ty, descriptors, &mut vec![])
                && layout.supports_resident(descriptors)
            {
                layouts[local as usize] = Some(Arc::new(layout));
                resident_demands.extend(&predecessors[local as usize]);
            }
        }
        native_results.retain(|local| layouts[*local as usize].is_some());
        native_results.sort_unstable();
        native_results.dedup();
        let results = function
            .instructions
            .iter()
            .map(|instruction| {
                instruction_result(instruction).filter(|dst| layouts[*dst as usize].is_some() || *dst < function.captures)
            })
            .collect();
        let mut mentions = vec![0u8; function.registers.len()];
        for instruction in &function.instructions {
            visit_locals(instruction, |local| {
                if let Some(count) = mentions.get_mut(local as usize) {
                    *count = count.saturating_add(1);
                }
            });
        }
        let mut read_projections = vec![None; function.instructions.len()];
        for (pc, pair) in function.instructions.windows(2).enumerate() {
            if let VmInstruction::DerefCopy { dst: temporary, .. } = pair[0]
                && layouts[temporary as usize].is_none()
                && mentions[temporary as usize] == 2
                && let VmInstruction::ProjectRecord {
                    dst, base, index, ..
                }
                | VmInstruction::ProjectTuple {
                    dst, base, index, ..
                } = pair[1]
                && base == temporary
            {
                read_projections[pc] = Some((dst, index));
            }
        }
        Self {
            layouts,
            copy_environments,
            results,
            read_projections,
            native_results,
            native_return,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct Initialization {
    root: bool,
    holes: BTreeSet<Vec<u32>>,
    variants: BTreeMap<Vec<u32>, u32>,
}

/// Ownership of initialization moves with execution. While machine code owns
/// the mask, all VM/home accesses read and update those exact flags. The saved
/// state is inactive until the loan returns; it is never consulted as a shadow
/// mask. Nested engine entries restore the immediately enclosing owner.
#[derive(Debug, Default)]
struct InitializationStorage {
    owned: Initialization,
    active: Option<GeneratedInitialization>,
    // Only nested entries need backing. Popping a loan retains capacity, not
    // the loan's flag pointer or authority. The ordinary active loan is inline.
    suspended: Vec<GeneratedInitialization>,
}

impl InitializationStorage {
    fn snapshot(view: &GeneratedInitialization) -> Result<Initialization, VmArtifactError> {
        let mut holes = view.holes()?;
        let root = !holes.remove(&vec![]);
        Ok(Initialization { root, holes, variants: BTreeMap::new() })
    }

    fn install(&mut self, initialization: Initialization) -> Result<(), VmArtifactError> {
        match &self.active {
            None => { self.owned = initialization; Ok(()) }
            Some(view) => view.install(initialization.root, &initialization.holes),
        }
    }

    fn detach_inactive_loan(&mut self, identity: usize) -> bool {
        if let Some(index) = self.suspended.iter().position(|view| view.identity() == identity) {
            self.suspended.remove(index).expire();
            true
        } else { false }
    }
}

#[derive(Debug, Default)]
struct InitializationCell(RefCell<InitializationStorage>);

impl InitializationCell {
    fn borrow(&self) -> Result<InitializationRead<'_>, VmArtifactError> {
        let storage = self.0.borrow();
        let generated = storage.active.as_ref().map(InitializationStorage::snapshot).transpose()?;
        Ok(InitializationRead { storage, generated })
    }

    fn borrow_mut(&self) -> Result<InitializationWrite<'_>, VmArtifactError> {
        let storage = self.0.borrow_mut();
        let generated = storage.active.as_ref().map(InitializationStorage::snapshot).transpose()?;
        Ok(InitializationWrite { storage, generated })
    }

    fn clear(&self, path: &[u32]) {
        let mut storage = self.0.borrow_mut();
        match &storage.active {
            None => {
                let state = &mut storage.owned;
                if path.is_empty() { *state = Initialization::default(); }
                else {
                    state.holes.retain(|hole| !hole.starts_with(path));
                    state.holes.insert(path.to_vec());
                    state.variants.retain(|field, _| !field.starts_with(path));
                }
            }
            Some(view) => {
                // Retirement cannot grant read authority, even if an unsafe
                // producer supplied invalid flags. The view remains scoped.
                let _ = view.clear(path);
            }
        }
    }
}

struct InitializationRead<'a> {
    storage: Ref<'a, InitializationStorage>,
    generated: Option<Initialization>,
}

impl Deref for InitializationRead<'_> {
    type Target = Initialization;
    fn deref(&self) -> &Initialization {
        self.generated.as_ref().unwrap_or(&self.storage.owned)
    }
}

struct InitializationWrite<'a> {
    storage: RefMut<'a, InitializationStorage>,
    generated: Option<Initialization>,
}

impl Deref for InitializationWrite<'_> {
    type Target = Initialization;
    fn deref(&self) -> &Initialization {
        self.generated.as_ref().unwrap_or(&self.storage.owned)
    }
}

impl DerefMut for InitializationWrite<'_> {
    fn deref_mut(&mut self) -> &mut Initialization {
        self.generated.as_mut().unwrap_or(&mut self.storage.owned)
    }
}

impl Drop for InitializationWrite<'_> {
    fn drop(&mut self) {
        if let Some(state) = self.generated.take() {
            // The mutable borrow prevents the owning loan from expiring while
            // this short synchronous update holds its checked writable view.
            self.storage.install(state).expect("live native initialization write");
        }
    }
}

pub(super) struct NativeHomeLoan {
    home: Arc<NativeHome>,
    identity: Option<usize>,
}

impl NativeHomeLoan {
    pub(super) fn finish(mut self) -> Result<(), VmArtifactError> { self.restore() }

    fn restore(&mut self) -> Result<(), VmArtifactError> {
        let Some(identity) = self.identity.take() else { return Ok(()); };
        {
            let mut registry = self.home.registry.borrow_mut();
            if registry.native_inputs.len() == 1 && registry.native_inputs.contains_key(&identity) {
                // Reset tombstones along with the last live entry, preserving
                // reusable capacity across complete segment entries.
                registry.native_inputs.clear();
            } else { registry.native_inputs.remove(&identity); }
        }
        let mut storage = self.home.state.0.borrow_mut();
        let Some(view) = storage.active.take() else {
            return Err(error("native initialization loan lost its owner"));
        };
        if view.identity() != identity {
            storage.active = Some(view);
            // An invalid return order still cannot leave this caller's expired
            // sidecar in the chain used by the later, active loan.
            storage.detach_inactive_loan(identity);
            return Err(error("native initialization loans returned out of order"));
        }
        let snapshot = InitializationStorage::snapshot(&view);
        view.expire();
        storage.active = storage.suspended.pop();
        match snapshot {
            Ok(snapshot) => storage.install(snapshot),
            Err(failure) => {
                // Never leave a flag pointer reachable after its stack expires.
                storage.install(Initialization::default())?;
                Err(failure)
            }
        }
    }
}

impl Drop for NativeHomeLoan {
    fn drop(&mut self) { let _ = self.restore(); }
}

/// Owning a source slot and borrowing its bytes have different retirement
/// authority, even though both expose the same resident/initialization API.
#[derive(Debug)]
enum StorageAuthority {
    Owned,
    ExternalArgument,
}

/// Private scalar spills have no resident identity, reference origins, or
/// initialization authority beyond one generated segment. Keep their raw
/// backing separate from source homes; snapshots retain scalar values only.
#[derive(Debug)]
pub(super) struct NativeScalarSpills {
    allocation: NativeAllocation,
    live_bytes: Rc<Cell<usize>>,
}

impl NativeScalarSpills {
    pub(super) fn acquire(layout: MemoryLayout, scratch_bytes: usize,
        budget: &mut ExecutionBudget,
    ) -> Result<Self, VmArtifactError> {
        if let Some(spills) = budget.native_memory.scalar_spills.take() {
            let available = budget.native_memory.live_native_bytes().checked_add(scratch_bytes)
                .is_some_and(|bytes| bytes as u64 <= budget.limits.max_native_bytes);
            let backing = spills.allocation.layout();
            if backing.size() == layout.size() && backing.alignment() >= layout.alignment()
                && backing.size() as u64 <= budget.limits.max_native_allocation_bytes && available {
                return Ok(spills);
            }
            // An oversized idle buffer may not force a smaller live frame
            // over its byte ceiling. Release it before admitting exact backing.
            drop(spills);
        }
        let available = budget.limits.max_native_bytes
            .saturating_sub(budget.native_memory.live_native_bytes() as u64)
            .saturating_sub(scratch_bytes as u64)
            .min(budget.limits.max_native_allocation_bytes);
        let allocation = RawAllocation::new(layout, usize::try_from(available).unwrap_or(usize::MAX))
            .map_err(super::native_memory::memory_error)?;
        let allocation = NativeAllocation::new(allocation,
            budget.native_memory.measurements.clone(), AllocationKind::Home);
        budget.reserve_value("native scalar spill backing", 1)?;
        let live_bytes = budget.native_memory.home_bytes.clone();
        live_bytes.set(live_bytes.get().checked_add(layout.size())
            .ok_or_else(|| error("native scalar spill size overflow"))?);
        Ok(Self { allocation, live_bytes })
    }

    pub(super) fn slot(&self, offset: usize, layout: &NativeLayout) -> Result<*mut u8, VmArtifactError> {
        if !matches!(layout.shape, NativeShape::Scalar)
            || offset.checked_add(layout.memory.size()).is_none_or(|end| end > self.allocation.layout().size())
            || self.allocation.layout().alignment() < layout.memory.alignment()
            || offset % layout.memory.alignment() != 0 {
            return Err(error("invalid private native scalar spill layout"));
        }
        // The checked extent and alignment come from the sealed native plan.
        Ok(unsafe { self.allocation.as_ptr().as_ptr().add(offset) })
    }

    pub(super) fn store(&self, offset: usize, layout: &NativeLayout, value: Option<&VmValue>,
        budget: &mut ExecutionBudget,
    ) -> Result<bool, VmArtifactError> {
        let pointer = self.slot(offset, layout)?;
        let Some(value) = value else { return Ok(false); };
        if !super::vm_type_matches(&super::borrowed_value_type(value, &layout.ty), &layout.ty) {
            return Err(error("native scalar spill value has a different concrete type"));
        }
        let value = match value {
            VmValue::Uninitialized(_) => return Ok(false),
            VmValue::Resident(home) => {
                home.project(&[])?;
                if !home.is_initialized(&[]) { return Ok(false); }
                home.scalar_value()?
            }
            value => value.clone(),
        };
        // This is private scalar storage, with no resident/reference metadata
        // or outstanding addressable owner. The layout validates scalar bits.
        unsafe { layout.write(pointer, value, budget)?; }
        Ok(true)
    }

    /// # Safety
    /// A flag of one must come from successful scalar storage or the verified
    /// generated segment's current initialization mask. It certifies initialized
    /// bytes for this exact layout; Bool/Char value validity is checked here.
    pub(super) unsafe fn load(&self, offset: usize, layout: &NativeLayout, initialized: u8,
        budget: &mut ExecutionBudget,
    ) -> Result<Option<VmValue>, VmArtifactError> {
        let pointer = self.slot(offset, layout)?;
        match initialized {
            0 => Ok(None),
            // Only the generated segment's current flag permits a read; old
            // backing bytes alone never establish an initialized register.
            1 => unsafe { layout.read(pointer, budget).map(Some) },
            _ => Err(error("invalid native scalar spill initialization flag")),
        }
    }

    pub(super) fn release(self, budget: &mut ExecutionBudget) {
        // Re-entry owns a separate buffer while the outer segment is active.
        // Keep at most one idle allocation, and never any of its value/mask
        // authority. Every next segment reconstructs those from its registers.
        budget.native_memory.scalar_spills = Some(self);
    }
}

impl Drop for NativeScalarSpills {
    fn drop(&mut self) {
        self.live_bytes.set(self.live_bytes.get() - self.allocation.layout().size());
    }
}

#[derive(Debug)]
pub(super) struct NativeHome {
    allocation: RefCell<Option<NativeAllocation>>,
    pointer: *mut u8,
    live: Cell<bool>,
    authority: StorageAuthority,
    pub(super) layout: Arc<NativeLayout>,
    state: InitializationCell,
    address_exposed: Cell<bool>,
    live_bytes: Rc<Cell<usize>>,
    measurements: Option<Rc<NativeMemoryMeasurements>>,
    registry: HomeRegistry,
    residents: std::rc::Weak<super::native_residents::ResidentMetadata>,
}

impl Drop for NativeHome {
    fn drop(&mut self) {
        self.retire();
    }
}

impl NativeHome {
    pub(super) fn new(
        layout: Arc<NativeLayout>,
        budget: &mut ExecutionBudget,
    ) -> Result<Arc<Self>, VmArtifactError> {
        let bytes = layout.memory.size();
        budget.native_memory.reclaim_idle_spills(bytes,
            usize::try_from(budget.limits.max_native_bytes).unwrap_or(usize::MAX));
        let available = budget
            .limits
            .max_native_bytes
            .saturating_sub(budget.native_memory.live_native_bytes() as u64)
            .min(budget.limits.max_native_allocation_bytes);
        let allocation = RawAllocation::new(
            layout.memory,
            usize::try_from(available).unwrap_or(usize::MAX),
        )
        .map_err(super::native_memory::memory_error)?;
        // Track immediately: a later logical-budget rejection still allocated
        // and then released these bytes. The owner handles both return paths.
        let allocation = NativeAllocation::new(allocation,
            budget.native_memory.measurements.clone(), AllocationKind::Home);
        budget.reserve_value("native storage home", 1)?;
        let live_bytes = budget.native_memory.home_bytes.clone();
        live_bytes.set(
            live_bytes
                .get()
                .checked_add(bytes)
                .ok_or_else(|| error("native storage size overflow"))?,
        );
        let home = Arc::new(Self {
            pointer: allocation.as_ptr().as_ptr(),
            allocation: RefCell::new(Some(allocation)),
            live: Cell::new(true),
            authority: StorageAuthority::Owned,
            layout,
            state: InitializationCell::default(),
            address_exposed: Cell::new(false),
            live_bytes,
            measurements: budget.native_memory.measurements.clone(),
            registry: budget.native_memory.homes.clone(),
            residents: Rc::downgrade(&budget.native_memory.residents),
        });
        if bytes != 0 {
            home.registry
                .borrow_mut()
                .allocations.insert(home.pointer().addr(), Arc::downgrade(&home));
        }
        Ok(home)
    }

    pub(super) fn pointer(&self) -> *mut u8 {
        self.pointer
    }

    /// Bind a synchronously owned native argument to its existing storage.
    /// The native caller owns the allocation; this view owns only the source
    /// resident obligation during bytecode execution and never frees the slot.
    pub(super) unsafe fn external_argument(
        layout: Arc<NativeLayout>,
        pointer: *mut u8,
        budget: &mut ExecutionBudget,
    ) -> Result<Arc<Self>, VmArtifactError> {
        unsafe { Self::argument_with_reference_admission(layout, pointer, budget, None, ReferenceRead::External) }
    }

    unsafe fn argument_with_reference_admission(layout: Arc<NativeLayout>, pointer: *mut u8,
        budget: &mut ExecutionBudget, holes: Option<&BTreeSet<Vec<u32>>>, admission: ReferenceRead,
    ) -> Result<Arc<Self>, VmArtifactError> {
        budget.reserve_value("native argument storage view", 1)?;
        let pointer = if layout.memory.size() == 0 {
            std::ptr::without_provenance_mut(layout.memory.alignment())
        } else {
            pointer
        };
        let home = Arc::new(Self {
            allocation: RefCell::new(None),
            pointer,
            live: Cell::new(true),
            authority: StorageAuthority::ExternalArgument,
            layout,
            state: InitializationCell::default(),
            address_exposed: Cell::new(true),
            live_bytes: budget.native_memory.home_bytes.clone(),
            measurements: budget.native_memory.measurements.clone(),
            registry: budget.native_memory.homes.clone(),
            residents: Rc::downgrade(&budget.native_memory.residents),
        });
        unsafe {
            home.initialize_with_reference_admission(budget, holes, admission)?;
        }
        Ok(home)
    }

    pub(super) fn is_external(&self) -> bool {
        matches!(self.authority, StorageAuthority::ExternalArgument)
    }

    fn is_live(&self) -> bool {
        self.live.get()
    }

    /// Transfer initialization to a generated capture input. The sidecar is the
    /// input's logical identity even when multiple homes have no payload bytes.
    /// The guard must return before the caller releases that writable sidecar.
    pub(super) unsafe fn lend_native(self: &Arc<Self>, flags: *mut u8,
        paths: Arc<[Vec<u32>]>, budget: &mut ExecutionBudget,
    ) -> Result<NativeHomeLoan, VmArtifactError> {
        self.project(&[])?;
        let view = unsafe { GeneratedInitialization::new(flags, paths)? };
        let identity = view.identity();
        let mut registry = self.registry.borrow_mut();
        if registry.native_inputs.contains_key(&identity) {
            return Err(error("native capture sidecar already has a resident owner"));
        }
        let mut storage = self.state.0.borrow_mut();
        if registry.native_inputs.len() == registry.native_inputs.capacity() {
            // Charge the actual new bucket capacity before publishing it. A
            // rejected growth leaves both the old table and loan state intact.
            let mut grown = HashMap::with_capacity(registry.native_inputs.len() + 1);
            budget.reserve_value("native resident input registry", grown.capacity())?;
            grown.extend(registry.native_inputs.drain());
            registry.native_inputs = grown;
        }
        if storage.active.is_some() && storage.suspended.len() == storage.suspended.capacity() {
            budget.reserve_value("nested native initialization loans", storage.suspended.len() + 1)?;
            storage.suspended.reserve_exact(1);
        }
        if let Some(previous) = storage.active.replace(view) {
            storage.suspended.push(previous);
        }
        registry.native_inputs.insert(identity, Arc::downgrade(self));
        Ok(NativeHomeLoan { home: self.clone(), identity: Some(identity) })
    }

    /// Resolve the exact input established by `lend_native`. Both generated
    /// borrowing and VM re-entry use this existing home and its active mask;
    /// neither invents an owned view or infers identity from byte addresses.
    pub(super) fn capture_loan(
        layout: Arc<NativeLayout>, pointer: *mut u8, flags: *const u8, budget: &ExecutionBudget,
    ) -> Result<Arc<Self>, VmArtifactError> {
        let home = budget.native_memory.homes.borrow().native_inputs.get(&flags.addr()).and_then(Weak::upgrade)
            .ok_or_else(|| error("generated capture input has no live resident owner"))?;
        if home.ty() != &layout.ty || home.pointer() != pointer {
            return Err(error("generated capture input has a different owner layout or address"));
        }
        home.project(&[])?;
        home.state.borrow()?;
        Ok(home)
    }

    /// Adopt a value constructed directly in this uninitialized native slot.
    /// The unsafe producer supplies valid resident/loan/ownership obligations;
    /// this walk validates bits and records origins without rebuilding a value.
    pub(super) unsafe fn initialize_native(
        &self,
        budget: &mut ExecutionBudget,
    ) -> Result<(), VmArtifactError> {
        unsafe { self.initialize_with_reference_admission(budget, None, ReferenceRead::External) }
    }

    unsafe fn initialize_with_reference_admission(&self, budget: &mut ExecutionBudget,
        holes: Option<&BTreeSet<Vec<u32>>>, admission: ReferenceRead,
    ) -> Result<(), VmArtifactError> {
        fn visit(
            home: &NativeHome,
            layout: &NativeLayout,
            pointer: *const u8,
            path: &mut Vec<u32>,
            budget: &mut ExecutionBudget,
            holes: Option<&BTreeSet<Vec<u32>>>,
            admission: ReferenceRead,
        ) -> Result<(), VmArtifactError> {
            budget.tick()?;
            if holes.is_some_and(|holes| holes.contains(path)) {
                home.state.borrow_mut()?.holes.insert(path.clone());
                return Ok(());
            }
            let (offset, fields) = match &layout.shape {
                NativeShape::Product(fields) => (0, fields),
                NativeShape::Enum {
                    payload_offset,
                    variants,
                } => {
                    let tag = unsafe { pointer.cast::<u32>().read() };
                    let fields = variants
                        .get(tag as usize)
                        .ok_or_else(|| error("invalid native enum discriminant"))?;
                    home.state.borrow_mut()?.variants.insert(path.clone(), tag);
                    (*payload_offset, fields)
                }
                NativeShape::Scalar | NativeShape::StaticData | NativeShape::Callable | NativeShape::Reference { .. } => {
                    let value = unsafe { layout.read_with_reference_admission(pointer, budget, admission)? };
                    if matches!(value, VmValue::Reference { .. }) {
                        // Unsafe external adoption establishes the raw loan once;
                        // all later transport uses the shared resident identity.
                        unsafe { budget.native_memory.residents.write_reference(pointer.cast_mut(), &value, false, false)?; }
                    }
                    return Ok(());
                }
            };
            for (index, field) in fields.iter().enumerate() {
                path.push(index as u32);
                visit(
                    home,
                    &field.layout,
                    unsafe { pointer.add(offset + field.offset) },
                    path,
                    budget,
                    holes,
                    admission,
                )?;
                path.pop();
            }
            Ok(())
        }
        if !self.is_live() {
            return Err(error("native storage lifetime has ended"));
        }
        // Adoption validates existing resident bytes; it must not revoke
        // callable leases supplied by the producer before reading them.
        *self.state.borrow_mut()? = Initialization::default();
        if let Err(failure) = visit(self, &self.layout, self.pointer(), &mut vec![], budget, holes, admission) {
            self.clear(&[]);
            return Err(failure);
        }
        self.state.borrow_mut()?.root = !holes.is_some_and(|holes| holes.contains(&vec![]));
        Ok(())
    }
    /// Lexical storage death releases bytes even when dead SSA reference
    /// carriers still retain validation metadata. Such carriers cannot revive
    /// the owner: its initialization is cleared before its allocation goes.
    pub(super) fn retire(&self) {
        if !self.live.get() { return; }
        self.clear(&[]);
        self.live.set(false);
        let allocation = self.allocation.borrow_mut().take();
        if let Some(allocation) = allocation {
            drop(allocation);
            self.live_bytes
                .set(self.live_bytes.get() - self.layout.memory.size());
            if self.layout.memory.size() != 0 {
                self.registry.borrow_mut().allocations.remove(&self.pointer.addr());
            }
        }
    }
    pub(super) fn ty(&self) -> &VmType {
        &self.layout.ty
    }
    pub(super) fn expose_address(&self) {
        self.address_exposed.set(true);
    }
    /// Export initialized resident bytes, preserving padding and actual stored
    /// pointers. This is a semantic raw move/copy, never a boundary adapter.
    /// The caller supplies writable, aligned storage of this exact layout.
    pub(super) unsafe fn write_bytes(&self, destination: *mut u8) -> Result<(), VmArtifactError> {
        if !self.is_fully_initialized(&[]) {
            return Err(error("native write requires a fully initialized resident"));
        }
        unsafe { self.write_bytes_with_sidecar(destination) }
    }

    /// Move resident bytes including holes only together with a separately
    /// checked initialization sidecar. The generated tail packet uses this
    /// private extension; ordinary native results still require complete owners.
    pub(super) unsafe fn write_bytes_with_sidecar(&self, destination: *mut u8) -> Result<(), VmArtifactError> {
        if !self.is_live() {
            return Err(error("native storage lifetime has ended"));
        }
        let state = self.state.borrow()?;
        if !state.root {
            return Err(error("native sidecar write requires a live resident root"));
        }
        if let Some(callables) = self.residents.upgrade() {
            callables.expose_references(self.pointer().addr(), self.layout.memory.size())?;
        }
        unsafe {
            std::ptr::copy(self.pointer(), destination, self.layout.memory.size());
        }
        if let Some(callables) = self.residents.upgrade() {
            callables.copy(self.pointer().addr(), destination.addr(), self.layout.memory.size());
        }
        if let Some(measurements) = &self.measurements {
            measurements.copied(AllocationKind::Home, self.layout.memory.size());
        }
        Ok(())
    }
    pub(super) fn address_was_exposed(&self) -> bool {
        self.address_exposed.get()
    }
    pub(super) fn contains_address(&self, pointer: *const u8) -> bool {
        pointer.addr() >= self.pointer().addr()
            && pointer.addr()
                <= self
                    .pointer()
                    .addr()
                    .saturating_add(self.layout.memory.size())
    }

    pub(super) fn has_reference_fields(
        &self,
        budget: &mut ExecutionBudget,
    ) -> Result<bool, VmArtifactError> {
        fn inspect(
            layout: &NativeLayout,
            budget: &mut ExecutionBudget,
        ) -> Result<bool, VmArtifactError> {
            budget.tick()?;
            match &layout.shape {
                NativeShape::Reference { .. } | NativeShape::Callable => Ok(true),
                NativeShape::Product(fields) => {
                    for field in fields.distinct() {
                        if inspect(&field.layout, budget)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                NativeShape::Enum { variants, .. } => {
                    for field in variants.iter().flat_map(|fields| fields.distinct()) {
                        if inspect(&field.layout, budget)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                NativeShape::Scalar | NativeShape::StaticData => Ok(false),
            }
        }
        inspect(&self.layout, budget)
    }

    /// Scalar register reads allocate no transport object. Aggregate loads
    /// use the budgeted path below, and checked references preserve origins.
    pub(super) fn scalar_value(&self) -> Result<VmValue, VmArtifactError> {
        if !self.is_initialized(&[]) {
            return Err(error("native scalar storage is uninitialized"));
        }
        let pointer = self.pointer();
        macro_rules! read {
            ($rust:ty, $variant:ident) => {
                Ok(VmValue::$variant(unsafe { pointer.cast::<$rust>().read() }))
            };
        }
        match self.ty() {
            VmType::Unit => Ok(VmValue::Unit),
            VmType::I8 => read!(i8, I8),
            VmType::U8 => read!(u8, U8),
            VmType::I16 => read!(i16, I16),
            VmType::U16 => read!(u16, U16),
            VmType::I32 => read!(i32, I32),
            VmType::U32 => read!(u32, U32),
            VmType::I64 => read!(i64, I64),
            VmType::U64 => read!(u64, U64),
            VmType::I128 => read!(i128, I128),
            VmType::U128 => read!(u128, U128),
            VmType::Isize => read!(i64, Isize),
            VmType::Usize => read!(u64, Usize),
            VmType::F32 => read!(f32, F32),
            VmType::F64 => read!(f64, F64),
            VmType::Bool => match unsafe { pointer.read() } {
                0 => Ok(VmValue::Bool(false)),
                1 => Ok(VmValue::Bool(true)),
                _ => Err(error("invalid native boolean")),
            },
            VmType::Char => char::from_u32(unsafe { pointer.cast::<u32>().read() })
                .map(VmValue::Char)
                .ok_or_else(|| error("invalid native character")),
            VmType::RawPointer { .. } => Ok(VmValue::RawPointer {
                pointer: unsafe { pointer.cast::<*mut u8>().read() },
                signature: self.ty().clone(),
            }),
            _ => Err(error("native storage is not a scalar")),
        }
    }

    pub(super) fn is_initialized(&self, path: &[u32]) -> bool {
        self.is_live() && self.state.borrow().is_ok_and(|state|
            state.root && !state.holes.iter().any(|hole| path.starts_with(hole)))
    }

    pub(super) fn is_fully_initialized(&self, path: &[u32]) -> bool {
        self.is_live() && self.state.borrow().is_ok_and(|state| state.root
            && !state
                .holes
                .iter()
                .any(|hole| path.starts_with(hole) || hole.starts_with(path)))
    }

    /// Generated byte operations supply their checked logical mask separately
    /// from payload transport. Do not reconstruct scalar values to adopt it.
    pub(super) fn replace_initialization(&self, path: &[u32], holes: &BTreeSet<Vec<u32>>)
        -> Result<(), VmArtifactError>
    {
        self.project(path)?;
        let mut state = self.state.borrow_mut()?;
        if !path.is_empty() && (!state.root || state.holes.iter().any(|hole|
            hole.len() < path.len() && path.starts_with(hole))) {
            return Err(error("native storage field cannot initialize an absent parent"));
        }
        if path.is_empty() {
            state.root = !holes.contains(&vec![]);
        }
        state.holes.retain(|hole| !hole.starts_with(path));
        state.holes.extend(holes.iter().map(|hole| path.iter().chain(hole).copied().collect()));
        state.variants.retain(|field, _| !field.starts_with(path));
        Ok(())
    }

    pub(super) fn clear(&self, path: &[u32]) {
        if !self.is_live() { return; }
        if let Some(callables) = self.residents.upgrade() {
            if path.is_empty() {
                callables.clear(self.pointer.addr(), self.layout.memory.size());
            } else if let Ok((pointer, layout)) = self.project(path) {
                callables.clear(pointer.addr(), layout.memory.size());
            }
        }
        self.state.clear(path);
    }

    /// Observe an enum tag written by native code. A valid native replacement
    /// initializes its complete new variant; moved-out state of an earlier
    /// variant cannot be applied to unrelated payload fields.
    fn variant(
        &self,
        path: &[u32],
        pointer: *const u8,
        count: usize,
    ) -> Result<u32, VmArtifactError> {
        if !self.is_initialized(path) {
            return Err(error("native storage enum is uninitialized"));
        }
        let tag = unsafe { pointer.cast::<u32>().read() };
        if tag as usize >= count {
            return Err(error("invalid native enum discriminant"));
        }
        let mut state = self.state.borrow_mut()?;
        if state
            .variants
            .insert(path.to_vec(), tag)
            .is_some_and(|old| old != tag)
        {
            state.holes.retain(|hole| !hole.starts_with(path));
            state
                .variants
                .retain(|field, _| field.as_slice() == path || !field.starts_with(path));
        }
        Ok(tag)
    }

    pub(super) fn project(
        &self,
        path: &[u32],
    ) -> Result<(*mut u8, Arc<NativeLayout>), VmArtifactError> {
        if !self.is_live() {
            return Err(error("native storage lifetime has ended"));
        }
        let mut pointer = self.pointer();
        let mut layout = self.layout.clone();
        for (depth, &index) in path.iter().enumerate() {
            let (offset, fields) = match &layout.shape {
                NativeShape::Product(fields) => (0, fields),
                NativeShape::Enum {
                    payload_offset,
                    variants,
                } => {
                    let tag = self.variant(&path[..depth], pointer, variants.len())?;
                    (*payload_offset, &variants[tag as usize])
                }
                _ => return Err(error("native storage projection has no fields")),
            };
            let field = fields
                .get(index as usize)
                .ok_or_else(|| error("native storage field is out of range"))?;
            pointer = unsafe { pointer.add(offset + field.offset) };
            layout = field.layout.clone();
        }
        Ok((pointer, layout))
    }

    pub(super) fn field_count(&self, path: &[u32]) -> Result<usize, VmArtifactError> {
        let (pointer, layout) = self.project(path)?;
        match &layout.shape {
            NativeShape::Product(fields) => Ok(fields.len()),
            NativeShape::Enum { variants, .. } => {
                Ok(variants[self.variant(path, pointer, variants.len())? as usize].len())
            }
            _ => Err(error("native storage has no fields")),
        }
    }

    /// Recover only exact typed subobjects of a known live home. The ABI
    /// still carries genuine pointers; this lookup restores validation state,
    /// never a guest integer handle or a copied payload.
    pub(super) fn find_path(
        &self,
        pointer: *mut u8,
        ty: &VmType,
    ) -> Result<Option<Vec<u32>>, VmArtifactError> {
        fn visit(
            home: &NativeHome,
            layout: &NativeLayout,
            at: *mut u8,
            target: *mut u8,
            ty: &VmType,
            path: &mut Vec<u32>,
        ) -> Result<Option<Vec<u32>>, VmArtifactError> {
            if at == target && &layout.ty == ty {
                return Ok(Some(path.clone()));
            }
            if target.addr() < at.addr()
                || target.addr() > at.addr().saturating_add(layout.memory.size())
            {
                return Ok(None);
            }
            let (offset, fields) = match &layout.shape {
                NativeShape::Product(fields) => (0, fields),
                NativeShape::Enum {
                    payload_offset,
                    variants,
                } => {
                    if !home.is_initialized(path) {
                        return Ok(None);
                    }
                    (
                        *payload_offset,
                        &variants[home.variant(path, at, variants.len())? as usize],
                    )
                }
                _ => return Ok(None),
            };
            // Repeated array metadata must also support address lookup without
            // scanning N fields. At a boundary the preceding element can own
            // a trailing zero-sized field, so inspect at most two candidates.
            let (indices, previous) = match fields {
                NativeFields::Repeated { count: 0, .. } => return Ok(None),
                NativeFields::Repeated { count, stride, .. } => {
                    let relative = target.addr().saturating_sub(at.addr() + offset);
                    let index = if *stride == 0 { 0 } else { (relative / stride).min(count - 1) };
                    (index..index + 1, index.checked_sub(1).filter(|_| *stride != 0 && relative % stride == 0))
                }
                NativeFields::Explicit(_) => (0..fields.len(), None),
            };
            for index in indices.chain(previous) {
                let field = fields.get(index).expect("admitted native product index");
                path.push(index as u32);
                let found = visit(
                    home,
                    &field.layout,
                    unsafe { at.add(offset + field.offset) },
                    target,
                    ty,
                    path,
                )?;
                path.pop();
                if found.is_some() {
                    return Ok(found);
                }
            }
            Ok(None)
        }
        visit(self, &self.layout, self.pointer(), pointer, ty, &mut vec![])
    }

    pub(super) fn load(
        &self,
        path: &[u32],
        budget: &mut ExecutionBudget,
    ) -> Result<VmValue, VmArtifactError> {
        let (pointer, layout) = self.project(path)?;
        if !self.is_initialized(path) {
            return Ok(VmValue::Uninitialized(layout.ty.clone()));
        }
        if matches!(
            layout.shape,
            NativeShape::Scalar | NativeShape::StaticData | NativeShape::Callable | NativeShape::Reference { .. }
        ) {
            return unsafe { layout.read(pointer, budget) };
        }
        self.load_at(&layout, pointer, &mut path.to_vec(), budget)
    }

    fn load_at(
        &self,
        layout: &NativeLayout,
        pointer: *const u8,
        path: &mut Vec<u32>,
        budget: &mut ExecutionBudget,
    ) -> Result<VmValue, VmArtifactError> {
        if !self.is_initialized(path) {
            return Ok(VmValue::Uninitialized(layout.ty.clone()));
        }
        let (offset, fields, variant) = match &layout.shape {
            NativeShape::Product(fields) => (0, fields, None),
            NativeShape::Enum {
                payload_offset,
                variants,
            } => {
                let tag = self.variant(path, pointer, variants.len())?;
                (*payload_offset, &variants[tag as usize], Some(tag))
            }
            _ => return unsafe { layout.read(pointer, budget) },
        };
        budget.reserve_value("native storage load fields", fields.len())?;
        let mut values = Vec::with_capacity(fields.len());
        for (index, field) in fields.iter().enumerate() {
            path.push(index as u32);
            let value = self.load_at(
                &field.layout,
                unsafe { pointer.add(offset + field.offset) },
                path,
                budget,
            )?;
            path.pop();
            values.push(value);
        }
        Ok(match (&layout.ty, variant) {
            (VmType::Tuple(_), None) => VmValue::Tuple(values.into()),
            (VmType::FixedArray { .. }, None) => VmValue::Array { values: values.into() },
            (VmType::Nominal { definition, .. }, None) => VmValue::Record {
                definition: *definition,
                fields: values.into(),
                signature: layout.ty.clone(),
            },
            (VmType::Nominal { definition, .. }, Some(variant)) => VmValue::Enum {
                definition: *definition,
                variant,
                fields: values.into(),
                signature: layout.ty.clone(),
            },
            _ => return Err(error("native storage has an invalid structural layout")),
        })
    }

    pub(super) fn store(
        &self,
        path: &[u32],
        value: &VmValue,
        budget: &mut ExecutionBudget,
    ) -> Result<(), VmArtifactError> {
        let (pointer, layout) = self.project(path)?;
        if !super::vm_type_matches(&super::borrowed_value_type(value, &layout.ty), &layout.ty) {
            return Err(error("native storage value has a different concrete type"));
        }
        if !path.is_empty() && !self.state.borrow()?.root {
            return Err(error(
                "native storage field cannot initialize an absent parent",
            ));
        }
        if path.is_empty() {
            if let VmValue::Resident(source) = value {
                // The directional resident type relation above admits weaker
                // callable receiver views. Their authenticated bytes retain
                // the supplied contract; moving to that view does not change
                // layout or upgrade invocation authority.
                if self.layout.memory != source.layout.memory {
                    return Err(error("native storage move has a different layout"));
                }
                if !std::ptr::eq(self, source.as_ref()) {
                    let (source_pointer, _) = source.project(&[])?;
                    let initialization = source.state.borrow()?.clone();
                    unsafe {
                        std::ptr::copy(source_pointer, pointer, layout.memory.size());
                    }
                    budget.native_memory.residents.copy(source_pointer.addr(), pointer.addr(), layout.memory.size());
                    if let Some(measurements) = &self.measurements {
                        measurements.copied(AllocationKind::Home, layout.memory.size());
                    }
                    *self.state.borrow_mut()? = initialization;
                }
                return Ok(());
            }
            *self.state.borrow_mut()? = Initialization::default();
        } else {
            let mut state = self.state.borrow_mut()?;
            state.holes.retain(|hole| !hole.starts_with(path));
            state.variants.retain(|field, _| !field.starts_with(path));
        }
        budget.native_memory.residents.clear(pointer.addr(), layout.memory.size());
        self.store_at(&layout, pointer, &mut path.to_vec(), value, budget)?;
        self.state.borrow_mut()?.root = true;
        Ok(())
    }

    fn store_at(
        &self,
        layout: &NativeLayout,
        pointer: *mut u8,
        path: &mut Vec<u32>,
        value: &VmValue,
        budget: &mut ExecutionBudget,
    ) -> Result<(), VmArtifactError> {
        if matches!(value, VmValue::Uninitialized(_)) {
            budget.native_memory.residents.clear(pointer.addr(), layout.memory.size());
            self.state.borrow_mut()?.holes.insert(path.clone());
            return Ok(());
        }
        if let VmValue::Resident(source) = value {
            let (source_pointer, source_layout) = source.project(&[])?;
            // Aggregate fields are storage boundaries just like the whole
            // home above. Keep authenticated resident bytes and initialization
            // while admitting only the same directional callable view.
            if source_layout.memory != layout.memory || !super::vm_type_matches(&source_layout.ty, &layout.ty) {
                return Err(error("native field move has a different layout"));
            }
            let origin = source.state.borrow()?.clone();
            unsafe {
                std::ptr::copy(source_pointer, pointer, layout.memory.size());
            }
            budget.native_memory.residents.copy(source_pointer.addr(), pointer.addr(), layout.memory.size());
            if let Some(measurements) = &self.measurements {
                measurements.copied(AllocationKind::Home, layout.memory.size());
            }
            let mut state = self.state.borrow_mut()?;
            let prefixed =
                |relative: &[u32]| path.iter().chain(relative).copied().collect::<Vec<_>>();
            if !origin.root {
                state.holes.insert(path.clone());
            }
            state
                .holes
                .extend(origin.holes.iter().map(|hole| prefixed(hole)));
            state.variants.extend(
                origin
                    .variants
                    .into_iter()
                    .map(|(field, variant)| (prefixed(&field), variant)),
            );
            return Ok(());
        }
        let (offset, fields, values, tag) = match (&layout.shape, value) {
            (
                NativeShape::Product(fields),
                VmValue::Tuple(values) | VmValue::Array { values } | VmValue::Record { fields: values, .. },
            ) => (0, fields, values, None),
            (
                NativeShape::Enum {
                    payload_offset,
                    variants,
                },
                VmValue::Enum {
                    variant, fields, ..
                },
            ) => {
                let layouts = variants
                    .get(*variant as usize)
                    .ok_or_else(|| error("native storage enum tag is out of range"))?;
                (*payload_offset, layouts, fields, Some(*variant))
            }
            _ => {
                if matches!(value, VmValue::Reference { .. }) {
                    unsafe { budget.native_memory.residents.write_reference(pointer, value, false, false)?; }
                } else {
                    unsafe {
                        layout.write(pointer, value.clone(), budget)?;
                    }
                }
                return Ok(());
            }
        };
        if fields.len() != values.len() {
            return Err(error("native storage field count mismatch"));
        }
        for (index, (field, value)) in fields.iter().zip(values.iter()).enumerate() {
            path.push(index as u32);
            self.store_at(
                &field.layout,
                unsafe { pointer.add(offset + field.offset) },
                path,
                value,
                budget,
            )?;
            path.pop();
        }
        if let Some(tag) = tag {
            unsafe {
                pointer.cast::<u32>().write(tag);
            }
            self.state.borrow_mut()?.variants.insert(path.clone(), tag);
        }
        Ok(())
    }

    pub(super) fn take(
        &self,
        path: &[u32],
        budget: &mut ExecutionBudget,
    ) -> Result<VmValue, VmArtifactError> {
        if !self.is_initialized(path) {
            return Err(error("native storage resident was moved out"));
        }
        let value = self.load(path, budget)?;
        self.clear(path);
        Ok(value)
    }

    pub(super) fn matches_pattern(
        &self,
        path: &mut Vec<u32>,
        pattern: &super::VmPattern,
        budget: &mut ExecutionBudget,
    ) -> Result<bool, VmArtifactError> {
        use super::{PatternRead, VmPattern};
        match pattern.read_requirement() {
            PatternRead::None => return Ok(true),
            PatternRead::Root if !self.is_initialized(path) => return Ok(false),
            PatternRead::Value if !self.is_fully_initialized(path) => return Ok(false),
            _ => {}
        }
        let (pointer, layout) = self.project(path)?;
        if matches!(layout.shape, NativeShape::Reference { .. }) {
            // A resident reference is still a handle, not the pattern's
            // structural subject. Resolve its authenticated backing through
            // the same auto-dereference rule as an ordinary VM handle; only
            // the handle is loaded, never a reconstructed aggregate payload.
            return super::matches_runtime_pattern(&self.load(path, budget)?, pattern, &[], &[], budget);
        }
        if matches!(pattern, VmPattern::Literal(_)) {
            return Ok(super::matches_pattern(&self.load(path, budget)?, pattern));
        }
        let fields = match (&layout.shape, pattern) {
            (NativeShape::Product(fields), VmPattern::Array { elements: patterns, rest, .. })
                if crate::pattern::ArrayPatternRest::length(*rest, patterns.len()) == Some(fields.len()) =>
            {
                for (index, pattern) in patterns.iter().enumerate() {
                    budget.tick()?;
                    path.push(crate::pattern::ArrayPatternRest::index(*rest, index) as u32);
                    let matched = self.matches_pattern(path, pattern, budget)?;
                    path.pop();
                    if !matched { return Ok(false); }
                }
                return Ok(true);
            }
            (NativeShape::Product(fields), VmPattern::Tuple(patterns))
                if fields.len() == patterns.len() =>
            {
                for (index, pattern) in patterns.iter().enumerate() {
                    budget.tick()?;
                    path.push(index as u32);
                    let matched = self.matches_pattern(path, pattern, budget)?;
                    path.pop();
                    if !matched {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            (
                NativeShape::Product(fields),
                VmPattern::Record {
                    definition,
                    field_types,
                    field_count,
                    fields: patterns,
                },
            ) if matches!(&layout.ty, VmType::Nominal { definition: actual, .. } if actual == definition)
                && fields.len() == *field_count as usize
                && fields.len() == field_types.len()
                && fields
                    .iter()
                    .zip(field_types)
                    .all(|(field, ty)| super::vm_type_matches(&field.layout.ty, ty)) =>
            {
                patterns
            }
            (
                NativeShape::Enum { variants, .. },
                VmPattern::Enum {
                    definition,
                    variant,
                    field_types,
                    field_count,
                    fields: patterns,
                },
            ) if matches!(&layout.ty, VmType::Nominal { definition: actual, .. } if actual == definition)
                && self.variant(path, pointer, variants.len())? == *variant
                && variants[*variant as usize].len() == *field_count as usize
                && variants[*variant as usize].len() == field_types.len()
                && variants[*variant as usize]
                    .iter()
                    .zip(field_types)
                    .all(|(field, ty)| super::vm_type_matches(&field.layout.ty, ty)) =>
            {
                patterns
            }
            _ => return Ok(false),
        };
        for field in fields {
            budget.tick()?;
            path.push(field.index);
            let (_, actual) = self.project(path)?;
            let matched = super::vm_type_matches(&actual.ty, &field.ty)
                && self.is_fully_initialized(path)
                && self.matches_pattern(path, &field.pattern, budget)?;
            path.pop();
            if !matched {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resident_field_views_preserve_environment_identity_and_holes_without_strengthening() {
        let mut budget = budget(4096);
        let signature = |permission| VmType::Callable { shared_receiver: permission, unique_receiver: permission,
            safety: crate::Safety::Safe, parameters: vec![], result: Box::new(VmType::I64), effects: Box::default() };
        let strong = signature(true);
        let weak = signature(false);
        let layout = |ty| Arc::new(super::super::native_memory::native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap());
        let captures = super::super::RuntimeCaptureEnvironment::new(vec![VmValue::I64(42)]);
        let value = VmValue::Callable { callee: crate::DefKey(crate::Digest::of_bytes(b"resident-field-view")),
            captures: captures.clone(), signature: strong.clone() };
        let source = NativeHome::new(layout(VmType::Tuple(vec![strong.clone(), VmType::I64])), &mut budget).unwrap();
        source.store(&[], &VmValue::Tuple(Arc::from([value, VmValue::I64(7)])), &mut budget).unwrap();
        source.clear(&[1]);
        let destination = NativeHome::new(layout(VmType::Tuple(vec![VmType::Tuple(vec![weak.clone(), VmType::I64])])), &mut budget).unwrap();
        destination.store(&[], &VmValue::Tuple(Arc::from([VmValue::Resident(source)])), &mut budget).unwrap();
        assert!(!destination.is_initialized(&[0, 1]));
        let VmValue::Callable { captures: retained, signature: actual, .. } = destination.load(&[0, 0], &mut budget).unwrap() else { panic!() };
        assert!(Arc::ptr_eq(&captures, &retained));
        assert_eq!(actual, strong);
        let weak_source = NativeHome::new(layout(weak), &mut budget).unwrap();
        let strong_destination = NativeHome::new(layout(VmType::Tuple(vec![strong])), &mut budget).unwrap();
        let error = strong_destination.store(&[], &VmValue::Tuple(Arc::from([VmValue::Resident(weak_source.clone())])), &mut budget).unwrap_err();
        assert!(matches!(error, VmArtifactError::NativeMemory { message: "native storage value has a different concrete type" }), "{error:?}");
        let (pointer, field_layout) = strong_destination.project(&[0]).unwrap();
        let error = strong_destination.store_at(&field_layout, pointer, &mut vec![0], &VmValue::Resident(weak_source), &mut budget).unwrap_err();
        assert!(matches!(error, VmArtifactError::NativeMemory { message: "native field move has a different layout" }), "{error:?}");
        let scalar = NativeHome::new(layout(VmType::I64), &mut budget).unwrap();
        assert!(strong_destination.store(&[], &VmValue::Tuple(Arc::from([VmValue::Resident(scalar)])), &mut budget).is_err());
    }

    fn budget(bytes: u64) -> ExecutionBudget {
        ExecutionBudget {
            native_memory: Default::default(),
            unsafe_execution: false,
            limits: super::super::VmExecutionLimits {
                max_native_bytes: bytes,
                max_native_allocation_bytes: bytes,
                ..Default::default()
            },
            instructions: 0,
            allocated_elements: 0,
        }
    }

    #[test]
    fn private_scalar_spills_reuse_bytes_without_retaining_initialization_or_home_authority() {
        let mut budget = budget(1024);
        let layout = Arc::new(super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let spills = NativeScalarSpills::acquire(layout.memory, 0, &mut budget).unwrap();
        let pointer = spills.slot(0, &layout).unwrap();
        assert!(spills.store(0, &layout, Some(&VmValue::I64(42)), &mut budget).unwrap());
        assert_eq!(super::super::expect_i64(unsafe { spills.load(0, &layout, 1, &mut budget) }.unwrap().unwrap()).unwrap(), 42);
        spills.release(&mut budget);
        let charged = budget.allocated_elements;
        budget.limits.max_allocation_elements = charged;
        for _ in 0..1024 {
            let spills = NativeScalarSpills::acquire(layout.memory, 0, &mut budget).unwrap();
            assert_eq!(spills.slot(0, &layout).unwrap(), pointer);
            assert!(!spills.store(0, &layout, None, &mut budget).unwrap());
            assert!(unsafe { spills.load(0, &layout, 0, &mut budget) }.unwrap().is_none());
            assert!(!spills.store(0, &layout, Some(&VmValue::Uninitialized(VmType::I64)), &mut budget).unwrap());
            assert!(spills.store(0, &layout, Some(&VmValue::Uninitialized(VmType::U64)), &mut budget).is_err());
            assert!(unsafe { spills.load(0, &layout, 2, &mut budget) }.is_err());
            assert!(spills.store(0, &layout, Some(&VmValue::I64(42)), &mut budget).unwrap());
            assert_eq!(super::super::expect_i64(unsafe { spills.load(0, &layout, 1, &mut budget) }.unwrap().unwrap()).unwrap(), 42);
            let flags = [1];
            assert!(NativeHome::capture_loan(layout.clone(), pointer, flags.as_ptr(), &budget).is_err());
            assert!(budget.native_memory.homes.borrow().allocations.is_empty());
            assert!(budget.native_memory.homes.borrow().native_inputs.is_empty());
            spills.release(&mut budget);
            assert_eq!(budget.allocated_elements, charged);
        }
        assert!(matches!(NativeScalarSpills::acquire(MemoryLayout::of::<i128>(), 0, &mut budget),
            Err(VmArtifactError::AllocationLimit { .. })));
        assert!(budget.native_memory.scalar_spills.is_none());
        assert_eq!(budget.native_memory.live_native_bytes(), 0);
    }

    #[test]
    fn private_scalar_spills_validate_layout_bits_and_live_resident_inputs() {
        let mut budget = budget(1024);
        let layout = |ty| Arc::new(super::super::native_memory::native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap());
        let integer = layout(VmType::I64);
        let spills = NativeScalarSpills::acquire(integer.memory, 0, &mut budget).unwrap();
        assert!(spills.slot(1, &integer).is_err());
        assert!(spills.slot(8, &integer).is_err());
        assert!(spills.slot(0, &layout(VmType::I128)).is_err());
        assert!(spills.slot(0, &layout(VmType::Tuple(vec![VmType::I64]))).is_err());
        let boolean = layout(VmType::Bool);
        unsafe { spills.slot(0, &boolean).unwrap().write(2); }
        assert!(unsafe { spills.load(0, &boolean, 1, &mut budget) }.is_err());
        let character = layout(VmType::Char);
        unsafe { spills.slot(0, &character).unwrap().cast::<u32>().write(0xd800); }
        assert!(unsafe { spills.load(0, &character, 1, &mut budget) }.is_err());
        let home = NativeHome::new(integer.clone(), &mut budget).unwrap();
        let resident = VmValue::Resident(home.clone());
        assert!(!spills.store(0, &integer, Some(&resident), &mut budget).unwrap());
        home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        assert!(spills.store(0, &integer, Some(&resident), &mut budget).unwrap());
        home.retire();
        assert!(spills.store(0, &integer, Some(&resident), &mut budget).is_err());
    }

    #[test]
    fn private_scalar_spill_reentry_owns_distinct_backing_and_charges_live_bytes() {
        let mut budget = budget(16);
        budget.native_memory = super::super::native_memory::NativeMemory::profiled();
        let layout = super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap();
        let outer = NativeScalarSpills::acquire(layout.memory, 0, &mut budget).unwrap();
        let inner = NativeScalarSpills::acquire(layout.memory, 0, &mut budget).unwrap();
        assert_ne!(outer.slot(0, &layout).unwrap(), inner.slot(0, &layout).unwrap());
        assert_eq!(budget.native_memory.live_native_bytes(), 16);
        assert!(NativeScalarSpills::acquire(layout.memory, 0, &mut budget).is_err());
        inner.release(&mut budget);
        outer.release(&mut budget);
        assert_eq!(budget.native_memory.live_native_bytes(), 8);
        drop(budget.native_memory.scalar_spills.take());
        assert_eq!(budget.native_memory.live_native_bytes(), 0);
        let profile = budget.native_memory.measurements.as_ref().unwrap().snapshot();
        assert_eq!((profile.home_allocations, profile.home_deallocations, profile.home_peak_bytes), (2, 2, 16));
    }

    #[test]
    fn idle_scalar_spills_yield_the_byte_budget_to_raw_homes_and_control() {
        let layout = MemoryLayout::of::<i64>();
        let mut budget = budget(8);
        for kind in 0..3 {
            NativeScalarSpills::acquire(layout, 0, &mut budget).unwrap().release(&mut budget);
            match kind {
                0 => {
                    let pointer = budget.native_memory.allocate(layout, 8, 8).unwrap();
                    budget.native_memory.deallocate(pointer, layout).unwrap();
                }
                1 => {
                    let resident = Arc::new(super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
                    drop(NativeHome::new(resident, &mut budget).unwrap());
                }
                _ => { drop(budget.native_memory.reserve_control(8, budget.limits).unwrap()); }
            }
            assert!(budget.native_memory.scalar_spills.is_none());
            assert_eq!(budget.native_memory.live_native_bytes(), 0);
        }
        budget.limits.max_native_bytes = 12;
        let small = MemoryLayout::new(4, 1).unwrap();
        let pointer = budget.native_memory.allocate(small, 8, 12).unwrap();
        NativeScalarSpills::acquire(layout, 0, &mut budget).unwrap().release(&mut budget);
        let pointer = unsafe { budget.native_memory.reallocate(pointer, small, 8, 8, 12) }.unwrap();
        assert!(budget.native_memory.scalar_spills.is_none());
        budget.native_memory.deallocate(pointer, MemoryLayout::new(8, 1).unwrap()).unwrap();
        NativeScalarSpills::acquire(layout, 0, &mut budget).unwrap().release(&mut budget);
        let active = NativeScalarSpills::acquire(MemoryLayout::of::<i32>(), 0, &mut budget).unwrap();
        assert_eq!(budget.native_memory.live_native_bytes(), 4, "an active smaller frame does not retain excess cached bytes");
        let pointer = budget.native_memory.allocate(layout, 8, 12).unwrap();
        budget.native_memory.deallocate(pointer, layout).unwrap();
        drop(active);
        assert_eq!(budget.native_memory.live_native_bytes(), 0);
        NativeScalarSpills::acquire(layout, 0, &mut budget).unwrap().release(&mut budget);
        budget.native_memory.reclaim_idle_spills(0, 0);
        assert!(budget.native_memory.scalar_spills.is_none(), "a reduced allowance reclaims idle bytes even without new payload");
        assert_eq!(budget.native_memory.live_native_bytes(), 0);
    }

    #[test]
    fn borrowed_generated_captures_share_payload_masks_and_nested_loans() {
        let mut budget = budget(1024);
        let ty = VmType::Tuple(vec![VmType::I64, VmType::I64]);
        let layout = Arc::new(super::super::native_memory::native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap());
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        home.store(&[], &VmValue::Tuple(Arc::from([VmValue::I64(20), VmValue::I64(22)])), &mut budget).unwrap();
        let mut flags = [1,1,1];
        let paths: Arc<[Vec<u32>]> = Arc::from([vec![],vec![0],vec![1]]);
        let outer = unsafe { home.lend_native(flags.as_mut_ptr(), paths.clone(), &mut budget) }.unwrap();
        home.store(&[0], &VmValue::I64(21), &mut budget).unwrap();
        assert_eq!(unsafe { *home.pointer().cast::<[i64;2]>() }, [21,22]);
        flags[2] = 0;
        assert!(!home.is_initialized(&[1]));
        let mut inner_flags = [1,1,0];
        let loan = unsafe { home.lend_native(inner_flags.as_mut_ptr(), paths, &mut budget) }.unwrap();
        let nested = NativeHome::capture_loan(layout, home.pointer(), inner_flags.as_ptr(), &budget).unwrap();
        assert!(Arc::ptr_eq(&home, &nested));
        nested.store(&[1], &VmValue::I64(23), &mut budget).unwrap();
        assert_eq!(inner_flags, [1,1,1]);
        loan.finish().unwrap();
        assert_eq!(flags, [1,1,1]);
        assert_eq!(unsafe { *home.pointer().cast::<[i64;2]>() }, [21,23]);
        drop(nested);
        outer.finish().unwrap();
        assert!(home.is_fully_initialized(&[]), "returning a segment loan leaves the source owner live");
        drop(home);
        assert_eq!(flags, [1,1,1], "retiring the source cannot touch a returned segment's mask");
    }

    #[test]
    fn borrowed_generated_capture_expiration_precedes_every_payload_access() {
        let mut budget = budget(1024);
        let layout = Arc::new(super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        let mut flags = [1];
        let loan = unsafe { home.lend_native(flags.as_mut_ptr(), Arc::from([vec![]]), &mut budget) }.unwrap();
        loan.finish().unwrap();
        home.retire();
        assert!(home.project(&[]).is_err());
        assert!(home.load(&[], &mut budget).is_err());
        assert!(home.store(&[], &VmValue::I64(0), &mut budget).is_err());
        let destination = NativeHome::new(layout, &mut budget).unwrap();
        assert!(destination.store(&[], &VmValue::Resident(home.clone()), &mut budget).is_err(),
            "an expired resident cannot be copied before its lifetime check");
        drop(home);
        assert_eq!(flags, [1], "retiring the view cannot touch an expired frame mask");
    }

    #[test]
    fn generated_capture_loans_reuse_the_authoritative_owner_and_reject_unknown_slots() {
        let mut budget = budget(1024);
        let ty = VmType::Tuple(vec![VmType::I64, VmType::I64]);
        let layout = Arc::new(super::super::native_memory::native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap());
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        home.store(&[], &VmValue::Tuple(Arc::from([VmValue::I64(17), VmValue::I64(42)])), &mut budget).unwrap();
        let mut flags = [1, 1, 1];
        let paths = Arc::from([vec![], vec![0], vec![1]]);
        assert!(NativeHome::capture_loan(layout.clone(), home.pointer(), flags.as_ptr(), &budget).is_err(),
            "matching bytes do not establish a lent capture input");
        let native_loan = unsafe { home.lend_native(flags.as_mut_ptr(), paths, &mut budget) }.unwrap();
        let loan = NativeHome::capture_loan(layout.clone(), home.pointer(), flags.as_ptr(), &budget).unwrap();
        assert!(Arc::ptr_eq(&home, &loan));
        flags[1] = 0;
        assert!(!home.is_initialized(&[0]));
        loan.store(&[1], &VmValue::I64(43), &mut budget).unwrap();
        loan.clear(&[1]);
        assert_eq!(flags, [1, 0, 0], "VM operations publish to the active native mask");
        loan.store(&[1], &VmValue::I64(43), &mut budget).unwrap();
        assert_eq!(flags, [1, 0, 1]);
        drop(loan);
        let mut unrelated = [17i64, 42];
        assert!(NativeHome::capture_loan(layout.clone(), unrelated.as_mut_ptr().cast(), flags.as_ptr(), &budget).is_err());
        let wrong = Arc::new(super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        assert!(NativeHome::capture_loan(wrong, home.pointer(), flags.as_ptr(), &budget).is_err());
        native_loan.finish().unwrap();
        flags = [0, 0, 0];
        assert_eq!(flags, [0, 0, 0]);
        assert!(!home.is_initialized(&[0]));
        assert_eq!(super::super::expect_i64(home.load(&[1], &mut budget).unwrap()).unwrap(), 43);
        assert!(NativeHome::capture_loan(layout, home.pointer(), flags.as_ptr(), &budget).is_err(),
            "a returned input no longer authenticates storage");
    }

    #[test]
    fn native_initialization_loans_reuse_backing_without_retaining_returned_masks() {
        let mut budget = budget(1024);
        let layout = Arc::new(super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let home = NativeHome::new(layout, &mut budget).unwrap();
        home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        let paths: Arc<[Vec<u32>]> = Arc::from([vec![]]);
        let mut backing = std::ptr::null();
        let mut charged = 0;
        for iteration in 0..1024 {
            let mut outer_flags = [1];
            let mut middle_flags = [1];
            let mut inner_flags = [0];
            let outer = unsafe { home.lend_native(outer_flags.as_mut_ptr(), paths.clone(), &mut budget) }.unwrap();
            let middle = unsafe { home.lend_native(middle_flags.as_mut_ptr(), paths.clone(), &mut budget) }.unwrap();
            let inner = unsafe { home.lend_native(inner_flags.as_mut_ptr(), paths.clone(), &mut budget) }.unwrap();
            assert!(!home.is_initialized(&[]));
            inner_flags[0] = 1;
            inner.finish().unwrap();
            assert_eq!(middle_flags, [1]);
            middle.finish().unwrap();
            outer.finish().unwrap();
            outer_flags[0] = 2;
            middle_flags[0] = 2;
            inner_flags[0] = 2;
            assert_eq!((outer_flags, middle_flags, inner_flags), ([2], [2], [2]));
            assert_eq!(super::super::expect_i64(home.scalar_value().unwrap()).unwrap(), 42);
            let state = home.state.0.borrow();
            assert!(state.active.is_none() && state.suspended.is_empty());
            assert!(budget.native_memory.homes.borrow().native_inputs.is_empty());
            assert_eq!(Arc::strong_count(&paths), 1, "returned loans retain no path or mask authority");
            if iteration == 0 {
                backing = state.suspended.as_ptr();
                charged = budget.allocated_elements;
                budget.limits.max_allocation_elements = charged;
            } else {
                assert_eq!(state.suspended.as_ptr(), backing);
                assert_eq!(budget.allocated_elements, charged, "only real backing growth is charged");
            }
        }
    }

    #[test]
    fn native_initialization_loan_growth_failure_preserves_the_active_owner() {
        let mut budget = budget(1024);
        let layout = Arc::new(super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        let paths: Arc<[Vec<u32>]> = Arc::from([vec![]]);
        let mut outer_flags = [1];
        budget.limits.max_allocation_elements = budget.allocated_elements;
        assert!(matches!(unsafe { home.lend_native(outer_flags.as_mut_ptr(), paths.clone(), &mut budget) },
            Err(VmArtifactError::AllocationLimit { .. })));
        assert!(home.state.0.borrow().active.is_none());
        assert!(budget.native_memory.homes.borrow().native_inputs.is_empty());
        budget.limits.max_allocation_elements = u64::MAX;
        let outer = unsafe { home.lend_native(outer_flags.as_mut_ptr(), paths.clone(), &mut budget) }.unwrap();
        budget.limits.max_allocation_elements = budget.allocated_elements;
        let mut inner_flags = [0];
        assert!(matches!(unsafe { home.lend_native(inner_flags.as_mut_ptr(), paths.clone(), &mut budget) },
            Err(VmArtifactError::AllocationLimit { .. })));
        assert_eq!(home.state.0.borrow().active.as_ref().unwrap().identity(), outer_flags.as_ptr().addr());
        assert_eq!(budget.native_memory.homes.borrow().native_inputs.len(), 1);
        assert!(NativeHome::capture_loan(layout.clone(), home.pointer(), inner_flags.as_ptr(), &budget).is_err());
        assert!(Arc::ptr_eq(&NativeHome::capture_loan(layout, home.pointer(), outer_flags.as_ptr(), &budget).unwrap(), &home));
        assert!(unsafe { home.lend_native(outer_flags.as_mut_ptr(), paths, &mut budget) }.is_err(),
            "an active sidecar cannot be lent twice");
        outer.finish().unwrap();
        assert_eq!(super::super::expect_i64(home.scalar_value().unwrap()).unwrap(), 42);
    }

    #[test]
    fn native_initialization_loans_compose_across_nested_engine_entries() {
        let mut budget = budget(1024);
        let ty = VmType::Tuple(vec![VmType::I64, VmType::I64]);
        let layout = Arc::new(super::super::native_memory::native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap());
        let home = NativeHome::new(layout, &mut budget).unwrap();
        home.store(&[], &VmValue::Tuple(Arc::from([VmValue::I64(20), VmValue::I64(22)])), &mut budget).unwrap();
        let paths: Arc<[Vec<u32>]> = Arc::from([vec![], vec![0], vec![1]]);
        let mut outer_flags = [1, 1, 1];
        let outer = unsafe { home.lend_native(outer_flags.as_mut_ptr(), paths.clone(), &mut budget) }.unwrap();
        home.clear(&[0]);
        assert_eq!(outer_flags, [1, 0, 1]);
        let mut inner_flags = [1, 0, 1];
        let inner = unsafe { home.lend_native(inner_flags.as_mut_ptr(), paths, &mut budget) }.unwrap();
        home.store(&[0], &VmValue::I64(20), &mut budget).unwrap();
        inner_flags[2] = 0;
        assert_eq!(inner_flags, [1, 1, 0]);
        assert!(!home.is_initialized(&[1]));
        assert_eq!(outer_flags, [1, 0, 1], "inactive flags are not a competing authority");
        inner.finish().unwrap();
        assert_eq!(outer_flags, [1, 1, 0]);
        inner_flags = [0, 0, 0];
        assert_eq!(inner_flags, [0, 0, 0]);
        home.store(&[1], &VmValue::I64(22), &mut budget).unwrap();
        assert_eq!(outer_flags, [1, 1, 1]);
        outer.finish().unwrap();
        assert!(home.is_fully_initialized(&[]));
        assert_eq!(super::super::expect_i64(home.load(&[1], &mut budget).unwrap()).unwrap(), 22);
    }

    #[test]
    fn native_capture_inputs_preserve_distinct_zero_byte_owners_and_retirement() {
        let mut budget = budget(1024);
        let layout = Arc::new(super::super::native_memory::native_layout(&VmType::Unit, &Arc::from([]), &mut vec![]).unwrap());
        let first = NativeHome::new(layout.clone(), &mut budget).unwrap();
        let second = NativeHome::new(layout.clone(), &mut budget).unwrap();
        for home in [&first, &second] { home.store(&[], &VmValue::Unit, &mut budget).unwrap(); }
        assert_eq!(first.pointer(), second.pointer());
        let mut first_flags = [1];
        let mut second_flags = [1];
        let first_loan = unsafe { first.lend_native(first_flags.as_mut_ptr(), Arc::from([vec![]]), &mut budget) }.unwrap();
        let second_loan = unsafe { second.lend_native(second_flags.as_mut_ptr(), Arc::from([vec![]]), &mut budget) }.unwrap();
        let selected = NativeHome::capture_loan(layout.clone(), second.pointer(), second_flags.as_ptr(), &budget).unwrap();
        assert!(Arc::ptr_eq(&selected, &second));
        first_flags[0] = 0;
        assert_eq!(first_flags, [0]);
        assert!(!first.is_initialized(&[]));
        assert!(selected.is_initialized(&[]));
        second_loan.finish().unwrap();
        first_loan.finish().unwrap();
        assert!(selected.is_initialized(&[]), "the reference follows the home beyond the invocation");
        second.retire();
        assert!(!selected.is_initialized(&[]));
        assert!(selected.load(&[], &mut budget).is_err());
        assert!(NativeHome::capture_loan(layout, second.pointer(), second_flags.as_ptr(), &budget).is_err());
    }

    #[test]
    fn invalid_native_initialization_never_survives_its_loan_as_read_authority() {
        let mut budget = budget(1024);
        let layout = Arc::new(super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        let mut flags = [2];
        assert!(unsafe { home.lend_native(flags.as_mut_ptr(), Arc::from([vec![]]), &mut budget) }.is_err());
        flags[0] = 1;
        let loan = unsafe { home.lend_native(flags.as_mut_ptr(), Arc::from([vec![]]), &mut budget) }.unwrap();
        flags[0] = 2;
        assert_eq!(flags, [2]);
        assert!(home.scalar_value().is_err());
        assert!(NativeHome::capture_loan(layout.clone(), home.pointer(), flags.as_ptr(), &budget).is_err());
        assert!(loan.finish().is_err());
        flags[0] = 1;
        assert!(!home.is_initialized(&[]));
        assert!(NativeHome::capture_loan(layout, home.pointer(), flags.as_ptr(), &budget).is_err());
    }

    #[test]
    fn out_of_order_native_loan_return_detaches_the_expiring_sidecar() {
        let mut budget = budget(1024);
        let layout = Arc::new(super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let home = NativeHome::new(layout, &mut budget).unwrap();
        home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        let mut outer_flags = [1];
        let mut inner_flags = [1];
        let outer = unsafe { home.lend_native(outer_flags.as_mut_ptr(), Arc::from([vec![]]), &mut budget) }.unwrap();
        let inner = unsafe { home.lend_native(inner_flags.as_mut_ptr(), Arc::from([vec![]]), &mut budget) }.unwrap();
        assert!(outer.finish().is_err());
        outer_flags[0] = 2;
        assert_eq!(outer_flags, [2]);
        assert_eq!(super::super::expect_i64(home.scalar_value().unwrap()).unwrap(), 42);
        inner.finish().unwrap();
        assert_eq!(super::super::expect_i64(home.scalar_value().unwrap()).unwrap(), 42);
        assert!(budget.native_memory.homes.borrow().native_inputs.is_empty());
    }

    #[test]
    fn resident_patterns_share_materialized_inspection_requirements() {
        use super::super::{VmPattern as P, VmPatternField};
        let nominal = crate::DefKey(crate::Digest::of_bytes(b"pattern-partial-record"));
        let tuple = VmType::Tuple(vec![VmType::I64, VmType::I64]);
        let descriptor = super::super::VmNominalCopyDescriptor {
            definition: nominal, source_contract: crate::Digest::of_bytes(b"pattern-record-contract"),
            is_enum: false, arguments: vec![], variants: vec![vec![tuple.clone()]],
        };
        let cases = [
            (tuple.clone(), VmValue::Tuple(Arc::from([VmValue::I64(17), VmValue::I64(42)])), vec![0],
                vec![(P::Tuple(vec![P::Any, P::Any]), true),
                    (P::Tuple(vec![P::Literal("17".into()), P::Any]), false)]),
            (VmType::FixedArray { element: Box::new(VmType::I64), length: 2 },
                VmValue::Array { values: Arc::from([VmValue::I64(17), VmValue::I64(42)]) }, vec![0],
                vec![(P::Array { element: VmType::I64, elements: vec![P::Literal("42".into())],
                    rest: Some(crate::pattern::ArrayPatternRest { prefix: 0, omitted: 1 }) }, false)]),
            (VmType::Nominal { definition: nominal, arguments: vec![] },
                VmValue::Record { definition: nominal, signature: VmType::Nominal { definition: nominal, arguments: vec![] }, fields: Arc::from([
                    VmValue::Tuple(Arc::from([VmValue::I64(17), VmValue::I64(42)]))]) }, vec![0,0],
                vec![(P::Record { definition: nominal, field_count: 1, field_types: vec![tuple.clone()], fields: vec![] }, true),
                    (P::Record { definition: nominal, field_count: 1, field_types: vec![tuple.clone()],
                        fields: vec![VmPatternField { index: 0, ty: tuple, pattern: P::Any }] }, false)]),
        ];
        for (ty, value, hole, patterns) in cases {
            let mut budget = budget(1024);
            let layout = Arc::new(super::super::native_memory::native_layout(
                &ty, &Arc::from([descriptor.clone()]), &mut vec![]).unwrap());
            let home = NativeHome::new(layout, &mut budget).unwrap();
            home.store(&[], &value, &mut budget).unwrap();
            home.take(&hole, &mut budget).unwrap();
            let materialized = home.load(&[], &mut budget).unwrap();
            assert!(!super::super::value_matches_vm_type(&VmValue::Resident(home.clone()), &ty));
            assert!(super::super::value_matches_vm_layout(&VmValue::Resident(home.clone()), &ty,
                super::super::Initialization::Storage));
            for (pattern, expected) in patterns {
                assert_eq!(super::super::matches_pattern(&materialized, &pattern), expected, "materialized {pattern:?}");
                assert_eq!(home.matches_pattern(&mut vec![], &pattern, &mut budget).unwrap(), expected, "resident {pattern:?}");
            }
            assert!(home.matches_pattern(&mut hole.clone(), &P::Any, &mut budget).unwrap());
        }
    }

    #[test]
    fn partial_external_owner_never_reads_a_moved_reference_leaf() {
        let ty = VmType::Tuple(vec![VmType::Reference { unique: true, referent: Box::new(VmType::I64) }, VmType::I64]);
        let layout = Arc::new(super::super::native_memory::native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap());
        let mut budget = budget(1024);
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        home.store(&[], &VmValue::Tuple(Arc::from([
            VmValue::Uninitialized(VmType::Reference { unique: true, referent: Box::new(VmType::I64) }),
            VmValue::I64(42),
        ])), &mut budget).unwrap();
        let pointer = home.pointer();
        unsafe { pointer.cast::<*mut i64>().write(std::ptr::null_mut()); }
        let mut flags = [1,0,1];
        let loan = unsafe { home.lend_native(flags.as_mut_ptr(), Arc::from([vec![],vec![0],vec![1]]), &mut budget) }.unwrap();
        assert_eq!(home.pointer(), pointer);
        assert!(home.is_initialized(&[]));
        assert!(!home.is_initialized(&[0]));
        assert!(!home.is_fully_initialized(&[]));
        assert!(matches!(home.load(&[0], &mut budget).unwrap(), VmValue::Uninitialized(_)));
        assert!(matches!(home.load(&[1], &mut budget).unwrap(), VmValue::I64(42)));
        loan.finish().unwrap();
        // The ordinary complete-value ABI still refuses these bytes: the
        // null moved field is not a resident reference without its sidecar.
        assert!(unsafe { NativeHome::external_argument(layout, pointer, &mut budget) }.is_err());
    }

    #[test]
    fn native_owner_move_transfers_only_unique_unexposed_vacant_homes() {
        use super::super::RuntimeRegisters;
        for mode in ["vacant", "exposed", "shared", "destination"] {
            let mut budget = budget(if mode == "vacant" { 16 } else { 32 });
            budget.native_memory = super::super::native_memory::NativeMemory::profiled();
            let measurements = budget.native_memory.measurements.clone().unwrap();
            let tuple = VmType::Tuple(vec![VmType::I64, VmType::I64]);
            let reference = VmType::Reference { unique: false, referent: Box::new(tuple.clone()) };
            let function = VmFunction {
                definition: crate::DefKey(crate::Digest::of_bytes(b"native-owner-move")),
                safety: crate::Safety::Safe, unsafe_execution: false,
                nominal_copy_descriptors: vec![], captures: 0, parameters: 0,
                registers: vec![tuple.clone(), tuple, reference.clone(), reference],
                // Demand native storage for both slots. We exercise the move
                // directly; an actual borrow is introduced only in its case.
                instructions: vec![
                    VmInstruction::Borrow { dst: 2, src: 0, fields: vec![], unique: false, reborrow: false },
                    VmInstruction::Borrow { dst: 3, src: 1, fields: vec![], unique: false, reborrow: false },
                ],
            };
            let mut registers = RuntimeRegisters::for_function(&function, &mut budget).unwrap();
            let value = VmValue::Tuple(vec![VmValue::I64(19), VmValue::I64(23)].into());
            registers.values[0] = Some(registers.materialize_native(0, &value, &mut budget).unwrap());
            let source_pointer = registers.native_homes[&0].pointer();
            if mode == "exposed" { registers.native_homes[&0].expose_address(); }
            let shared = (mode == "shared").then(|| registers.native_homes[&0].clone());
            let destination = (mode == "destination").then(|| {
                registers.native_home(1, &mut budget).unwrap().pointer()
            });
            registers.move_into(1, 0, &mut budget).unwrap();
            registers.native_write(1);
            registers.finish_native_writes(&mut budget).unwrap();
            assert!(registers.values[0].is_none());
            let moved = registers.native_homes[&1].load(&[], &mut budget).unwrap();
            assert_eq!(super::super::expect_tuple_i64(moved).unwrap(), [19, 23]);
            let profile = measurements.snapshot();
            if mode == "vacant" {
                assert_eq!(registers.native_homes[&1].pointer(), source_pointer);
                assert_eq!((profile.home_allocations, profile.home_deallocations, profile.home_peak_bytes), (1, 0, 16));
                assert_eq!(profile.home_bulk_copy_bytes, 0);
            } else {
                assert_ne!(registers.native_homes[&1].pointer(), source_pointer);
                assert_eq!(profile.home_allocations, 2);
                assert_eq!(profile.home_bulk_copy_bytes, 16);
                if let Some(destination) = destination {
                    assert_eq!(registers.native_homes[&1].pointer(), destination);
                }
                if mode == "exposed" {
                    assert_eq!(registers.native_homes[&0].pointer(), source_pointer);
                    assert_eq!(profile.home_deallocations, 0);
                }
            }
            drop(registers);
            drop(shared);
            let final_profile = measurements.snapshot();
            assert_eq!(final_profile.home_live_bytes, 0);
            assert_eq!(final_profile.home_allocations, final_profile.home_deallocations);
        }
    }

    #[test]
    fn native_profile_counts_rejected_temporary_homes_and_one_shot_retirement() {
        let mut budget = budget(16);
        budget.native_memory = super::super::native_memory::NativeMemory::profiled();
        budget.limits.max_allocation_elements = 0;
        let measurements = budget.native_memory.measurements.clone().unwrap();
        let layout = Arc::new(super::super::native_memory::native_layout(
            &VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        assert!(NativeHome::new(layout.clone(), &mut budget).is_err());
        let temporary = measurements.snapshot();
        assert_eq!((temporary.home_allocations, temporary.home_deallocations), (1, 1));
        assert_eq!((temporary.home_live_bytes, temporary.home_peak_bytes), (0, 8));
        assert_eq!(budget.native_memory.live_native_bytes(), 0);
        let too_large = Arc::new(super::super::native_memory::native_layout(
            &VmType::Tuple(vec![VmType::I64; 3]), &Arc::from([]), &mut vec![]).unwrap());
        assert!(NativeHome::new(too_large, &mut budget).is_err());
        assert_eq!(measurements.snapshot(), temporary, "byte admission rejected before allocation");

        budget.limits.max_allocation_elements = 100;
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        let stale = home.clone();
        home.retire();
        let retired = measurements.snapshot();
        assert_eq!((retired.home_allocations, retired.home_deallocations), (2, 2));
        let mut exported = 0i64;
        assert!(unsafe { stale.write_bytes_with_sidecar((&raw mut exported).cast()) }.is_err());
        assert!(unsafe { stale.write_bytes((&raw mut exported).cast()) }.is_err());
        home.retire();
        drop(home);
        drop(stale);
        assert_eq!(measurements.snapshot(), retired);
        assert_eq!(budget.native_memory.live_native_bytes(), 0);

        let unit = Arc::new(super::super::native_memory::native_layout(
            &VmType::Unit, &Arc::from([]), &mut vec![]).unwrap());
        drop(NativeHome::new(unit, &mut budget).unwrap());
        let mut native = 42i64;
        // SAFETY: this initialized local outlives the synchronous external view.
        let external = unsafe { NativeHome::external_argument(layout, (&raw mut native).cast(), &mut budget) }.unwrap();
        external.retire();
        drop(external);
        assert_eq!(native, 42);
        assert_eq!(measurements.snapshot(), retired, "zero-size and external storage acquire no backing bytes");
    }

    #[test]
    fn native_profile_counts_bulk_home_transfers_and_exports_not_scalar_stores() {
        let mut budget = budget(64);
        budget.native_memory = super::super::native_memory::NativeMemory::profiled();
        let measurements = budget.native_memory.measurements.clone().unwrap();
        let layout = Arc::new(super::super::native_memory::native_layout(
            &VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let source = NativeHome::new(layout.clone(), &mut budget).unwrap();
        source.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        assert_eq!(measurements.snapshot().home_bulk_copy_bytes, 0);
        let destination = NativeHome::new(layout, &mut budget).unwrap();
        destination.store(&[], &VmValue::Resident(source.clone()), &mut budget).unwrap();
        assert_eq!(measurements.snapshot().home_bulk_copy_bytes, 8);
        destination.store(&[], &VmValue::Resident(destination.clone()), &mut budget).unwrap();
        assert_eq!(measurements.snapshot().home_bulk_copy_bytes, 8, "self store has no bulk copy");
        let tuple = Arc::new(super::super::native_memory::native_layout(
            &VmType::Tuple(vec![VmType::I64; 2]), &Arc::from([]), &mut vec![]).unwrap());
        let tuple = NativeHome::new(tuple, &mut budget).unwrap();
        tuple.store(&[], &VmValue::Tuple(vec![VmValue::Resident(source), VmValue::I64(19)].into()), &mut budget).unwrap();
        assert_eq!(measurements.snapshot().home_bulk_copy_bytes, 16);
        let mut output = std::mem::MaybeUninit::<[i64; 2]>::uninit();
        // SAFETY: two aligned i64 slots exactly match the complete tuple layout.
        unsafe { tuple.write_bytes(output.as_mut_ptr().cast()).unwrap(); }
        assert_eq!(unsafe { output.assume_init() }, [42, 19]);
        assert_eq!(measurements.snapshot().home_bulk_copy_bytes, 32);
        tuple.clear(&[0]);
        assert!(unsafe { tuple.write_bytes(output.as_mut_ptr().cast()) }.is_err());
        assert_eq!(measurements.snapshot().home_bulk_copy_bytes, 32, "rejected exports copy nothing");
    }

    #[test]
    fn retired_home_cannot_revive_storage_and_releases_its_byte_budget() {
        let mut budget = budget(8);
        let layout = Arc::new(
            super::super::native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![])
                .unwrap(),
        );
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        let stale_carrier = home.clone();
        home.retire();
        assert_eq!(budget.native_memory.live_native_bytes(), 0);
        assert!(!stale_carrier.is_initialized(&[]));
        assert!(stale_carrier.load(&[], &mut budget).is_err());
        assert!(
            stale_carrier
                .store(&[], &VmValue::I64(1), &mut budget)
                .is_err()
        );
        let replacement = NativeHome::new(layout, &mut budget).unwrap();
        replacement
            .store(&[], &VmValue::I64(19), &mut budget)
            .unwrap();
        drop(stale_carrier);
        drop(home);
        assert_eq!(budget.native_memory.live_native_bytes(), 8);
        assert_eq!(
            super::super::expect_i64(replacement.load(&[], &mut budget).unwrap()).unwrap(),
            19
        );
    }

    #[test]
    fn partial_initialization_never_exports_a_complete_native_value() {
        let mut budget = budget(16);
        let layout = Arc::new(
            super::super::native_memory::native_layout(
                &VmType::Tuple(vec![VmType::I64, VmType::I64]),
                &Arc::from([]),
                &mut vec![],
            )
            .unwrap(),
        );
        let home = NativeHome::new(layout, &mut budget).unwrap();
        home.store(
            &[],
            &VmValue::Tuple(Arc::from([VmValue::I64(19), VmValue::I64(23)])),
            &mut budget,
        )
        .unwrap();
        home.take(&[0], &mut budget).unwrap();
        assert!(home.is_initialized(&[]));
        assert!(!home.is_fully_initialized(&[]));
        assert!(home.is_fully_initialized(&[1]));
        let mut destination = [0i64; 2];
        // SAFETY: valid writable extent, but logical initialization must reject
        // the operation before touching that destination.
        assert!(unsafe { home.write_bytes(destination.as_mut_ptr().cast()) }.is_err());
        assert_eq!(destination, [0, 0]);
        home.store(&[0], &VmValue::I64(20), &mut budget).unwrap();
        assert!(home.is_fully_initialized(&[]));
        unsafe { home.write_bytes(destination.as_mut_ptr().cast()) }.unwrap();
        assert_eq!(destination, [20, 23]);
    }

    #[test]
    fn direct_native_field_read_requires_a_single_consumer() {
        let tuple = VmType::Tuple(vec![VmType::I64, VmType::I64]);
        let mut function = VmFunction {
            definition: crate::DefKey(crate::Digest::of_bytes(b"native-field-read-plan")),
            safety: crate::Safety::Safe,
            unsafe_execution: false,
            nominal_copy_descriptors: vec![],
            captures: 0,
            parameters: 1,
            registers: vec![
                VmType::Reference {
                    unique: false,
                    referent: Box::new(tuple.clone()),
                },
                tuple,
                VmType::I64,
            ],
            instructions: vec![
                VmInstruction::DerefCopy {
                    dst: 1,
                    reference: 0,
                },
                VmInstruction::ProjectTuple {
                    dst: 2,
                    base: 1,
                    index: 0,
                    field_count: 2,
                    field_type: VmType::I64,
                },
                VmInstruction::Return { value: 2 },
            ],
        };
        let descriptors = Arc::from([]);
        assert_eq!(
            NativeFramePlan::new(&function, &descriptors, false).read_projections[0],
            Some((2, 0))
        );
        // Delimited completion is an additional consumer even though it does
        // not look like an ordinary arithmetic or projection instruction.
        function
            .instructions
            .insert(2, VmInstruction::CompleteHandler { value: 1 });
        assert_eq!(
            NativeFramePlan::new(&function, &descriptors, false).read_projections[0],
            None
        );
    }
}
