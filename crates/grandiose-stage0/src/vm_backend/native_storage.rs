//! Native homes for addressable VM locals. A home is established by ordinary
//! value initialization, not by a native call. Resident bytes are authoritative;
//! the separate state records only initialization and checked-reference origins.

use super::native_memory::{NativeFields, NativeLayout, NativeReference, NativeShape};
use super::native_profile::{AllocationKind, NativeAllocation, NativeMemoryMeasurements};
use super::{
    ExecutionBudget, ReferenceTarget, VmArtifactError, VmFunction, VmInstruction,
    VmNominalCopyDescriptor, VmType, VmValue,
};
use grandiose_runtime::memory::RawAllocation;
use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
    sync::{Arc, Weak},
};

fn error(message: &'static str) -> VmArtifactError {
    VmArtifactError::NativeMemory { message }
}

pub(super) type HomeRegistry = Rc<RefCell<BTreeMap<usize, Weak<NativeHome>>>>;

// One result slot per ordinary producing instruction. Handler payload tables
// are installed explicitly by the control engine.
fn instruction_result(instruction: &VmInstruction) -> Option<u32> {
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
fn visit_locals(instruction: &VmInstruction, mut visit: impl FnMut(u32)) {
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
        VmInstruction::Copy { dst, src, .. }
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
    pub(super) fn new(function: &VmFunction, descriptors: &Arc<[VmNominalCopyDescriptor]>) -> Self {
        Self::with_native_return(function, descriptors, false)
    }

    pub(super) fn with_native_return(
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
            if let VmInstruction::HostCall { dst, arguments, .. } | VmInstruction::HostCallOwned { dst, arguments, .. } = instruction {
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
            if !matches!(ty, VmType::Tuple(_) | VmType::FixedArray { .. } | VmType::Nominal { .. }) {
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

#[derive(Clone, Debug)]
enum StoredTarget {
    Home(Weak<NativeHome>),
    Native(NativeReference),
}

#[derive(Clone, Debug)]
struct StoredReference {
    pointer: *mut u8,
    target: StoredTarget,
    fields: Arc<[u32]>,
    unique: bool,
    referent: VmType,
}

#[derive(Clone, Debug, Default)]
struct Initialization {
    root: bool,
    holes: BTreeSet<Vec<u32>>,
    references: BTreeMap<Vec<u32>, StoredReference>,
    variants: BTreeMap<Vec<u32>, u32>,
}

/// Retaining this allocation is not retaining a language owner or running its
/// Drop hook. Source cleanup explicitly clears initialization before releasing
/// the home; outstanding runtime references cannot read a cleared resident.
#[derive(Debug)]
pub(super) struct NativeHome {
    allocation: RefCell<Option<NativeAllocation>>,
    pointer: *mut u8,
    live: Cell<bool>,
    external: bool,
    pub(super) layout: Arc<NativeLayout>,
    state: RefCell<Initialization>,
    address_exposed: Cell<bool>,
    live_bytes: Rc<Cell<usize>>,
    measurements: Option<Rc<NativeMemoryMeasurements>>,
    registry: HomeRegistry,
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
            external: false,
            layout,
            state: RefCell::new(Initialization::default()),
            address_exposed: Cell::new(false),
            live_bytes,
            measurements: budget.native_memory.measurements.clone(),
            registry: budget.native_memory.homes.clone(),
        });
        if bytes != 0 {
            home.registry
                .borrow_mut()
                .insert(home.pointer().addr(), Arc::downgrade(&home));
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
        unsafe { Self::external_argument_with_holes(layout, pointer, budget, None) }
    }

    /// Bind compiler-sealed partial initialization without ever reading a
    /// moved-out leaf. The ordinary external ABI always passes `None`.
    pub(super) unsafe fn external_argument_with_holes(
        layout: Arc<NativeLayout>,
        pointer: *mut u8,
        budget: &mut ExecutionBudget,
        holes: Option<&BTreeSet<Vec<u32>>>,
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
            external: true,
            layout,
            state: RefCell::new(Initialization::default()),
            address_exposed: Cell::new(true),
            live_bytes: budget.native_memory.home_bytes.clone(),
            measurements: budget.native_memory.measurements.clone(),
            registry: budget.native_memory.homes.clone(),
        });
        unsafe {
            home.initialize_native_with_holes(budget, holes)?;
        }
        Ok(home)
    }

    pub(super) fn is_external(&self) -> bool {
        self.external
    }

    /// Adopt a value constructed directly in this uninitialized native slot.
    /// The unsafe producer supplies valid resident/loan/ownership obligations;
    /// this walk validates bits and records origins without rebuilding a value.
    pub(super) unsafe fn initialize_native(
        &self,
        budget: &mut ExecutionBudget,
    ) -> Result<(), VmArtifactError> {
        unsafe { self.initialize_native_with_holes(budget, None) }
    }

    unsafe fn initialize_native_with_holes(
        &self,
        budget: &mut ExecutionBudget,
        holes: Option<&BTreeSet<Vec<u32>>>,
    ) -> Result<(), VmArtifactError> {
        fn visit(
            home: &NativeHome,
            layout: &NativeLayout,
            pointer: *const u8,
            path: &mut Vec<u32>,
            budget: &mut ExecutionBudget,
            holes: Option<&BTreeSet<Vec<u32>>>,
        ) -> Result<(), VmArtifactError> {
            budget.tick()?;
            if holes.is_some_and(|holes| holes.contains(path)) {
                home.state.borrow_mut().holes.insert(path.clone());
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
                    home.state.borrow_mut().variants.insert(path.clone(), tag);
                    (*payload_offset, fields)
                }
                NativeShape::Scalar | NativeShape::Reference { .. } => {
                    let value = unsafe { layout.read(pointer, budget)? };
                    if let VmValue::Reference {
                        target,
                        fields,
                        unique,
                        referent,
                    } = value
                    {
                        let target = match target {
                            ReferenceTarget::Home(home) => {
                                StoredTarget::Home(Arc::downgrade(&home))
                            }
                            ReferenceTarget::Native(native) => StoredTarget::Native(native),
                            _ => {
                                return Err(error("native result reference lacks a native origin"));
                            }
                        };
                        home.state.borrow_mut().references.insert(
                            path.clone(),
                            StoredReference {
                                pointer: unsafe { pointer.cast::<*mut u8>().read() },
                                target,
                                fields,
                                unique,
                                referent,
                            },
                        );
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
                )?;
                path.pop();
            }
            Ok(())
        }
        if !self.live.get() {
            return Err(error("native storage lifetime has ended"));
        }
        self.clear(&[]);
        if let Err(failure) = visit(self, &self.layout, self.pointer(), &mut vec![], budget, holes) {
            self.clear(&[]);
            return Err(failure);
        }
        self.state.borrow_mut().root = !holes.is_some_and(|holes| holes.contains(&vec![]));
        Ok(())
    }
    /// Lexical storage death releases bytes even when dead SSA reference
    /// carriers still retain validation metadata. Such carriers cannot revive
    /// the owner: its initialization is cleared before its allocation goes.
    pub(super) fn retire(&self) {
        self.clear(&[]);
        self.live.set(false);
        let allocation = self.allocation.borrow_mut().take();
        if let Some(allocation) = allocation {
            drop(allocation);
            self.live_bytes
                .set(self.live_bytes.get() - self.layout.memory.size());
            if self.layout.memory.size() != 0 {
                self.registry.borrow_mut().remove(&self.pointer.addr());
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
        let state = self.state.borrow();
        if !state.root || !state.holes.is_empty() {
            return Err(error("native write requires a fully initialized resident"));
        }
        for reference in state.references.values() {
            if let StoredTarget::Home(home) = &reference.target {
                home.upgrade()
                    .ok_or_else(|| error("stored reference outlived its native home"))?
                    .expose_address();
            }
        }
        unsafe {
            std::ptr::copy(self.pointer(), destination, self.layout.memory.size());
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
                NativeShape::Reference { .. } => Ok(true),
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
                NativeShape::Scalar => Ok(false),
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
        let state = self.state.borrow();
        state.root && !state.holes.iter().any(|hole| path.starts_with(hole))
    }

    pub(super) fn is_fully_initialized(&self, path: &[u32]) -> bool {
        let state = self.state.borrow();
        state.root
            && !state
                .holes
                .iter()
                .any(|hole| path.starts_with(hole) || hole.starts_with(path))
    }

    pub(super) fn clear(&self, path: &[u32]) {
        let mut state = self.state.borrow_mut();
        if path.is_empty() {
            *state = Initialization::default();
        } else {
            state.holes.retain(|hole| !hole.starts_with(path));
            state.holes.insert(path.to_vec());
            state.references.retain(|field, _| !field.starts_with(path));
            state.variants.retain(|field, _| !field.starts_with(path));
        }
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
        let mut state = self.state.borrow_mut();
        if state
            .variants
            .insert(path.to_vec(), tag)
            .is_some_and(|old| old != tag)
        {
            state.holes.retain(|hole| !hole.starts_with(path));
            state.references.retain(|field, _| !field.starts_with(path));
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
        if !self.live.get() {
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
            NativeShape::Scalar | NativeShape::Reference { .. }
        ) {
            return self.load_leaf(&layout, pointer, path, budget);
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
            _ => return self.load_leaf(layout, pointer, path, budget),
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

    fn load_leaf(
        &self,
        layout: &NativeLayout,
        pointer: *const u8,
        path: &[u32],
        budget: &mut ExecutionBudget,
    ) -> Result<VmValue, VmArtifactError> {
        if matches!(layout.shape, NativeShape::Reference { .. }) {
            let resident = unsafe { pointer.cast::<*mut u8>().read() };
            if let Some(stored) = self.state.borrow().references.get(path)
                && stored.pointer == resident
            {
                let target = match &stored.target {
                    StoredTarget::Home(home) => ReferenceTarget::Home(
                        home.upgrade()
                            .ok_or_else(|| error("stored reference outlived its native home"))?,
                    ),
                    StoredTarget::Native(native) => ReferenceTarget::Native(native.clone()),
                };
                return Ok(VmValue::Reference {
                    target,
                    fields: stored.fields.clone(),
                    unique: stored.unique,
                    referent: stored.referent.clone(),
                });
            }
            if !budget.unsafe_execution {
                return Err(error("native storage reference has no checked origin"));
            }
        }
        unsafe { layout.read(pointer, budget) }
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
        if !path.is_empty() && !self.state.borrow().root {
            return Err(error(
                "native storage field cannot initialize an absent parent",
            ));
        }
        if path.is_empty() {
            if let VmValue::Resident(source) = value {
                if self.ty() != source.ty() {
                    return Err(error("native storage move has a different layout"));
                }
                if !std::ptr::eq(self, source.as_ref()) {
                    unsafe {
                        std::ptr::copy(source.pointer(), pointer, layout.memory.size());
                    }
                    if let Some(measurements) = &self.measurements {
                        measurements.copied(AllocationKind::Home, layout.memory.size());
                    }
                    *self.state.borrow_mut() = source.state.borrow().clone();
                }
                return Ok(());
            }
            *self.state.borrow_mut() = Initialization::default();
        } else {
            let mut state = self.state.borrow_mut();
            state.holes.retain(|hole| !hole.starts_with(path));
            state.references.retain(|field, _| !field.starts_with(path));
            state.variants.retain(|field, _| !field.starts_with(path));
        }
        self.store_at(&layout, pointer, &mut path.to_vec(), value, budget)?;
        self.state.borrow_mut().root = true;
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
            self.state.borrow_mut().holes.insert(path.clone());
            return Ok(());
        }
        if let VmValue::Resident(source) = value {
            let (source_pointer, source_layout) = source.project(&[])?;
            if source_layout.ty != layout.ty {
                return Err(error("native field move has a different layout"));
            }
            let origin = source.state.borrow().clone();
            unsafe {
                std::ptr::copy(source_pointer, pointer, layout.memory.size());
            }
            if let Some(measurements) = &self.measurements {
                measurements.copied(AllocationKind::Home, layout.memory.size());
            }
            let mut state = self.state.borrow_mut();
            let prefixed =
                |relative: &[u32]| path.iter().chain(relative).copied().collect::<Vec<_>>();
            if !origin.root {
                state.holes.insert(path.clone());
            }
            state
                .holes
                .extend(origin.holes.iter().map(|hole| prefixed(hole)));
            state.references.extend(
                origin
                    .references
                    .into_iter()
                    .map(|(field, reference)| (prefixed(&field), reference)),
            );
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
                if let VmValue::Reference {
                    target: ReferenceTarget::Home(home),
                    fields,
                    unique,
                    referent,
                } = value
                {
                    let (address, selected) = home.project(fields)?;
                    if selected.ty != *referent || (!unique && !home.is_initialized(fields)) {
                        return Err(error(
                            "native storage reference has an invalid checked origin",
                        ));
                    }
                    // A typed VM-to-VM store retains the checked origin below.
                    // It does not expose this address to an opaque raw/native
                    // recipient, nor forbid a unique restoration capability.
                    unsafe {
                        pointer.cast::<*mut u8>().write(address);
                    }
                } else {
                    unsafe {
                        layout.write(pointer, value.clone())?;
                    }
                }
                if let VmValue::Reference {
                    target,
                    fields,
                    unique,
                    referent,
                } = value
                {
                    let target = match target {
                        ReferenceTarget::Home(home) => StoredTarget::Home(Arc::downgrade(home)),
                        ReferenceTarget::Native(native) => StoredTarget::Native(native.clone()),
                        _ => {
                            return Err(error(
                                "native storage reference lacks an addressable origin",
                            ));
                        }
                    };
                    self.state.borrow_mut().references.insert(
                        path.clone(),
                        StoredReference {
                            pointer: unsafe { pointer.cast::<*mut u8>().read() },
                            target,
                            fields: fields.clone(),
                            unique: *unique,
                            referent: referent.clone(),
                        },
                    );
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
            self.state.borrow_mut().variants.insert(path.clone(), tag);
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
        use super::VmPattern;
        if !self.is_initialized(path) {
            return Ok(false);
        }
        if matches!(pattern, VmPattern::Any) {
            return Ok(true);
        }
        if matches!(pattern, VmPattern::Literal(_)) {
            return Ok(super::matches_pattern(&self.load(path, budget)?, pattern));
        }
        let (pointer, layout) = self.project(path)?;
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
    fn partial_external_owner_never_reads_a_moved_reference_leaf() {
        #[repr(C)]
        struct Partial { moved: *mut i64, live: i64 }
        let mut storage = Partial { moved: std::ptr::null_mut(), live: 42 };
        let ty = VmType::Tuple(vec![VmType::Reference { unique: true, referent: Box::new(VmType::I64) }, VmType::I64]);
        let layout = Arc::new(super::super::native_memory::native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap());
        let mut budget = budget(1024);
        let pointer = (&mut storage as *mut Partial).cast();
        let holes = BTreeSet::from([vec![0]]);
        let home = unsafe { NativeHome::external_argument_with_holes(layout.clone(), pointer, &mut budget, Some(&holes)) }.unwrap();
        assert_eq!(home.pointer(), pointer);
        assert!(home.is_initialized(&[]));
        assert!(!home.is_initialized(&[0]));
        assert!(!home.is_fully_initialized(&[]));
        assert!(matches!(home.load(&[0], &mut budget).unwrap(), VmValue::Uninitialized(_)));
        assert!(matches!(home.load(&[1], &mut budget).unwrap(), VmValue::I64(42)));
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
            NativeFramePlan::new(&function, &descriptors).read_projections[0],
            Some((2, 0))
        );
        // Delimited completion is an additional consumer even though it does
        // not look like an ordinary arithmetic or projection instruction.
        function
            .instructions
            .insert(2, VmInstruction::CompleteHandler { value: 1 });
        assert_eq!(
            NativeFramePlan::new(&function, &descriptors).read_projections[0],
            None
        );
    }
}
