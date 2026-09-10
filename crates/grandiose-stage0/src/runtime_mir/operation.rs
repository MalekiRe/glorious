//! Closed runtime operations. No generic selection, deferred literal or abstract destruction exists in this language.

impl RuntimeOperation {
    pub(crate) fn destination(&self) -> Option<MirLocal> {
        match self {
            Self::ConstUnit { dst, .. } => Some(*dst),
            Self::ConstI64 { dst, .. } => Some(*dst),
            Self::ConstU8 { dst, .. } => Some(*dst),
            Self::ConstU16 { dst, .. } => Some(*dst),
            Self::ConstU32 { dst, .. } => Some(*dst),
            Self::ConstU64 { dst, .. } => Some(*dst),
            Self::ConstUsize { dst, .. } => Some(*dst),
            Self::ConstU128 { dst, .. } => Some(*dst),
            Self::ConstI8 { dst, .. } => Some(*dst),
            Self::ConstI16 { dst, .. } => Some(*dst),
            Self::ConstI32 { dst, .. } => Some(*dst),
            Self::ConstIsize { dst, .. } => Some(*dst),
            Self::ConstI128 { dst, .. } => Some(*dst),
            Self::ConstF64 { dst, .. } => Some(*dst),
            Self::ConstF32 { dst, .. } => Some(*dst),
            Self::FloatIntrinsic { dst, .. } => Some(*dst),
            Self::MemoryIntrinsic { dst, .. } => Some(*dst),
            Self::IntIntrinsic { dst, .. } => Some(*dst),
            Self::ConstBool { dst, .. } => Some(*dst),
            Self::ConstChar { dst, .. } => Some(*dst),
            Self::ConstText { dst, .. } => Some(*dst),
            Self::ConstStaticData { dst, .. } => Some(*dst),
            Self::StaticLen { dst, .. } => Some(*dst),
            Self::TextByteLen { dst, .. } => Some(*dst),
            Self::TextConcat { dst, .. } => Some(*dst),
            Self::TextEq { dst, .. } => Some(*dst),
            Self::TextFromUtf8Checked { dst, .. } => Some(*dst),
            Self::TextAsBytes { dst, .. } => Some(*dst),
            Self::CharFromU32Checked { dst, .. } => Some(*dst),
            Self::CharToU32 { dst, .. } => Some(*dst),
            Self::BytesLen { dst, .. } => Some(*dst),
            Self::BytesConcat { dst, .. } => Some(*dst),
            Self::BytesGet { dst, .. } => Some(*dst),
            Self::BytesSlice { dst, .. } => Some(*dst),
            Self::BytesFromArrayMove { dst, .. } => Some(*dst),
            Self::BytesToArray { dst, .. } => Some(*dst),
            Self::BytesUtf8ValidUpTo { dst, .. } => Some(*dst),
            Self::Blake3 { dst, .. } => Some(*dst),
            Self::StoreUsize { dst, .. }
            | Self::ArrayLen { dst, .. }
            | Self::ArrayElementIsInitialized { dst, .. }
            | Self::TakeArrayElement { dst, .. } => Some(*dst),
            Self::ArrayGetBorrowShared { dst, .. } => Some(*dst),
            Self::ArrayEmpty { dst, .. } => Some(*dst),
            Self::ArrayPushMove { .. } => None,
            Self::U32CheckedAdd { dst, .. } => Some(*dst),
            Self::U32CheckedSub { dst, .. } => Some(*dst),
            Self::U32CheckedMul { dst, .. } => Some(*dst),
            Self::U32CheckedDiv { dst, .. } => Some(*dst),
            Self::U32CheckedRem { dst, .. } => Some(*dst),
            Self::U32WrappingAdd { dst, .. } => Some(*dst),
            Self::U32WrappingSub { dst, .. } => Some(*dst),
            Self::U32WrappingMul { dst, .. } => Some(*dst),
            Self::U32WrappingShl { dst, .. } => Some(*dst),
            Self::U32WrappingShr { dst, .. } => Some(*dst),
            Self::U32CheckedShl { dst, .. } => Some(*dst),
            Self::U32CheckedShr { dst, .. } => Some(*dst),
            Self::U32Eq { dst, .. } => Some(*dst),
            Self::U32Lt { dst, .. } => Some(*dst),
            Self::U32Le { dst, .. } => Some(*dst),
            Self::U32ToUsize { dst, .. } => Some(*dst),
            Self::UsizeToU32Checked { dst, .. } => Some(*dst),
            Self::I64ToU32Checked { dst, .. } => Some(*dst),
            Self::I64ToU32Wrapping { dst, .. } => Some(*dst),
            Self::I64ToUsizeChecked { dst, .. } => Some(*dst),
            Self::I64ToUsizeWrapping { dst, .. } => Some(*dst),
            Self::I64ToU8Checked { dst, .. } => Some(*dst),
            Self::I64ToU8Wrapping { dst, .. } => Some(*dst),
            Self::I64ToU16Checked { dst, .. } => Some(*dst),
            Self::I64ToU16Wrapping { dst, .. } => Some(*dst),
            Self::I64ToI16Checked { dst, .. } => Some(*dst),
            Self::I64ToI16Wrapping { dst, .. } => Some(*dst),
            Self::I64ToI32Checked { dst, .. } => Some(*dst),
            Self::I64ToI32Wrapping { dst, .. } => Some(*dst),
            Self::I64ToI8Checked { dst, .. } => Some(*dst),
            Self::I64ToI8Wrapping { dst, .. } => Some(*dst),
            Self::I64ToU64Checked { dst, .. } => Some(*dst),
            Self::I64ToU64Wrapping { dst, .. } => Some(*dst),
            Self::I64ToIsizeChecked { dst, .. } => Some(*dst),
            Self::I64ToIsizeWrapping { dst, .. } => Some(*dst),
            Self::I64ToU128Checked { dst, .. } => Some(*dst),
            Self::I64ToU128Wrapping { dst, .. } => Some(*dst),
            Self::I64ToI128Checked { dst, .. } => Some(*dst),
            Self::I64ToI128Wrapping { dst, .. } => Some(*dst),
            Self::MakeTuple { dst, .. } => Some(*dst),
            Self::MakeArray { dst, .. } => Some(*dst),
            Self::MakeRecord { dst, .. } => Some(*dst),
            Self::MakeEnum { dst, .. } => Some(*dst),
            Self::ProjectRecord { dst, .. } => Some(*dst),
            Self::TakeProjection { dst, .. } => Some(*dst),
            Self::IsInitialized { dst, .. } => Some(*dst),
            Self::DestroyCallable { dst, .. } => Some(*dst),
            Self::ProjectTuple { dst, .. } => Some(*dst),
            Self::ProjectArray { dst, .. } => Some(*dst),
            Self::UpdateRecord { dst, .. } => Some(*dst),
            Self::PatternTest { dst, .. } => Some(*dst),
            Self::Perform { dst, .. } => Some(*dst),
            Self::InstallHandler { .. } | Self::ClaimEffectPayloads { .. } => None,
            Self::UninstallHandler => None,
            Self::CompleteHandler { .. } => None,
            Self::CaptureResumption { dst, .. } => Some(*dst),
            Self::Resume { .. } => None,
            Self::ResumeReturn { dst, .. } => Some(*dst),
            Self::ResumeSnapshot { .. } => None,
            Self::Forward { .. } => None,
            Self::Cancel { .. } => None,
            Self::StorageLive { .. } => None,
            Self::StorageDead { .. } => None,
            Self::SetDropFlag { flag, .. } => Some(*flag),
            Self::DestroyIf { .. } => None,
            Self::Copy { dst, .. } => Some(*dst),
            Self::Store { dst, .. } => Some(*dst),
            Self::Move { dst, .. } => Some(*dst),
            Self::Borrow { dst, .. } => Some(*dst),
            Self::DerefCopy { dst, .. } => Some(*dst),
            Self::DerefMove { dst, .. } => Some(*dst),
            Self::DerefIsInitialized { dst, .. } => Some(*dst),
            Self::DerefStore { .. } => None,
            Self::NotBool { dst, .. } => Some(*dst),
            Self::AddI64 { dst, .. } => Some(*dst),
            Self::WrappingAddI64 { dst, .. } => Some(*dst),
            Self::WrappingSubI64 { dst, .. } => Some(*dst),
            Self::WrappingMulI64 { dst, .. } => Some(*dst),
            Self::IntEqualI64 { dst, .. } => Some(*dst),
            Self::IntLessI64 { dst, .. } => Some(*dst),
            Self::IntGreaterI64 { dst, .. } => Some(*dst),
            Self::BitAndI64 { dst, .. } => Some(*dst),
            Self::BitAndU32 { dst, .. } => Some(*dst),
            Self::BitAndU64 { dst, .. } => Some(*dst),
            Self::BitXorI64 { dst, .. } => Some(*dst),
            Self::IntShrI64 { dst, .. } => Some(*dst),
            Self::BitOrI64 { dst, .. } => Some(*dst),
            Self::BitNotI64 { dst, .. } => Some(*dst),
            Self::ShlI64 { dst, .. } => Some(*dst),
            Self::SubI64 { dst, .. } => Some(*dst),
            Self::MulI64 { dst, .. } => Some(*dst),
            Self::DivI64 { dst, .. } => Some(*dst),
            Self::RemI64 { dst, .. } => Some(*dst),
            Self::AddF64 { dst, .. } => Some(*dst),
            Self::ConcatText { dst, .. } => Some(*dst),
            Self::SubF64 { dst, .. } => Some(*dst),
            Self::MulF64 { dst, .. } => Some(*dst),
            Self::DivF64 { dst, .. } => Some(*dst),
            Self::RemF64 { dst, .. } => Some(*dst),
            Self::EqI64 { dst, .. } => Some(*dst),
            Self::NeI64 { dst, .. } => Some(*dst),
            Self::NeU32 { dst, .. } => Some(*dst),
            Self::NeU64 { dst, .. } => Some(*dst),
            Self::LtI64 { dst, .. } => Some(*dst),
            Self::LeI64 { dst, .. } => Some(*dst),
            Self::GtI64 { dst, .. } => Some(*dst),
            Self::GeI64 { dst, .. } => Some(*dst),
            Self::EqF64 { dst, .. } => Some(*dst),
            Self::NeF64 { dst, .. } => Some(*dst),
            Self::LtF64 { dst, .. } => Some(*dst),
            Self::LeF64 { dst, .. } => Some(*dst),
            Self::GtF64 { dst, .. } => Some(*dst),
            Self::GeF64 { dst, .. } => Some(*dst),
            Self::EqBool { dst, .. } => Some(*dst),
            Self::NeBool { dst, .. } => Some(*dst),
            Self::EqText { dst, .. } => Some(*dst),
            Self::NeText { dst, .. } => Some(*dst),
            Self::EqChar { dst, .. } => Some(*dst),
            Self::NeChar { dst, .. } => Some(*dst),
            Self::LtChar { dst, .. } => Some(*dst),
            Self::LeChar { dst, .. } => Some(*dst),
            Self::GtChar { dst, .. } => Some(*dst),
            Self::GeChar { dst, .. } => Some(*dst),
            Self::Call { dst, .. } => Some(*dst),
            Self::HostCall { dst, .. } => Some(*dst),
            Self::Abort => None,
            Self::MakeCallable { dst, .. } => Some(*dst),
            Self::MakeLabel { dst, .. } => Some(*dst),
            Self::CallIndirect { dst, .. } => Some(*dst),
        }
    }
    pub(crate) fn references(&self) -> Vec<MirLocal> {
        match self {
            Self::StoreUsize { dst, value } | Self::ArrayLen { dst, value } => vec![*dst, *value],
            Self::ArrayElementIsInitialized { dst, value, index }
            | Self::TakeArrayElement { dst, value, index } => vec![*dst, *value, *index],
            Self::ConstUnit { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstI64 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstU8 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstU16 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstU32 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstU64 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstUsize { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstU128 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstI8 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstI16 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstI32 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstIsize { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstI128 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstF64 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstF32 { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::FloatIntrinsic { dst, arguments, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(arguments.iter().copied());
                values
            }
            Self::MemoryIntrinsic { dst, arguments, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(arguments.iter().copied());
                values
            }
            Self::IntIntrinsic { dst, arguments, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(arguments.iter().copied());
                values
            }
            Self::ConstBool { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstChar { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstText { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ConstStaticData { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::StaticLen { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::TextByteLen { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::TextConcat {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::TextEq {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::TextFromUtf8Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::TextAsBytes { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::CharFromU32Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::CharToU32 { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::BytesLen { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::BytesConcat {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::BytesGet {
                dst, bytes, index, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*bytes);
                values.push(*index);
                values
            }
            Self::BytesSlice {
                dst,
                bytes,
                start,
                end,
                ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*bytes);
                values.push(*start);
                values.push(*end);
                values
            }
            Self::BytesFromArrayMove { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::BytesToArray { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::BytesUtf8ValidUpTo { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::Blake3 { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::ArrayGetBorrowShared {
                dst, value, index, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values.push(*index);
                values
            }
            Self::ArrayEmpty { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::ArrayPushMove { value, item, .. } => {
                let mut values = Vec::new();
                values.push(*value);
                values.push(*item);
                values
            }
            Self::U32CheckedAdd {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32CheckedSub {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32CheckedMul {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32CheckedDiv {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32CheckedRem {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32WrappingAdd {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32WrappingSub {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32WrappingMul {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32WrappingShl {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32WrappingShr {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32CheckedShl {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32CheckedShr {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32Eq {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32Lt {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32Le {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::U32ToUsize { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::UsizeToU32Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU32Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU32Wrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToUsizeChecked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToUsizeWrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU8Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU8Wrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU16Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU16Wrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToI16Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToI16Wrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToI32Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToI32Wrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToI8Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToI8Wrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU64Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU64Wrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToIsizeChecked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToIsizeWrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU128Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToU128Wrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToI128Checked { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::I64ToI128Wrapping { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::MakeTuple { dst, fields, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(fields.iter().copied());
                values
            }
            Self::MakeArray { dst, fields, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(fields.iter().copied());
                values
            }
            Self::MakeRecord { dst, fields, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(fields.iter().copied());
                values
            }
            Self::MakeEnum { dst, fields, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(fields.iter().copied());
                values
            }
            Self::ProjectRecord { dst, base, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*base);
                values
            }
            Self::TakeProjection { dst, base, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*base);
                values
            }
            Self::IsInitialized { dst, base, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*base);
                values
            }
            Self::DestroyCallable { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::ProjectTuple { dst, base, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*base);
                values
            }
            Self::ProjectArray { dst, base, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*base);
                values
            }
            Self::UpdateRecord {
                dst, base, value, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*base);
                values.push(*value);
                values
            }
            Self::PatternTest { dst, subject, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*subject);
                values
            }
            Self::Perform { dst, arguments, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(arguments.iter().copied());
                values
            }
            Self::InstallHandler {
                payload_destinations,
                ..
            } => {
                let mut values = Vec::new();
                values.extend(payload_destinations.iter().copied());
                values
            }
            Self::ClaimEffectPayloads { payloads } => payloads.clone(),
            Self::UninstallHandler => Vec::new(),
            Self::CompleteHandler { value } => vec![*value],
            Self::CaptureResumption { dst, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values
            }
            Self::Resume { value, .. } => {
                let mut values = Vec::new();
                values.push(*value);
                values
            }
            Self::ResumeReturn { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::ResumeSnapshot {
                snapshot, value, ..
            } => {
                let mut values = Vec::new();
                values.push(*snapshot);
                values.push(*value);
                values
            }
            Self::Forward { .. } => Vec::new(),
            Self::Cancel { .. } => Vec::new(),
            Self::StorageLive { local, .. } => {
                let mut values = Vec::new();
                values.push(*local);
                values
            }
            Self::StorageDead { local, .. } => {
                let mut values = Vec::new();
                values.push(*local);
                values
            }
            Self::SetDropFlag { flag, .. } => {
                let mut values = Vec::new();
                values.push(*flag);
                values
            }
            Self::DestroyIf { local, flag, .. } => {
                let mut values = Vec::new();
                values.push(*local);
                values.push(*flag);
                values
            }
            Self::Copy { dst, src, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*src);
                values
            }
            Self::Store { dst, src, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*src);
                values
            }
            Self::Move { dst, src, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*src);
                values
            }
            Self::Borrow { dst, src, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*src);
                values
            }
            Self::DerefCopy { dst, reference, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*reference);
                values
            }
            Self::DerefMove { dst, reference, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*reference);
                values
            }
            Self::DerefIsInitialized { dst, reference, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*reference);
                values
            }
            Self::DerefStore { reference, src, .. } => {
                let mut values = Vec::new();
                values.push(*reference);
                values.push(*src);
                values
            }
            Self::NotBool { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::AddI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::WrappingAddI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::WrappingSubI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::WrappingMulI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::IntEqualI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::IntLessI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::IntGreaterI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::BitAndI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::BitAndU32 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::BitAndU64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::BitXorI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::IntShrI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::BitOrI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::BitNotI64 { dst, value, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values
            }
            Self::ShlI64 {
                dst, value, count, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*value);
                values.push(*count);
                values
            }
            Self::SubI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::MulI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::DivI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::RemI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::AddF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::ConcatText {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::SubF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::MulF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::DivF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::RemF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::EqI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::NeI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::NeU32 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::NeU64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::LtI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::LeI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::GtI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::GeI64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::EqF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::NeF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::LtF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::LeF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::GtF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::GeF64 {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::EqBool {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::NeBool {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::EqText {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::NeText {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::EqChar {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::NeChar {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::LtChar {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::LeChar {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::GtChar {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::GeChar {
                dst, left, right, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*left);
                values.push(*right);
                values
            }
            Self::Call { dst, arguments, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(arguments.iter().copied());
                values
            }
            Self::HostCall { dst, arguments, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(arguments.iter().copied());
                values
            }
            Self::Abort => Vec::new(),
            Self::MakeCallable { dst, captures, .. } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.extend(captures.iter().copied());
                values
            }
            Self::MakeLabel {
                dst, destination, ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*destination);
                values
            }
            Self::CallIndirect {
                dst,
                callee,
                arguments,
                ..
            } => {
                let mut values = Vec::new();
                values.push(*dst);
                values.push(*callee);
                values.extend(arguments.iter().copied());
                values
            }
        }
    }
}

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuntimeOperation {
    ConstUnit {
        dst: MirLocal,
    },
    ConstI64 {
        dst: MirLocal,
        value: i64,
    },
    ConstU8 {
        dst: MirLocal,
        value: u8,
    },
    ConstU16 {
        dst: MirLocal,
        value: u16,
    },
    ConstU32 {
        dst: MirLocal,
        value: u32,
    },
    ConstU64 {
        dst: MirLocal,
        value: u64,
    },
    ConstUsize {
        dst: MirLocal,
        value: u64,
    },
    ConstU128 {
        dst: MirLocal,
        value: u128,
    },
    ConstI8 {
        dst: MirLocal,
        value: i8,
    },
    ConstI16 {
        dst: MirLocal,
        value: i16,
    },
    ConstI32 {
        dst: MirLocal,
        value: i32,
    },
    ConstIsize {
        dst: MirLocal,
        value: i64,
    },
    ConstI128 {
        dst: MirLocal,
        value: i128,
    },
    ConstF64 {
        dst: MirLocal,
        bits: u64,
    },
    ConstF32 {
        dst: MirLocal,
        bits: u32,
    },
    FloatIntrinsic {
        dst: MirLocal,
        primitive: FloatPrimitive,
        arguments: Vec<MirLocal>,
    },
    MemoryIntrinsic {
        dst: MirLocal,
        primitive: crate::MemoryPrimitive,
        types: Vec<Type>,
        arguments: Vec<MirLocal>,
    },
    IntIntrinsic {
        dst: MirLocal,
        primitive: PrimitiveRole,
        scalar: crate::types::ScalarType,
        arguments: Vec<MirLocal>,
    },
    ConstBool {
        dst: MirLocal,
        value: bool,
    },
    ConstChar {
        dst: MirLocal,
        value: u32,
    },
    ConstText {
        dst: MirLocal,
        value: String,
    },
    ConstStaticData {
        dst: MirLocal,
        tag: u128,
        alignment: u32,
        bytes: Vec<u8>,
    },
    StaticLen {
        dst: MirLocal,
        value: MirLocal,
    },
    TextByteLen {
        dst: MirLocal,
        value: MirLocal,
    },
    TextConcat {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    TextEq {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    TextFromUtf8Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    TextAsBytes {
        dst: MirLocal,
        value: MirLocal,
    },
    CharFromU32Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    CharToU32 {
        dst: MirLocal,
        value: MirLocal,
    },
    BytesLen {
        dst: MirLocal,
        value: MirLocal,
    },
    BytesConcat {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    BytesGet {
        dst: MirLocal,
        bytes: MirLocal,
        index: MirLocal,
    },
    BytesSlice {
        dst: MirLocal,
        bytes: MirLocal,
        start: MirLocal,
        end: MirLocal,
    },
    BytesFromArrayMove {
        dst: MirLocal,
        value: MirLocal,
    },
    BytesToArray {
        dst: MirLocal,
        value: MirLocal,
    },
    BytesUtf8ValidUpTo {
        dst: MirLocal,
        value: MirLocal,
    },
    Blake3 {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Read the extent without copying or consuming the array.
    ArrayLen {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Assign a compiler-owned, activation-local loop counter.
    StoreUsize {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Probe a dynamically indexed move hole.
    ArrayElementIsInitialized {
        dst: MirLocal,
        value: MirLocal,
        index: MirLocal,
    },
    /// Move one element out, leaving a hole in the owning array.
    TakeArrayElement {
        dst: MirLocal,
        value: MirLocal,
        index: MirLocal,
    },
    ArrayGetBorrowShared {
        dst: MirLocal,
        value: MirLocal,
        index: MirLocal,
        element_type: Type,
    },
    ArrayEmpty {
        dst: MirLocal,
        element_type: Type,
    },
    ArrayPushMove {
        value: MirLocal,
        item: MirLocal,
        element_type: Type,
    },
    U32CheckedAdd {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedSub {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedMul {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedDiv {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedRem {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingAdd {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingSub {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingMul {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingShl {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingShr {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedShl {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedShr {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32Eq {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32Lt {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32Le {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32ToUsize {
        dst: MirLocal,
        value: MirLocal,
    },
    UsizeToU32Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU32Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU32Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToUsizeChecked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToUsizeWrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU8Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU8Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU16Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU16Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI16Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI16Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI32Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI32Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI8Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI8Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU64Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU64Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToIsizeChecked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToIsizeWrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU128Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU128Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI128Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI128Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    MakeTuple {
        dst: MirLocal,
        fields: Vec<MirLocal>,
    },
    MakeArray {
        dst: MirLocal,
        fields: Vec<MirLocal>,
        element_type: Type,
    },
    MakeRecord {
        dst: MirLocal,
        definition: DefKey,
        fields: Vec<MirLocal>,
        field_types: Vec<Type>,
    },
    MakeEnum {
        dst: MirLocal,
        definition: DefKey,
        variant: u32,
        fields: Vec<MirLocal>,
        field_types: Vec<Type>,
    },
    ProjectRecord {
        dst: MirLocal,
        base: MirLocal,
        index: u32,
        field_count: u32,
        field_type: Type,
    },
    TakeProjection {
        dst: MirLocal,
        base: MirLocal,
        fields: Vec<u32>,
    },
    IsInitialized {
        dst: MirLocal,
        base: MirLocal,
        fields: Vec<u32>,
    },
    DestroyCallable {
        dst: MirLocal,
        value: MirLocal,
    },
    ProjectTuple {
        dst: MirLocal,
        base: MirLocal,
        index: u32,
        field_count: u32,
        field_type: Type,
    },
    ProjectArray {
        dst: MirLocal,
        base: MirLocal,
        index: u32,
        field_count: u32,
        element_type: Type,
    },
    UpdateRecord {
        dst: MirLocal,
        base: MirLocal,
        index: u32,
        field_count: u32,
        value: MirLocal,
        field_type: Type,
    },
    PatternTest {
        dst: MirLocal,
        subject: MirLocal,
        pattern: MirPattern,
    },
    Perform {
        site: MirPerformSiteId,
        dst: MirLocal,
        effect: DefKey,
        effect_arguments: Vec<crate::GenericArgument>,
        operation: u32,
        arguments: Vec<MirLocal>,
    },
    InstallHandler {
        site: MirHandlerSiteId,
        effect: DefKey,
        effect_arguments: Vec<crate::GenericArgument>,
        operation: u32,
        payload_destinations: Vec<MirLocal>,
        resume_type: Type,
        continuation: MirContinuationPolicy,
        target: MirBlockId,
        continuation_owned: Vec<MirLocal>,
    },
    ClaimEffectPayloads { payloads: Vec<MirLocal> },
    UninstallHandler,
    CompleteHandler {
        value: MirLocal,
    },
    CaptureResumption {
        site: MirResumptionSiteId,
        dst: MirLocal,
    },
    Resume {
        site: MirResumptionSiteId,
        value: MirLocal,
    },
    ResumeReturn {
        site: MirResumptionSiteId,
        dst: MirLocal,
        value: MirLocal,
    },
    ResumeSnapshot {
        site: MirResumptionSiteId,
        snapshot: MirLocal,
        value: MirLocal,
    },
    Forward {
        site: MirResumptionSiteId,
    },
    Cancel {
        site: MirResumptionSiteId,
    },
    StorageLive {
        binding: MirPlaceBindingId,
        local: MirLocal,
    },
    StorageDead {
        binding: MirPlaceBindingId,
        local: MirLocal,
    },
    SetDropFlag {
        flag: MirLocal,
        value: bool,
    },
    DestroyIf {
        local: MirLocal,
        flag: MirLocal,
    },
    Copy {
        dst: MirLocal,
        src: MirLocal,
    },
    Store {
        dst: MirLocal,
        src: MirLocal,
    },
    Move {
        dst: MirLocal,
        src: MirLocal,
    },
    Borrow {
        dst: MirLocal,
        src: MirLocal,
        fields: Vec<u32>,
        unique: bool,
        reborrow: bool,
    },
    DerefCopy {
        dst: MirLocal,
        reference: MirLocal,
    },
    DerefMove {
        dst: MirLocal,
        reference: MirLocal,
    },
    DerefIsInitialized {
        dst: MirLocal,
        reference: MirLocal,
    },
    DerefStore {
        reference: MirLocal,
        src: MirLocal,
    },
    NotBool {
        dst: MirLocal,
        value: MirLocal,
    },
    AddI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    WrappingAddI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    WrappingSubI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    WrappingMulI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    IntEqualI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    IntLessI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    IntGreaterI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    BitAndI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    BitAndU32 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    BitAndU64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    BitXorI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    IntShrI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    BitOrI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    BitNotI64 {
        dst: MirLocal,
        value: MirLocal,
    },
    ShlI64 {
        dst: MirLocal,
        value: MirLocal,
        count: MirLocal,
    },
    SubI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    MulI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    DivI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    RemI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    AddF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    ConcatText {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    SubF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    MulF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    DivF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    RemF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeU32 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeU64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LtI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LeI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GtI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GeI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LtF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LeF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GtF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GeF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqBool {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeBool {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqText {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeText {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LtChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LeChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GtChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GeChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    Call {
        dst: MirLocal,
        callee: DefKey,
        arguments: Vec<MirLocal>,
    },
    HostCall {
        dst: MirLocal,
        capability: String,
        symbol: String,
        source_contract: crate::Digest,
        parameters: Vec<Type>,
        result: Type,
        resident_operations: Vec<(Type, Option<DefKey>)>,
        arguments: Vec<MirLocal>,
    },
    Abort,
    MakeCallable {
        dst: MirLocal,
        callee: DefKey,
        captures: Vec<MirLocal>,
        environment: Option<MirCaptureEnvironment>,
    },
    MakeLabel {
        label: MirLabelId,
        dst: MirLocal,
        brand: crate::LabelBrand,
        target: MirBlockId,
        destination: MirLocal,
    },
    CallIndirect {
        dst: MirLocal,
        callee: MirLocal,
        arguments: Vec<MirLocal>,
    },
}

impl RuntimeOperation {
    pub(crate) fn from_atomic(value: crate::MirInstruction) -> Result<Self, RuntimeError> {
        Ok(match value {
            crate::MirInstruction::ConstUnit { dst } => Self::ConstUnit { dst },
            crate::MirInstruction::ConstI64 { dst, value } => Self::ConstI64 { dst, value },
            crate::MirInstruction::ConstU8 { dst, value } => Self::ConstU8 { dst, value },
            crate::MirInstruction::ConstU16 { dst, value } => Self::ConstU16 { dst, value },
            crate::MirInstruction::ConstU32 { dst, value } => Self::ConstU32 { dst, value },
            crate::MirInstruction::ConstU64 { dst, value } => Self::ConstU64 { dst, value },
            crate::MirInstruction::ConstUsize { dst, value } => Self::ConstUsize { dst, value },
            crate::MirInstruction::ConstU128 { dst, value } => Self::ConstU128 { dst, value },
            crate::MirInstruction::ConstI8 { dst, value } => Self::ConstI8 { dst, value },
            crate::MirInstruction::ConstI16 { dst, value } => Self::ConstI16 { dst, value },
            crate::MirInstruction::ConstI32 { dst, value } => Self::ConstI32 { dst, value },
            crate::MirInstruction::ConstIsize { dst, value } => Self::ConstIsize { dst, value },
            crate::MirInstruction::ConstI128 { dst, value } => Self::ConstI128 { dst, value },
            crate::MirInstruction::ConstF64 { dst, bits } => Self::ConstF64 { dst, bits },
            crate::MirInstruction::ConstF32 { dst, bits } => Self::ConstF32 { dst, bits },
            crate::MirInstruction::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            } => Self::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            },
            crate::MirInstruction::MemoryIntrinsic {
                dst,
                primitive,
                types,
                arguments,
            } => Self::MemoryIntrinsic {
                dst,
                primitive,
                types,
                arguments,
            },
            crate::MirInstruction::IntIntrinsic {
                dst,
                primitive,
                scalar,
                arguments,
            } => Self::IntIntrinsic {
                dst,
                primitive,
                scalar,
                arguments,
            },
            crate::MirInstruction::ConstBool { dst, value } => Self::ConstBool { dst, value },
            crate::MirInstruction::ConstChar { dst, value } => Self::ConstChar { dst, value },
            crate::MirInstruction::ConstText { dst, value } => Self::ConstText { dst, value },
            crate::MirInstruction::ConstStaticData {
                dst,
                tag,
                alignment,
                bytes,
            } => Self::ConstStaticData {
                dst,
                tag,
                alignment,
                bytes,
            },
            crate::MirInstruction::StaticLen { dst, value } => Self::StaticLen { dst, value },
            crate::MirInstruction::TextByteLen { dst, value } => Self::TextByteLen { dst, value },
            crate::MirInstruction::TextConcat { dst, left, right } => {
                Self::TextConcat { dst, left, right }
            }
            crate::MirInstruction::TextEq { dst, left, right } => Self::TextEq { dst, left, right },
            crate::MirInstruction::TextFromUtf8Checked { dst, value } => {
                Self::TextFromUtf8Checked { dst, value }
            }
            crate::MirInstruction::TextAsBytes { dst, value } => Self::TextAsBytes { dst, value },
            crate::MirInstruction::CharFromU32Checked { dst, value } => {
                Self::CharFromU32Checked { dst, value }
            }
            crate::MirInstruction::CharToU32 { dst, value } => Self::CharToU32 { dst, value },
            crate::MirInstruction::BytesLen { dst, value } => Self::BytesLen { dst, value },
            crate::MirInstruction::BytesConcat { dst, left, right } => {
                Self::BytesConcat { dst, left, right }
            }
            crate::MirInstruction::BytesGet { dst, bytes, index } => {
                Self::BytesGet { dst, bytes, index }
            }
            crate::MirInstruction::BytesSlice {
                dst,
                bytes,
                start,
                end,
            } => Self::BytesSlice {
                dst,
                bytes,
                start,
                end,
            },
            crate::MirInstruction::BytesFromArrayMove { dst, value } => {
                Self::BytesFromArrayMove { dst, value }
            }
            crate::MirInstruction::BytesToArray { dst, value } => Self::BytesToArray { dst, value },
            crate::MirInstruction::BytesUtf8ValidUpTo { dst, value } => {
                Self::BytesUtf8ValidUpTo { dst, value }
            }
            crate::MirInstruction::Blake3 { dst, value } => Self::Blake3 { dst, value },
            crate::MirInstruction::ArrayGetBorrowShared {
                dst,
                value,
                index,
                element_type,
            } => Self::ArrayGetBorrowShared {
                dst,
                value,
                index,
                element_type,
            },
            crate::MirInstruction::StoreUsize { dst, value } => Self::StoreUsize { dst, value },
            crate::MirInstruction::ArrayLen { dst, value } => Self::ArrayLen { dst, value },
            crate::MirInstruction::ArrayElementIsInitialized { dst, value, index } => {
                Self::ArrayElementIsInitialized { dst, value, index }
            }
            crate::MirInstruction::TakeArrayElement { dst, value, index } => {
                Self::TakeArrayElement { dst, value, index }
            }
            crate::MirInstruction::ArrayEmpty { dst, element_type } => {
                Self::ArrayEmpty { dst, element_type }
            }
            crate::MirInstruction::ArrayPushMove {
                value,
                item,
                element_type,
            } => Self::ArrayPushMove {
                value,
                item,
                element_type,
            },
            crate::MirInstruction::U32CheckedAdd { dst, left, right } => {
                Self::U32CheckedAdd { dst, left, right }
            }
            crate::MirInstruction::U32CheckedSub { dst, left, right } => {
                Self::U32CheckedSub { dst, left, right }
            }
            crate::MirInstruction::U32CheckedMul { dst, left, right } => {
                Self::U32CheckedMul { dst, left, right }
            }
            crate::MirInstruction::U32CheckedDiv { dst, left, right } => {
                Self::U32CheckedDiv { dst, left, right }
            }
            crate::MirInstruction::U32CheckedRem { dst, left, right } => {
                Self::U32CheckedRem { dst, left, right }
            }
            crate::MirInstruction::U32WrappingAdd { dst, left, right } => {
                Self::U32WrappingAdd { dst, left, right }
            }
            crate::MirInstruction::U32WrappingSub { dst, left, right } => {
                Self::U32WrappingSub { dst, left, right }
            }
            crate::MirInstruction::U32WrappingMul { dst, left, right } => {
                Self::U32WrappingMul { dst, left, right }
            }
            crate::MirInstruction::U32WrappingShl { dst, left, right } => {
                Self::U32WrappingShl { dst, left, right }
            }
            crate::MirInstruction::U32WrappingShr { dst, left, right } => {
                Self::U32WrappingShr { dst, left, right }
            }
            crate::MirInstruction::U32CheckedShl { dst, left, right } => {
                Self::U32CheckedShl { dst, left, right }
            }
            crate::MirInstruction::U32CheckedShr { dst, left, right } => {
                Self::U32CheckedShr { dst, left, right }
            }
            crate::MirInstruction::U32Eq { dst, left, right } => Self::U32Eq { dst, left, right },
            crate::MirInstruction::U32Lt { dst, left, right } => Self::U32Lt { dst, left, right },
            crate::MirInstruction::U32Le { dst, left, right } => Self::U32Le { dst, left, right },
            crate::MirInstruction::U32ToUsize { dst, value } => Self::U32ToUsize { dst, value },
            crate::MirInstruction::UsizeToU32Checked { dst, value } => {
                Self::UsizeToU32Checked { dst, value }
            }
            crate::MirInstruction::I64ToU32Checked { dst, value } => {
                Self::I64ToU32Checked { dst, value }
            }
            crate::MirInstruction::I64ToU32Wrapping { dst, value } => {
                Self::I64ToU32Wrapping { dst, value }
            }
            crate::MirInstruction::I64ToUsizeChecked { dst, value } => {
                Self::I64ToUsizeChecked { dst, value }
            }
            crate::MirInstruction::I64ToUsizeWrapping { dst, value } => {
                Self::I64ToUsizeWrapping { dst, value }
            }
            crate::MirInstruction::I64ToU8Checked { dst, value } => {
                Self::I64ToU8Checked { dst, value }
            }
            crate::MirInstruction::I64ToU8Wrapping { dst, value } => {
                Self::I64ToU8Wrapping { dst, value }
            }
            crate::MirInstruction::I64ToU16Checked { dst, value } => {
                Self::I64ToU16Checked { dst, value }
            }
            crate::MirInstruction::I64ToU16Wrapping { dst, value } => {
                Self::I64ToU16Wrapping { dst, value }
            }
            crate::MirInstruction::I64ToI16Checked { dst, value } => {
                Self::I64ToI16Checked { dst, value }
            }
            crate::MirInstruction::I64ToI16Wrapping { dst, value } => {
                Self::I64ToI16Wrapping { dst, value }
            }
            crate::MirInstruction::I64ToI32Checked { dst, value } => {
                Self::I64ToI32Checked { dst, value }
            }
            crate::MirInstruction::I64ToI32Wrapping { dst, value } => {
                Self::I64ToI32Wrapping { dst, value }
            }
            crate::MirInstruction::I64ToI8Checked { dst, value } => {
                Self::I64ToI8Checked { dst, value }
            }
            crate::MirInstruction::I64ToI8Wrapping { dst, value } => {
                Self::I64ToI8Wrapping { dst, value }
            }
            crate::MirInstruction::I64ToU64Checked { dst, value } => {
                Self::I64ToU64Checked { dst, value }
            }
            crate::MirInstruction::I64ToU64Wrapping { dst, value } => {
                Self::I64ToU64Wrapping { dst, value }
            }
            crate::MirInstruction::I64ToIsizeChecked { dst, value } => {
                Self::I64ToIsizeChecked { dst, value }
            }
            crate::MirInstruction::I64ToIsizeWrapping { dst, value } => {
                Self::I64ToIsizeWrapping { dst, value }
            }
            crate::MirInstruction::I64ToU128Checked { dst, value } => {
                Self::I64ToU128Checked { dst, value }
            }
            crate::MirInstruction::I64ToU128Wrapping { dst, value } => {
                Self::I64ToU128Wrapping { dst, value }
            }
            crate::MirInstruction::I64ToI128Checked { dst, value } => {
                Self::I64ToI128Checked { dst, value }
            }
            crate::MirInstruction::I64ToI128Wrapping { dst, value } => {
                Self::I64ToI128Wrapping { dst, value }
            }
            crate::MirInstruction::MakeTuple { dst, fields } => Self::MakeTuple { dst, fields },
            crate::MirInstruction::MakeArray {
                dst,
                fields,
                element_type,
            } => Self::MakeArray {
                dst,
                fields,
                element_type,
            },
            crate::MirInstruction::MakeRecord {
                dst,
                definition,
                fields,
                field_types,
            } => Self::MakeRecord {
                dst,
                definition,
                fields,
                field_types,
            },
            crate::MirInstruction::MakeEnum {
                dst,
                definition,
                variant,
                fields,
                field_types,
            } => Self::MakeEnum {
                dst,
                definition,
                variant,
                fields,
                field_types,
            },
            crate::MirInstruction::ProjectRecord {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => Self::ProjectRecord {
                dst,
                base,
                index,
                field_count,
                field_type,
            },
            crate::MirInstruction::TakeProjection { dst, base, fields } => {
                Self::TakeProjection { dst, base, fields }
            }
            crate::MirInstruction::IsInitialized { dst, base, fields } => {
                Self::IsInitialized { dst, base, fields }
            }
            crate::MirInstruction::DestroyCallable { dst, value } => {
                Self::DestroyCallable { dst, value }
            }
            crate::MirInstruction::ProjectTuple {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => Self::ProjectTuple {
                dst,
                base,
                index,
                field_count,
                field_type,
            },
            crate::MirInstruction::ProjectArray {
                dst,
                base,
                index,
                field_count,
                element_type,
            } => Self::ProjectArray {
                dst,
                base,
                index,
                field_count,
                element_type,
            },
            crate::MirInstruction::UpdateRecord {
                dst,
                base,
                index,
                field_count,
                value,
                field_type,
            } => Self::UpdateRecord {
                dst,
                base,
                index,
                field_count,
                value,
                field_type,
            },
            crate::MirInstruction::PatternTest {
                dst,
                subject,
                pattern,
            } => Self::PatternTest {
                dst,
                subject,
                pattern,
            },
            crate::MirInstruction::Perform {
                site,
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            } => Self::Perform {
                site,
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            },
            crate::MirInstruction::InstallHandler {
                site,
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                resume_type,
                continuation,
                target,
            } => Self::InstallHandler {
                site,
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                resume_type,
                continuation,
                target,
                continuation_owned: vec![],
            },
            crate::MirInstruction::ClaimEffectPayloads { payloads } => Self::ClaimEffectPayloads { payloads },
            crate::MirInstruction::UninstallHandler => Self::UninstallHandler,
            crate::MirInstruction::CompleteHandler { value } => Self::CompleteHandler { value },
            crate::MirInstruction::CaptureResumption { site, dst } => {
                Self::CaptureResumption { site, dst }
            }
            crate::MirInstruction::Resume { site, value } => Self::Resume { site, value },
            crate::MirInstruction::ResumeReturn { site, dst, value } => {
                Self::ResumeReturn { site, dst, value }
            }
            crate::MirInstruction::ResumeSnapshot {
                site,
                snapshot,
                value,
            } => Self::ResumeSnapshot {
                site,
                snapshot,
                value,
            },
            crate::MirInstruction::Forward { site } => Self::Forward { site },
            crate::MirInstruction::Cancel { site } => Self::Cancel { site },
            crate::MirInstruction::StorageLive { binding, local } => {
                Self::StorageLive { binding, local }
            }
            crate::MirInstruction::StorageDead { binding, local } => {
                Self::StorageDead { binding, local }
            }
            crate::MirInstruction::SetDropFlag { flag, value } => Self::SetDropFlag { flag, value },
            crate::MirInstruction::DestroyIf { local, flag } => Self::DestroyIf { local, flag },
            crate::MirInstruction::Copy { dst, src } => Self::Copy { dst, src },
            crate::MirInstruction::Store { dst, src } => Self::Store { dst, src },
            crate::MirInstruction::Move { dst, src } => Self::Move { dst, src },
            crate::MirInstruction::Borrow {
                dst,
                src,
                fields,
                unique,
                reborrow,
            } => Self::Borrow {
                dst,
                src,
                fields,
                unique,
                reborrow,
            },
            crate::MirInstruction::DerefCopy { dst, reference } => {
                Self::DerefCopy { dst, reference }
            }
            crate::MirInstruction::DerefMove { dst, reference } => {
                Self::DerefMove { dst, reference }
            }
            crate::MirInstruction::DerefIsInitialized { dst, reference } => {
                Self::DerefIsInitialized { dst, reference }
            }
            crate::MirInstruction::DerefStore { reference, src } => {
                Self::DerefStore { reference, src }
            }
            crate::MirInstruction::NotBool { dst, value } => Self::NotBool { dst, value },
            crate::MirInstruction::AddI64 { dst, left, right } => Self::AddI64 { dst, left, right },
            crate::MirInstruction::WrappingAddI64 { dst, left, right } => {
                Self::WrappingAddI64 { dst, left, right }
            }
            crate::MirInstruction::WrappingSubI64 { dst, left, right } => {
                Self::WrappingSubI64 { dst, left, right }
            }
            crate::MirInstruction::WrappingMulI64 { dst, left, right } => {
                Self::WrappingMulI64 { dst, left, right }
            }
            crate::MirInstruction::IntEqualI64 { dst, left, right } => {
                Self::IntEqualI64 { dst, left, right }
            }
            crate::MirInstruction::IntLessI64 { dst, left, right } => {
                Self::IntLessI64 { dst, left, right }
            }
            crate::MirInstruction::IntGreaterI64 { dst, left, right } => {
                Self::IntGreaterI64 { dst, left, right }
            }
            crate::MirInstruction::BitAndI64 { dst, left, right } => {
                Self::BitAndI64 { dst, left, right }
            }
            crate::MirInstruction::BitAndU32 { dst, left, right } => {
                Self::BitAndU32 { dst, left, right }
            }
            crate::MirInstruction::BitAndU64 { dst, left, right } => {
                Self::BitAndU64 { dst, left, right }
            }
            crate::MirInstruction::BitXorI64 { dst, left, right } => {
                Self::BitXorI64 { dst, left, right }
            }
            crate::MirInstruction::IntShrI64 { dst, left, right } => {
                Self::IntShrI64 { dst, left, right }
            }
            crate::MirInstruction::BitOrI64 { dst, left, right } => {
                Self::BitOrI64 { dst, left, right }
            }
            crate::MirInstruction::BitNotI64 { dst, value } => Self::BitNotI64 { dst, value },
            crate::MirInstruction::ShlI64 { dst, value, count } => {
                Self::ShlI64 { dst, value, count }
            }
            crate::MirInstruction::SubI64 { dst, left, right } => Self::SubI64 { dst, left, right },
            crate::MirInstruction::MulI64 { dst, left, right } => Self::MulI64 { dst, left, right },
            crate::MirInstruction::DivI64 { dst, left, right } => Self::DivI64 { dst, left, right },
            crate::MirInstruction::RemI64 { dst, left, right } => Self::RemI64 { dst, left, right },
            crate::MirInstruction::AddF64 { dst, left, right } => Self::AddF64 { dst, left, right },
            crate::MirInstruction::ConcatText { dst, left, right } => {
                Self::ConcatText { dst, left, right }
            }
            crate::MirInstruction::SubF64 { dst, left, right } => Self::SubF64 { dst, left, right },
            crate::MirInstruction::MulF64 { dst, left, right } => Self::MulF64 { dst, left, right },
            crate::MirInstruction::DivF64 { dst, left, right } => Self::DivF64 { dst, left, right },
            crate::MirInstruction::RemF64 { dst, left, right } => Self::RemF64 { dst, left, right },
            crate::MirInstruction::EqI64 { dst, left, right } => Self::EqI64 { dst, left, right },
            crate::MirInstruction::NeI64 { dst, left, right } => Self::NeI64 { dst, left, right },
            crate::MirInstruction::NeU32 { dst, left, right } => Self::NeU32 { dst, left, right },
            crate::MirInstruction::NeU64 { dst, left, right } => Self::NeU64 { dst, left, right },
            crate::MirInstruction::LtI64 { dst, left, right } => Self::LtI64 { dst, left, right },
            crate::MirInstruction::LeI64 { dst, left, right } => Self::LeI64 { dst, left, right },
            crate::MirInstruction::GtI64 { dst, left, right } => Self::GtI64 { dst, left, right },
            crate::MirInstruction::GeI64 { dst, left, right } => Self::GeI64 { dst, left, right },
            crate::MirInstruction::EqF64 { dst, left, right } => Self::EqF64 { dst, left, right },
            crate::MirInstruction::NeF64 { dst, left, right } => Self::NeF64 { dst, left, right },
            crate::MirInstruction::LtF64 { dst, left, right } => Self::LtF64 { dst, left, right },
            crate::MirInstruction::LeF64 { dst, left, right } => Self::LeF64 { dst, left, right },
            crate::MirInstruction::GtF64 { dst, left, right } => Self::GtF64 { dst, left, right },
            crate::MirInstruction::GeF64 { dst, left, right } => Self::GeF64 { dst, left, right },
            crate::MirInstruction::EqBool { dst, left, right } => Self::EqBool { dst, left, right },
            crate::MirInstruction::NeBool { dst, left, right } => Self::NeBool { dst, left, right },
            crate::MirInstruction::EqText { dst, left, right } => Self::EqText { dst, left, right },
            crate::MirInstruction::NeText { dst, left, right } => Self::NeText { dst, left, right },
            crate::MirInstruction::EqChar { dst, left, right } => Self::EqChar { dst, left, right },
            crate::MirInstruction::NeChar { dst, left, right } => Self::NeChar { dst, left, right },
            crate::MirInstruction::LtChar { dst, left, right } => Self::LtChar { dst, left, right },
            crate::MirInstruction::LeChar { dst, left, right } => Self::LeChar { dst, left, right },
            crate::MirInstruction::GtChar { dst, left, right } => Self::GtChar { dst, left, right },
            crate::MirInstruction::GeChar { dst, left, right } => Self::GeChar { dst, left, right },
            crate::MirInstruction::Call {
                dst,
                callee,
                arguments,
                generic_arguments,
                trait_instance,
            } if generic_arguments.is_empty() && trait_instance.is_none() => Self::Call {
                dst,
                callee,
                arguments,
            },
            crate::MirInstruction::HostCall {
                dst,
                capability,
                symbol,
                source_contract,
                parameters,
                result,
                resident_operations,
                arguments,
            } => Self::HostCall {
                dst,
                capability,
                symbol,
                source_contract,
                parameters,
                result,
                resident_operations,
                arguments,
            },
            crate::MirInstruction::Abort => Self::Abort,
            crate::MirInstruction::MakeCallable {
                dst,
                callee,
                captures,
                environment,
                generic_arguments,
                trait_instance,
            } if generic_arguments.is_empty() && trait_instance.is_none() => Self::MakeCallable {
                dst,
                callee,
                captures,
                environment,
            },
            crate::MirInstruction::MakeLabel {
                label,
                dst,
                brand,
                target,
                destination,
            } => Self::MakeLabel {
                label,
                dst,
                brand,
                target,
                destination,
            },
            crate::MirInstruction::CallIndirect {
                dst,
                callee,
                arguments,
            } => Self::CallIndirect {
                dst,
                callee,
                arguments,
            },
            _ => {
                return Err(RuntimeError(
                    "non-concrete instruction escaped atomic selection".into(),
                ));
            }
        })
    }
    pub(crate) fn to_backend(&self) -> crate::MirInstruction {
        match self.clone() {
            Self::ConstUnit { dst } => crate::MirInstruction::ConstUnit { dst },
            Self::ConstI64 { dst, value } => crate::MirInstruction::ConstI64 { dst, value },
            Self::ConstU8 { dst, value } => crate::MirInstruction::ConstU8 { dst, value },
            Self::ConstU16 { dst, value } => crate::MirInstruction::ConstU16 { dst, value },
            Self::ConstU32 { dst, value } => crate::MirInstruction::ConstU32 { dst, value },
            Self::ConstU64 { dst, value } => crate::MirInstruction::ConstU64 { dst, value },
            Self::ConstUsize { dst, value } => crate::MirInstruction::ConstUsize { dst, value },
            Self::ConstU128 { dst, value } => crate::MirInstruction::ConstU128 { dst, value },
            Self::ConstI8 { dst, value } => crate::MirInstruction::ConstI8 { dst, value },
            Self::ConstI16 { dst, value } => crate::MirInstruction::ConstI16 { dst, value },
            Self::ConstI32 { dst, value } => crate::MirInstruction::ConstI32 { dst, value },
            Self::ConstIsize { dst, value } => crate::MirInstruction::ConstIsize { dst, value },
            Self::ConstI128 { dst, value } => crate::MirInstruction::ConstI128 { dst, value },
            Self::ConstF64 { dst, bits } => crate::MirInstruction::ConstF64 { dst, bits },
            Self::ConstF32 { dst, bits } => crate::MirInstruction::ConstF32 { dst, bits },
            Self::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            } => crate::MirInstruction::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            },
            Self::MemoryIntrinsic {
                dst,
                primitive,
                types,
                arguments,
            } => crate::MirInstruction::MemoryIntrinsic {
                dst,
                primitive,
                types,
                arguments,
            },
            Self::IntIntrinsic {
                dst,
                primitive,
                scalar,
                arguments,
            } => crate::MirInstruction::IntIntrinsic {
                dst,
                primitive,
                scalar,
                arguments,
            },
            Self::ConstBool { dst, value } => crate::MirInstruction::ConstBool { dst, value },
            Self::ConstChar { dst, value } => crate::MirInstruction::ConstChar { dst, value },
            Self::ConstText { dst, value } => crate::MirInstruction::ConstText { dst, value },
            Self::ConstStaticData {
                dst,
                tag,
                alignment,
                bytes,
            } => crate::MirInstruction::ConstStaticData {
                dst,
                tag,
                alignment,
                bytes,
            },
            Self::StaticLen { dst, value } => crate::MirInstruction::StaticLen { dst, value },
            Self::TextByteLen { dst, value } => crate::MirInstruction::TextByteLen { dst, value },
            Self::TextConcat { dst, left, right } => {
                crate::MirInstruction::TextConcat { dst, left, right }
            }
            Self::TextEq { dst, left, right } => crate::MirInstruction::TextEq { dst, left, right },
            Self::TextFromUtf8Checked { dst, value } => {
                crate::MirInstruction::TextFromUtf8Checked { dst, value }
            }
            Self::TextAsBytes { dst, value } => crate::MirInstruction::TextAsBytes { dst, value },
            Self::CharFromU32Checked { dst, value } => {
                crate::MirInstruction::CharFromU32Checked { dst, value }
            }
            Self::CharToU32 { dst, value } => crate::MirInstruction::CharToU32 { dst, value },
            Self::BytesLen { dst, value } => crate::MirInstruction::BytesLen { dst, value },
            Self::BytesConcat { dst, left, right } => {
                crate::MirInstruction::BytesConcat { dst, left, right }
            }
            Self::BytesGet { dst, bytes, index } => {
                crate::MirInstruction::BytesGet { dst, bytes, index }
            }
            Self::BytesSlice {
                dst,
                bytes,
                start,
                end,
            } => crate::MirInstruction::BytesSlice {
                dst,
                bytes,
                start,
                end,
            },
            Self::BytesFromArrayMove { dst, value } => {
                crate::MirInstruction::BytesFromArrayMove { dst, value }
            }
            Self::BytesToArray { dst, value } => crate::MirInstruction::BytesToArray { dst, value },
            Self::BytesUtf8ValidUpTo { dst, value } => {
                crate::MirInstruction::BytesUtf8ValidUpTo { dst, value }
            }
            Self::Blake3 { dst, value } => crate::MirInstruction::Blake3 { dst, value },
            Self::ArrayGetBorrowShared {
                dst,
                value,
                index,
                element_type,
            } => crate::MirInstruction::ArrayGetBorrowShared {
                dst,
                value,
                index,
                element_type,
            },
            Self::StoreUsize { dst, value } => crate::MirInstruction::StoreUsize { dst, value },
            Self::ArrayLen { dst, value } => crate::MirInstruction::ArrayLen { dst, value },
            Self::ArrayElementIsInitialized { dst, value, index } => {
                crate::MirInstruction::ArrayElementIsInitialized { dst, value, index }
            }
            Self::TakeArrayElement { dst, value, index } => {
                crate::MirInstruction::TakeArrayElement { dst, value, index }
            }
            Self::ArrayEmpty { dst, element_type } => {
                crate::MirInstruction::ArrayEmpty { dst, element_type }
            }
            Self::ArrayPushMove {
                value,
                item,
                element_type,
            } => crate::MirInstruction::ArrayPushMove {
                value,
                item,
                element_type,
            },
            Self::U32CheckedAdd { dst, left, right } => {
                crate::MirInstruction::U32CheckedAdd { dst, left, right }
            }
            Self::U32CheckedSub { dst, left, right } => {
                crate::MirInstruction::U32CheckedSub { dst, left, right }
            }
            Self::U32CheckedMul { dst, left, right } => {
                crate::MirInstruction::U32CheckedMul { dst, left, right }
            }
            Self::U32CheckedDiv { dst, left, right } => {
                crate::MirInstruction::U32CheckedDiv { dst, left, right }
            }
            Self::U32CheckedRem { dst, left, right } => {
                crate::MirInstruction::U32CheckedRem { dst, left, right }
            }
            Self::U32WrappingAdd { dst, left, right } => {
                crate::MirInstruction::U32WrappingAdd { dst, left, right }
            }
            Self::U32WrappingSub { dst, left, right } => {
                crate::MirInstruction::U32WrappingSub { dst, left, right }
            }
            Self::U32WrappingMul { dst, left, right } => {
                crate::MirInstruction::U32WrappingMul { dst, left, right }
            }
            Self::U32WrappingShl { dst, left, right } => {
                crate::MirInstruction::U32WrappingShl { dst, left, right }
            }
            Self::U32WrappingShr { dst, left, right } => {
                crate::MirInstruction::U32WrappingShr { dst, left, right }
            }
            Self::U32CheckedShl { dst, left, right } => {
                crate::MirInstruction::U32CheckedShl { dst, left, right }
            }
            Self::U32CheckedShr { dst, left, right } => {
                crate::MirInstruction::U32CheckedShr { dst, left, right }
            }
            Self::U32Eq { dst, left, right } => crate::MirInstruction::U32Eq { dst, left, right },
            Self::U32Lt { dst, left, right } => crate::MirInstruction::U32Lt { dst, left, right },
            Self::U32Le { dst, left, right } => crate::MirInstruction::U32Le { dst, left, right },
            Self::U32ToUsize { dst, value } => crate::MirInstruction::U32ToUsize { dst, value },
            Self::UsizeToU32Checked { dst, value } => {
                crate::MirInstruction::UsizeToU32Checked { dst, value }
            }
            Self::I64ToU32Checked { dst, value } => {
                crate::MirInstruction::I64ToU32Checked { dst, value }
            }
            Self::I64ToU32Wrapping { dst, value } => {
                crate::MirInstruction::I64ToU32Wrapping { dst, value }
            }
            Self::I64ToUsizeChecked { dst, value } => {
                crate::MirInstruction::I64ToUsizeChecked { dst, value }
            }
            Self::I64ToUsizeWrapping { dst, value } => {
                crate::MirInstruction::I64ToUsizeWrapping { dst, value }
            }
            Self::I64ToU8Checked { dst, value } => {
                crate::MirInstruction::I64ToU8Checked { dst, value }
            }
            Self::I64ToU8Wrapping { dst, value } => {
                crate::MirInstruction::I64ToU8Wrapping { dst, value }
            }
            Self::I64ToU16Checked { dst, value } => {
                crate::MirInstruction::I64ToU16Checked { dst, value }
            }
            Self::I64ToU16Wrapping { dst, value } => {
                crate::MirInstruction::I64ToU16Wrapping { dst, value }
            }
            Self::I64ToI16Checked { dst, value } => {
                crate::MirInstruction::I64ToI16Checked { dst, value }
            }
            Self::I64ToI16Wrapping { dst, value } => {
                crate::MirInstruction::I64ToI16Wrapping { dst, value }
            }
            Self::I64ToI32Checked { dst, value } => {
                crate::MirInstruction::I64ToI32Checked { dst, value }
            }
            Self::I64ToI32Wrapping { dst, value } => {
                crate::MirInstruction::I64ToI32Wrapping { dst, value }
            }
            Self::I64ToI8Checked { dst, value } => {
                crate::MirInstruction::I64ToI8Checked { dst, value }
            }
            Self::I64ToI8Wrapping { dst, value } => {
                crate::MirInstruction::I64ToI8Wrapping { dst, value }
            }
            Self::I64ToU64Checked { dst, value } => {
                crate::MirInstruction::I64ToU64Checked { dst, value }
            }
            Self::I64ToU64Wrapping { dst, value } => {
                crate::MirInstruction::I64ToU64Wrapping { dst, value }
            }
            Self::I64ToIsizeChecked { dst, value } => {
                crate::MirInstruction::I64ToIsizeChecked { dst, value }
            }
            Self::I64ToIsizeWrapping { dst, value } => {
                crate::MirInstruction::I64ToIsizeWrapping { dst, value }
            }
            Self::I64ToU128Checked { dst, value } => {
                crate::MirInstruction::I64ToU128Checked { dst, value }
            }
            Self::I64ToU128Wrapping { dst, value } => {
                crate::MirInstruction::I64ToU128Wrapping { dst, value }
            }
            Self::I64ToI128Checked { dst, value } => {
                crate::MirInstruction::I64ToI128Checked { dst, value }
            }
            Self::I64ToI128Wrapping { dst, value } => {
                crate::MirInstruction::I64ToI128Wrapping { dst, value }
            }
            Self::MakeTuple { dst, fields } => crate::MirInstruction::MakeTuple { dst, fields },
            Self::MakeArray {
                dst,
                fields,
                element_type,
            } => crate::MirInstruction::MakeArray {
                dst,
                fields,
                element_type,
            },
            Self::MakeRecord {
                dst,
                definition,
                fields,
                field_types,
            } => crate::MirInstruction::MakeRecord {
                dst,
                definition,
                fields,
                field_types,
            },
            Self::MakeEnum {
                dst,
                definition,
                variant,
                fields,
                field_types,
            } => crate::MirInstruction::MakeEnum {
                dst,
                definition,
                variant,
                fields,
                field_types,
            },
            Self::ProjectRecord {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => crate::MirInstruction::ProjectRecord {
                dst,
                base,
                index,
                field_count,
                field_type,
            },
            Self::TakeProjection { dst, base, fields } => {
                crate::MirInstruction::TakeProjection { dst, base, fields }
            }
            Self::IsInitialized { dst, base, fields } => {
                crate::MirInstruction::IsInitialized { dst, base, fields }
            }
            Self::DestroyCallable { dst, value } => {
                crate::MirInstruction::DestroyCallable { dst, value }
            }
            Self::ProjectTuple {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => crate::MirInstruction::ProjectTuple {
                dst,
                base,
                index,
                field_count,
                field_type,
            },
            Self::ProjectArray {
                dst,
                base,
                index,
                field_count,
                element_type,
            } => crate::MirInstruction::ProjectArray {
                dst,
                base,
                index,
                field_count,
                element_type,
            },
            Self::UpdateRecord {
                dst,
                base,
                index,
                field_count,
                value,
                field_type,
            } => crate::MirInstruction::UpdateRecord {
                dst,
                base,
                index,
                field_count,
                value,
                field_type,
            },
            Self::PatternTest {
                dst,
                subject,
                pattern,
            } => crate::MirInstruction::PatternTest {
                dst,
                subject,
                pattern,
            },
            Self::Perform {
                site,
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            } => crate::MirInstruction::Perform {
                site,
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            },
            Self::InstallHandler {
                site,
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                resume_type,
                continuation,
                target,
                ..
            } => crate::MirInstruction::InstallHandler {
                site,
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                resume_type,
                continuation,
                target,
            },
            Self::ClaimEffectPayloads { payloads } => crate::MirInstruction::ClaimEffectPayloads { payloads },
            Self::UninstallHandler => crate::MirInstruction::UninstallHandler,
            Self::CompleteHandler { value } => crate::MirInstruction::CompleteHandler { value },
            Self::CaptureResumption { site, dst } => {
                crate::MirInstruction::CaptureResumption { site, dst }
            }
            Self::Resume { site, value } => crate::MirInstruction::Resume { site, value },
            Self::ResumeReturn { site, dst, value } => {
                crate::MirInstruction::ResumeReturn { site, dst, value }
            }
            Self::ResumeSnapshot {
                site,
                snapshot,
                value,
            } => crate::MirInstruction::ResumeSnapshot {
                site,
                snapshot,
                value,
            },
            Self::Forward { site } => crate::MirInstruction::Forward { site },
            Self::Cancel { site } => crate::MirInstruction::Cancel { site },
            Self::StorageLive { binding, local } => {
                crate::MirInstruction::StorageLive { binding, local }
            }
            Self::StorageDead { binding, local } => {
                crate::MirInstruction::StorageDead { binding, local }
            }
            Self::SetDropFlag { flag, value } => crate::MirInstruction::SetDropFlag { flag, value },
            Self::DestroyIf { local, flag } => crate::MirInstruction::DestroyIf { local, flag },
            Self::Copy { dst, src } => crate::MirInstruction::Copy { dst, src },
            Self::Store { dst, src } => crate::MirInstruction::Store { dst, src },
            Self::Move { dst, src } => crate::MirInstruction::Move { dst, src },
            Self::Borrow {
                dst,
                src,
                fields,
                unique,
                reborrow,
            } => crate::MirInstruction::Borrow {
                dst,
                src,
                fields,
                unique,
                reborrow,
            },
            Self::DerefCopy { dst, reference } => {
                crate::MirInstruction::DerefCopy { dst, reference }
            }
            Self::DerefMove { dst, reference } => {
                crate::MirInstruction::DerefMove { dst, reference }
            }
            Self::DerefIsInitialized { dst, reference } => {
                crate::MirInstruction::DerefIsInitialized { dst, reference }
            }
            Self::DerefStore { reference, src } => {
                crate::MirInstruction::DerefStore { reference, src }
            }
            Self::NotBool { dst, value } => crate::MirInstruction::NotBool { dst, value },
            Self::AddI64 { dst, left, right } => crate::MirInstruction::AddI64 { dst, left, right },
            Self::WrappingAddI64 { dst, left, right } => {
                crate::MirInstruction::WrappingAddI64 { dst, left, right }
            }
            Self::WrappingSubI64 { dst, left, right } => {
                crate::MirInstruction::WrappingSubI64 { dst, left, right }
            }
            Self::WrappingMulI64 { dst, left, right } => {
                crate::MirInstruction::WrappingMulI64 { dst, left, right }
            }
            Self::IntEqualI64 { dst, left, right } => {
                crate::MirInstruction::IntEqualI64 { dst, left, right }
            }
            Self::IntLessI64 { dst, left, right } => {
                crate::MirInstruction::IntLessI64 { dst, left, right }
            }
            Self::IntGreaterI64 { dst, left, right } => {
                crate::MirInstruction::IntGreaterI64 { dst, left, right }
            }
            Self::BitAndI64 { dst, left, right } => {
                crate::MirInstruction::BitAndI64 { dst, left, right }
            }
            Self::BitAndU32 { dst, left, right } => {
                crate::MirInstruction::BitAndU32 { dst, left, right }
            }
            Self::BitAndU64 { dst, left, right } => {
                crate::MirInstruction::BitAndU64 { dst, left, right }
            }
            Self::BitXorI64 { dst, left, right } => {
                crate::MirInstruction::BitXorI64 { dst, left, right }
            }
            Self::IntShrI64 { dst, left, right } => {
                crate::MirInstruction::IntShrI64 { dst, left, right }
            }
            Self::BitOrI64 { dst, left, right } => {
                crate::MirInstruction::BitOrI64 { dst, left, right }
            }
            Self::BitNotI64 { dst, value } => crate::MirInstruction::BitNotI64 { dst, value },
            Self::ShlI64 { dst, value, count } => {
                crate::MirInstruction::ShlI64 { dst, value, count }
            }
            Self::SubI64 { dst, left, right } => crate::MirInstruction::SubI64 { dst, left, right },
            Self::MulI64 { dst, left, right } => crate::MirInstruction::MulI64 { dst, left, right },
            Self::DivI64 { dst, left, right } => crate::MirInstruction::DivI64 { dst, left, right },
            Self::RemI64 { dst, left, right } => crate::MirInstruction::RemI64 { dst, left, right },
            Self::AddF64 { dst, left, right } => crate::MirInstruction::AddF64 { dst, left, right },
            Self::ConcatText { dst, left, right } => {
                crate::MirInstruction::ConcatText { dst, left, right }
            }
            Self::SubF64 { dst, left, right } => crate::MirInstruction::SubF64 { dst, left, right },
            Self::MulF64 { dst, left, right } => crate::MirInstruction::MulF64 { dst, left, right },
            Self::DivF64 { dst, left, right } => crate::MirInstruction::DivF64 { dst, left, right },
            Self::RemF64 { dst, left, right } => crate::MirInstruction::RemF64 { dst, left, right },
            Self::EqI64 { dst, left, right } => crate::MirInstruction::EqI64 { dst, left, right },
            Self::NeI64 { dst, left, right } => crate::MirInstruction::NeI64 { dst, left, right },
            Self::NeU32 { dst, left, right } => crate::MirInstruction::NeU32 { dst, left, right },
            Self::NeU64 { dst, left, right } => crate::MirInstruction::NeU64 { dst, left, right },
            Self::LtI64 { dst, left, right } => crate::MirInstruction::LtI64 { dst, left, right },
            Self::LeI64 { dst, left, right } => crate::MirInstruction::LeI64 { dst, left, right },
            Self::GtI64 { dst, left, right } => crate::MirInstruction::GtI64 { dst, left, right },
            Self::GeI64 { dst, left, right } => crate::MirInstruction::GeI64 { dst, left, right },
            Self::EqF64 { dst, left, right } => crate::MirInstruction::EqF64 { dst, left, right },
            Self::NeF64 { dst, left, right } => crate::MirInstruction::NeF64 { dst, left, right },
            Self::LtF64 { dst, left, right } => crate::MirInstruction::LtF64 { dst, left, right },
            Self::LeF64 { dst, left, right } => crate::MirInstruction::LeF64 { dst, left, right },
            Self::GtF64 { dst, left, right } => crate::MirInstruction::GtF64 { dst, left, right },
            Self::GeF64 { dst, left, right } => crate::MirInstruction::GeF64 { dst, left, right },
            Self::EqBool { dst, left, right } => crate::MirInstruction::EqBool { dst, left, right },
            Self::NeBool { dst, left, right } => crate::MirInstruction::NeBool { dst, left, right },
            Self::EqText { dst, left, right } => crate::MirInstruction::EqText { dst, left, right },
            Self::NeText { dst, left, right } => crate::MirInstruction::NeText { dst, left, right },
            Self::EqChar { dst, left, right } => crate::MirInstruction::EqChar { dst, left, right },
            Self::NeChar { dst, left, right } => crate::MirInstruction::NeChar { dst, left, right },
            Self::LtChar { dst, left, right } => crate::MirInstruction::LtChar { dst, left, right },
            Self::LeChar { dst, left, right } => crate::MirInstruction::LeChar { dst, left, right },
            Self::GtChar { dst, left, right } => crate::MirInstruction::GtChar { dst, left, right },
            Self::GeChar { dst, left, right } => crate::MirInstruction::GeChar { dst, left, right },
            Self::Call {
                dst,
                callee,
                arguments,
            } => crate::MirInstruction::CallOwned {
                dst,
                callee,
                arguments,
            },
            Self::HostCall {
                dst,
                capability,
                symbol,
                source_contract,
                parameters,
                result,
                resident_operations,
                arguments,
            } => crate::MirInstruction::HostCallOwned {
                dst,
                capability,
                symbol,
                source_contract,
                parameters,
                result,
                resident_operations,
                arguments,
            },
            Self::Abort => crate::MirInstruction::Abort,
            Self::MakeCallable {
                dst,
                callee,
                captures,
                environment,
            } => crate::MirInstruction::MakeCallable {
                dst,
                callee,
                captures,
                environment,
                generic_arguments: vec![],
                trait_instance: None,
            },
            Self::MakeLabel {
                label,
                dst,
                brand,
                target,
                destination,
            } => crate::MirInstruction::MakeLabel {
                label,
                dst,
                brand,
                target,
                destination,
            },
            Self::CallIndirect {
                dst,
                callee,
                arguments,
            } => crate::MirInstruction::CallIndirectOwned {
                dst,
                callee,
                arguments,
            },
        }
    }
}
