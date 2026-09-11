//! Canonical instruction and embedded cleanup/pattern encodings.

use super::super::{
    VmCleanupProof, VmCompare, VmContinuationPolicy, VmInstruction, VmPattern, VmPatternField,
    VmStorageErasureAction, VmStorageErasureWitness,
};
use super::{
    encode_capture_environment, encode_integer_scalar, encode_type, encode_vm_generic_arguments,
};

pub(super) fn encode_instruction(value: &VmInstruction, output: &mut Vec<u8>) {
    match value {
        VmInstruction::TailCallOwned { callee, arguments } => {
            output.push(211);
            output.extend_from_slice(&callee.0.as_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments { output.extend_from_slice(&argument.to_le_bytes()); }
        }
        VmInstruction::DeclareFrameCleanup { actions } => {
            output.push(200);
            output.extend_from_slice(&(actions.len() as u64).to_le_bytes());
            for action in actions {
                output.extend_from_slice(&action.owner.to_le_bytes());
                output.extend_from_slice(&action.destructor.0.as_bytes());
            }
        }
        VmInstruction::DeclareResult { result, returns } => {
            output.push(172);
            encode_type(result, output);
            output.push(u8::from(*returns));
        }
        VmInstruction::ConstUnit { dst } => {
            output.push(28);
            output.extend_from_slice(&dst.to_le_bytes());
        }
        VmInstruction::ConstI64 { dst, value } => {
            output.push(0);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstU8 { dst, value } => {
            output.push(157);
            output.extend_from_slice(&dst.to_le_bytes());
            output.push(*value)
        }
        VmInstruction::ConstU16 { dst, value } => {
            output.push(158);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstU32 { dst, value } => {
            output.push(151);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstU64 { dst, value } => {
            output.push(152);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstUsize { dst, value } => {
            output.push(159);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstU128 { dst, value } => {
            output.push(160);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstI8 { dst, value } => {
            output.push(161);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstI16 { dst, value } => {
            output.push(162);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstI32 { dst, value } => {
            output.push(163);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstIsize { dst, value } => {
            output.push(164);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstI128 { dst, value } => {
            output.push(165);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstF64 { dst, bits } => {
            output.push(7);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&bits.to_le_bytes())
        }
        VmInstruction::ConstF32 { dst, bits } => {
            output.push(171);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&bits.to_le_bytes())
        }
        VmInstruction::MemoryIntrinsic {
            dst,
            primitive,
            types,
            arguments,
        } => {
            output.push(194);
            output.extend_from_slice(&dst.to_le_bytes());
            output.push(primitive.ordinal());
            output.extend_from_slice(&(types.len() as u64).to_le_bytes());
            for ty in types {
                encode_type(ty, output);
            }
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::TakeProjection { dst, base, fields }
        | VmInstruction::IsInitialized { dst, base, fields } => {
            output.push(if matches!(value, VmInstruction::TakeProjection { .. }) {
                195
            } else {
                196
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&base.to_le_bytes());
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields {
                output.extend_from_slice(&field.to_le_bytes());
            }
        }
        VmInstruction::DerefIsInitialized { dst, reference } => {
            output.push(197);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&reference.to_le_bytes());
        }
        VmInstruction::FloatIntrinsic {
            dst,
            primitive,
            arguments,
        } => {
            output.push(138);
            output.extend_from_slice(&dst.to_le_bytes());
            let selector = primitive.selector_name();
            output.extend_from_slice(&(selector.len() as u64).to_le_bytes());
            output.extend_from_slice(selector.as_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::IntIntrinsic {
            dst,
            primitive,
            scalar,
            arguments,
        } => {
            output.push(166);
            output.extend_from_slice(&dst.to_le_bytes());
            let selector = primitive.selector_name();
            output.extend_from_slice(&(selector.len() as u64).to_le_bytes());
            output.extend_from_slice(selector.as_bytes());
            output.push(
                encode_integer_scalar(*scalar)
                    .expect("integer intrinsic has a runtime integer scalar"),
            );
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::ConstBool { dst, value } => {
            output.push(16);
            output.extend_from_slice(&dst.to_le_bytes());
            output.push(u8::from(*value));
        }
        VmInstruction::ConstChar { dst, value } => {
            output.push(20);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ConstText { dst, value } => {
            output.push(24);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&(value.len() as u64).to_le_bytes());
            output.extend_from_slice(value.as_bytes());
        }
        VmInstruction::ConstStaticData {
            dst,
            tag,
            alignment,
            bytes,
        } => {
            output.push(175);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&tag.to_le_bytes());
            output.extend_from_slice(&alignment.to_le_bytes());
            output.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
            output.extend_from_slice(bytes);
        }
        VmInstruction::StaticLen { dst, value } => {
            output.push(176);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::MakeTupleOwned { dst, fields } | VmInstruction::MakeTuple { dst, fields } => {
            output.push(if matches!(value, VmInstruction::MakeTupleOwned { .. }) { 213 } else { 33 });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields {
                output.extend_from_slice(&field.to_le_bytes());
            }
        }
        VmInstruction::MakeArrayOwned { dst, fields, element_type } | VmInstruction::MakeArray {
            dst,
            fields,
            element_type,
        } => {
            output.push(if matches!(value, VmInstruction::MakeArrayOwned { .. }) { 214 } else { 37 });
            output.extend_from_slice(&dst.to_le_bytes());
            encode_type(element_type, output);
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields {
                output.extend_from_slice(&field.to_le_bytes());
            }
        }
        VmInstruction::MakeRecordOwned { dst, definition, fields, field_types } | VmInstruction::MakeRecord {
            dst,
            definition,
            fields,
            field_types,
        } => {
            output.push(if matches!(value, VmInstruction::MakeRecordOwned { .. }) { 215 } else { 34 });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for (field, field_type) in fields.iter().zip(field_types) {
                output.extend_from_slice(&field.to_le_bytes());
                encode_type(field_type, output);
            }
        }
        VmInstruction::ProjectRecord {
            dst,
            base,
            index,
            field_count,
            field_type,
        } => {
            output.push(35);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&base.to_le_bytes());
            output.extend_from_slice(&index.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            encode_type(field_type, output);
        }
        VmInstruction::ProjectTuple {
            dst,
            base,
            index,
            field_count,
            field_type,
        } => {
            output.push(42);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&base.to_le_bytes());
            output.extend_from_slice(&index.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            encode_type(field_type, output);
        }
        VmInstruction::ProjectArray {
            dst,
            base,
            index,
            field_count,
            element_type,
        } => {
            output.push(57);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&base.to_le_bytes());
            output.extend_from_slice(&index.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::UpdateRecord {
            dst,
            base,
            index,
            field_count,
            value,
            field_type,
        } => {
            output.push(39);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&base.to_le_bytes());
            output.extend_from_slice(&index.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
            encode_type(field_type, output);
        }
        VmInstruction::PatternTest {
            dst,
            subject,
            pattern,
        } => {
            output.push(40);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&subject.to_le_bytes());
            encode_pattern(pattern, output);
        }
        VmInstruction::PerformOwned {
            dst,
            effect,
            effect_arguments,
            operation,
            arguments,
        }
        | VmInstruction::Perform {
            dst,
            effect,
            effect_arguments,
            operation,
            arguments,
        } => {
            output.push(if matches!(value, VmInstruction::PerformOwned { .. }) {
                208
            } else {
                41
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&effect.0.as_bytes());
            encode_vm_generic_arguments(effect_arguments, output);
            output.extend_from_slice(&operation.to_le_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::InstallHandlerOwned {
            effect,
            effect_arguments,
            operation,
            payload_destinations,
            resume_type,
            continuation,
            target,
            ..
        }
        | VmInstruction::InstallHandler {
            effect,
            effect_arguments,
            operation,
            payload_destinations,
            resume_type,
            continuation,
            target,
        } => {
            output.push(
                if matches!(value, VmInstruction::InstallHandlerOwned { .. }) {
                    209
                } else {
                    44
                },
            );
            output.extend_from_slice(&effect.0.as_bytes());
            encode_vm_generic_arguments(effect_arguments, output);
            output.extend_from_slice(&operation.to_le_bytes());
            output.extend_from_slice(&(payload_destinations.len() as u64).to_le_bytes());
            for destination in payload_destinations {
                output.extend_from_slice(&destination.to_le_bytes());
            }
            encode_type(resume_type, output);
            match continuation {
                VmContinuationPolicy::Consume => output.push(0),
                VmContinuationPolicy::Replay { uses } => {
                    output.push(1);
                    output.extend_from_slice(&uses.to_le_bytes());
                }
                VmContinuationPolicy::Terminal => output.push(2),
                VmContinuationPolicy::Optional => output.push(3),
            }
            output.extend_from_slice(&target.to_le_bytes());
            if let VmInstruction::InstallHandlerOwned { continuation_owned, clause_owned, .. } = value {
                for roots in [continuation_owned, clause_owned] {
                    output.extend_from_slice(&(roots.len() as u64).to_le_bytes());
                    for root in roots {
                        output.extend_from_slice(&root.to_le_bytes());
                    }
                }
            }
        }
        VmInstruction::ClaimEffectPayloads { payloads } => {
            output.push(210);
            output.extend_from_slice(&(payloads.len() as u64).to_le_bytes());
            for value in payloads {
                output.extend_from_slice(&value.to_le_bytes());
            }
        }
        VmInstruction::UninstallHandler => output.push(45),
        VmInstruction::CompleteHandler { value } => {
            output.push(198);
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::Resume { value } => {
            output.push(46);
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ResumeReturn { dst, value } => {
            output.push(51);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::Forward => output.push(47),
        VmInstruction::Cancel => output.push(69),
        VmInstruction::CaptureResumption { dst } => {
            output.push(70);
            output.extend_from_slice(&dst.to_le_bytes());
        }
        VmInstruction::ResumeSnapshot { snapshot, value } => {
            output.push(50);
            output.extend_from_slice(&snapshot.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::Leave {
            brand_owner,
            brand_label,
            retained_handlers,
            exited_handlers,
            target,
            arguments,
            destinations,
            cleanup,
        } => {
            output.push(55);
            output.extend_from_slice(&brand_owner.0.as_bytes());
            output.extend_from_slice(&brand_label.to_le_bytes());
            for handlers in [retained_handlers, exited_handlers] {
                output.extend_from_slice(&(handlers.len() as u64).to_le_bytes());
                for handler in handlers { output.extend_from_slice(&handler.to_le_bytes()); }
            }
            output.extend_from_slice(&target.to_le_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
            output.extend_from_slice(&(destinations.len() as u64).to_le_bytes());
            for destination in destinations {
                output.extend_from_slice(&destination.to_le_bytes());
            }
            encode_cleanup_proof(cleanup, output);
        }
        VmInstruction::MakeEnumOwned { dst, definition, variant, fields, field_types } | VmInstruction::MakeEnum {
            dst,
            definition,
            variant,
            fields,
            field_types,
        } => {
            output.push(if matches!(value, VmInstruction::MakeEnumOwned { .. }) { 216 } else { 36 });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&variant.to_le_bytes());
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for (field, field_type) in fields.iter().zip(field_types) {
                output.extend_from_slice(&field.to_le_bytes());
                encode_type(field_type, output);
            }
        }
        VmInstruction::StorageLive { binding, local } => {
            output.push(167);
            output.extend_from_slice(&binding.to_le_bytes());
            output.extend_from_slice(&local.to_le_bytes());
        }
        VmInstruction::StorageDead { binding, local } => {
            output.push(168);
            output.extend_from_slice(&binding.to_le_bytes());
            output.extend_from_slice(&local.to_le_bytes());
        }
        VmInstruction::SetDropFlag { flag, value } => {
            output.push(169);
            output.extend_from_slice(&flag.to_le_bytes());
            output.push(*value as u8);
        }
        VmInstruction::DestroyIf { local, flag } => {
            output.push(170);
            output.extend_from_slice(&local.to_le_bytes());
            output.extend_from_slice(&flag.to_le_bytes());
        }
        VmInstruction::Copy { dst, src }
        | VmInstruction::Store { dst, src } | VmInstruction::StoreOwned { dst, src }
        | VmInstruction::Move { dst, src } => {
            output.push(match value {
                VmInstruction::Copy { .. } => 1,
                VmInstruction::Move { .. } => 2,
                VmInstruction::Store { .. } => 38,
                VmInstruction::StoreOwned { .. } => 212,
                _ => unreachable!("instruction family matched above"),
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&src.to_le_bytes())
        }
        VmInstruction::Borrow {
            dst,
            src,
            fields,
            unique,
            reborrow,
        } => {
            output.push(52);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&src.to_le_bytes());
            output.push(*unique as u8);
            output.push(*reborrow as u8);
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields {
                output.extend_from_slice(&field.to_le_bytes());
            }
        }
        VmInstruction::DerefCopy { dst, reference } => {
            output.push(53);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&reference.to_le_bytes());
        }
        VmInstruction::DerefMove { dst, reference } => {
            output.push(174);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&reference.to_le_bytes());
        }
        VmInstruction::DerefStore { reference, src } => {
            output.push(54);
            output.extend_from_slice(&reference.to_le_bytes());
            output.extend_from_slice(&src.to_le_bytes());
        }
        VmInstruction::NotBool { dst, value } => {
            output.push(19);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::BitNotI64 { dst, value } => {
            output.push(113);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ShlI64 { dst, value, count } => {
            output.push(114);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
            output.extend_from_slice(&count.to_le_bytes());
        }
        VmInstruction::EqBool { dst, left, right } | VmInstruction::NeBool { dst, left, right } => {
            output.push(if matches!(value, VmInstruction::EqBool { .. }) {
                21
            } else {
                22
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&left.to_le_bytes());
            output.extend_from_slice(&right.to_le_bytes());
        }
        VmInstruction::EqText { dst, left, right } | VmInstruction::NeText { dst, left, right } => {
            output.push(if matches!(value, VmInstruction::EqText { .. }) {
                25
            } else {
                26
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&left.to_le_bytes());
            output.extend_from_slice(&right.to_le_bytes());
        }
        VmInstruction::AddI64 { dst, left, right }
        | VmInstruction::WrappingAddI64 { dst, left, right }
        | VmInstruction::WrappingSubI64 { dst, left, right }
        | VmInstruction::WrappingMulI64 { dst, left, right }
        | VmInstruction::IntEqualI64 { dst, left, right }
        | VmInstruction::IntLessI64 { dst, left, right }
        | VmInstruction::IntGreaterI64 { dst, left, right }
        | VmInstruction::BitAndI64 { dst, left, right }
        | VmInstruction::BitXorI64 { dst, left, right }
        | VmInstruction::BitOrI64 { dst, left, right }
        | VmInstruction::IntShrI64 { dst, left, right }
        | VmInstruction::SubI64 { dst, left, right }
        | VmInstruction::MulI64 { dst, left, right }
        | VmInstruction::DivI64 { dst, left, right }
        | VmInstruction::RemI64 { dst, left, right }
        | VmInstruction::AddF64 { dst, left, right }
        | VmInstruction::SubF64 { dst, left, right }
        | VmInstruction::MulF64 { dst, left, right }
        | VmInstruction::DivF64 { dst, left, right }
        | VmInstruction::RemF64 { dst, left, right } => {
            output.push(match value {
                VmInstruction::AddI64 { .. } => 3,
                VmInstruction::WrappingAddI64 { .. } => 104,
                VmInstruction::WrappingSubI64 { .. } => 106,
                VmInstruction::WrappingMulI64 { .. } => 107,
                VmInstruction::IntEqualI64 { .. } => 105,
                VmInstruction::IntLessI64 { .. } => 109,
                VmInstruction::IntGreaterI64 { .. } => 110,
                VmInstruction::BitAndI64 { .. } => 108,
                VmInstruction::BitXorI64 { .. } => 112,
                VmInstruction::BitOrI64 { .. } => 111,
                VmInstruction::IntShrI64 { .. } => 115,
                VmInstruction::SubI64 { .. } => 4,
                VmInstruction::MulI64 { .. } => 5,
                VmInstruction::DivI64 { .. } => 8,
                VmInstruction::RemI64 { .. } => 9,
                VmInstruction::AddF64 { .. } => 10,
                VmInstruction::SubF64 { .. } => 11,
                VmInstruction::MulF64 { .. } => 12,
                VmInstruction::DivF64 { .. } => 13,
                VmInstruction::RemF64 { .. } => 14,
                _ => unreachable!("matched arithmetic instruction"),
            });
            for r in [dst, left, right] {
                output.extend_from_slice(&r.to_le_bytes())
            }
        }
        VmInstruction::ConcatText { dst, left, right } => {
            output.push(27);
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::BitAndU32 { dst, left, right }
        | VmInstruction::BitAndU64 { dst, left, right } => {
            output.push(if matches!(value, VmInstruction::BitAndU32 { .. }) {
                153
            } else {
                154
            });
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::CompareI64 {
            dst,
            left,
            right,
            op,
        }
        | VmInstruction::CompareF64 {
            dst,
            left,
            right,
            op,
        }
        | VmInstruction::CompareChar {
            dst,
            left,
            right,
            op,
        } => {
            output.push(match value {
                VmInstruction::CompareI64 { .. } => 17,
                VmInstruction::CompareF64 { .. } => 18,
                VmInstruction::CompareChar { .. } => 23,
                _ => unreachable!("matched comparison instruction"),
            });
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            output.push(match op {
                VmCompare::Equal => 0,
                VmCompare::NotEqual => 1,
                VmCompare::Less => 2,
                VmCompare::LessEqual => 3,
                VmCompare::Greater => 4,
                VmCompare::GreaterEqual => 5,
            });
        }
        VmInstruction::CompareU32 {
            dst,
            left,
            right,
            op,
        }
        | VmInstruction::CompareU64 {
            dst,
            left,
            right,
            op,
        } => {
            output.push(if matches!(value, VmInstruction::CompareU32 { .. }) {
                155
            } else {
                156
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&left.to_le_bytes());
            output.extend_from_slice(&right.to_le_bytes());
            output.push(match op {
                VmCompare::Equal => 0,
                VmCompare::NotEqual => 1,
                VmCompare::Less => 2,
                VmCompare::LessEqual => 3,
                VmCompare::Greater => 4,
                VmCompare::GreaterEqual => 5,
            });
        }
        VmInstruction::CallOwned {
            dst,
            callee,
            arguments,
        }
        | VmInstruction::Call {
            dst,
            callee,
            arguments,
        } => {
            output.push(if matches!(value, VmInstruction::CallOwned { .. }) {
                205
            } else {
                6
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&callee.0.as_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::HostCallOwned {
            dst,
            capability,
            symbol,
            source_contract,
            parameters,
            result,
            resident_operations,
            arguments,
        }
        | VmInstruction::HostCall {
            dst,
            capability,
            symbol,
            source_contract,
            parameters,
            result,
            resident_operations,
            arguments,
        } => {
            output.push(if matches!(value, VmInstruction::HostCallOwned { .. }) {
                207
            } else {
                56
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&(capability.len() as u64).to_le_bytes());
            output.extend_from_slice(capability.as_bytes());
            output.extend_from_slice(&(symbol.len() as u64).to_le_bytes());
            output.extend_from_slice(symbol.as_bytes());
            output.extend_from_slice(&source_contract.as_bytes());
            output.extend_from_slice(&(parameters.len() as u64).to_le_bytes());
            for parameter in parameters {
                encode_type(parameter, output);
            }
            encode_type(result, output);
            output.extend_from_slice(&(resident_operations.len() as u64).to_le_bytes());
            for resident in resident_operations {
                encode_type(&resident.ty, output);
                output.extend_from_slice(&resident.source_type.as_bytes());
                output.push(u8::from(resident.destructor.is_some()));
                if let Some(destructor) = resident.destructor {
                    output.extend_from_slice(&destructor.0.as_bytes());
                }
            }
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::TextByteLen { dst, value } => {
            output.push(64);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::TextConcat { dst, left, right } => {
            output.push(65);
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::TextEq { dst, left, right } => {
            output.push(66);
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::TextFromUtf8Checked { dst, value } => {
            output.push(67);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::TextAsBytes { dst, value } => {
            output.push(68);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::CharFromU32Checked { dst, value } => {
            output.push(48);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::CharToU32 { dst, value } => {
            output.push(49);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::StoreUsize { dst, value } => {
            output.push(204);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ArrayLen { dst, value } => {
            output.push(201);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ArrayElementIsInitialized {
            dst,
            value: array,
            index,
        }
        | VmInstruction::TakeArrayElement {
            dst,
            value: array,
            index,
        } => {
            output.push(if matches!(value, VmInstruction::TakeArrayElement { .. }) {
                203
            } else {
                202
            });
            for register in [dst, array, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::BytesLen { dst, value } => {
            output.push(80);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::BytesUtf8ValidUpTo { dst, value } => {
            output.push(86);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::Blake3 { dst, value } => {
            output.push(173);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ArrayGetBorrowShared {
            dst,
            value,
            index,
            element_type,
        } => {
            output.push(143);
            for register in [dst, value, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArrayEmpty { dst, element_type } => {
            output.push(145);
            output.extend_from_slice(&dst.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayPushMove {
            value,
            item,
            element_type,
        } => {
            output.push(146);
            output.extend_from_slice(&value.to_le_bytes());
            output.extend_from_slice(&item.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::BytesConcat { dst, left, right } => {
            output.push(81);
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::BytesGet { dst, bytes, index } => {
            output.push(82);
            for register in [dst, bytes, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::BytesSlice {
            dst,
            bytes,
            start,
            end,
        } => {
            output.push(83);
            for register in [dst, bytes, start, end] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::BytesFromArrayMove { dst, value } => {
            output.push(84);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::BytesToArray { dst, value } => {
            output.push(85);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::U32CheckedAdd { dst, left, right }
        | VmInstruction::U32CheckedSub { dst, left, right }
        | VmInstruction::U32CheckedMul { dst, left, right }
        | VmInstruction::U32CheckedDiv { dst, left, right }
        | VmInstruction::U32CheckedRem { dst, left, right }
        | VmInstruction::U32WrappingAdd { dst, left, right }
        | VmInstruction::U32WrappingSub { dst, left, right }
        | VmInstruction::U32WrappingMul { dst, left, right }
        | VmInstruction::U32WrappingShl { dst, left, right }
        | VmInstruction::U32WrappingShr { dst, left, right }
        | VmInstruction::U32CheckedShl { dst, left, right }
        | VmInstruction::U32CheckedShr { dst, left, right }
        | VmInstruction::U32Eq { dst, left, right }
        | VmInstruction::U32Lt { dst, left, right }
        | VmInstruction::U32Le { dst, left, right } => {
            output.push(match value {
                VmInstruction::U32CheckedAdd { .. } => 87,
                VmInstruction::U32CheckedSub { .. } => 88,
                VmInstruction::U32CheckedMul { .. } => 89,
                VmInstruction::U32CheckedDiv { .. } => 90,
                VmInstruction::U32CheckedRem { .. } => 91,
                VmInstruction::U32WrappingAdd { .. } => 92,
                VmInstruction::U32WrappingSub { .. } => 93,
                VmInstruction::U32WrappingMul { .. } => 94,
                VmInstruction::U32WrappingShl { .. } => 95,
                VmInstruction::U32WrappingShr { .. } => 96,
                VmInstruction::U32CheckedShl { .. } => 97,
                VmInstruction::U32CheckedShr { .. } => 98,
                VmInstruction::U32Eq { .. } => 99,
                VmInstruction::U32Lt { .. } => 100,
                VmInstruction::U32Le { .. } => 101,
                _ => unreachable!("instruction family matched above"),
            });
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::U32ToUsize { dst, value } => {
            output.push(102);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::UsizeToU32Checked { dst, value } => {
            output.push(103);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU32Checked { dst, value } => {
            output.push(116);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU32Wrapping { dst, value } => {
            output.push(117);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToUsizeChecked { dst, value } => {
            output.push(118);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToUsizeWrapping { dst, value } => {
            output.push(119);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU8Checked { dst, value } => {
            output.push(120);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU8Wrapping { dst, value } => {
            output.push(121);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU16Checked { dst, value } => {
            output.push(122);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU16Wrapping { dst, value } => {
            output.push(123);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI16Checked { dst, value } => {
            output.push(124);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI16Wrapping { dst, value } => {
            output.push(125);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI32Checked { dst, value } => {
            output.push(126);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI32Wrapping { dst, value } => {
            output.push(127);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI8Checked { dst, value } => {
            output.push(128);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI8Wrapping { dst, value } => {
            output.push(129);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU64Checked { dst, value } => {
            output.push(130);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU64Wrapping { dst, value } => {
            output.push(131);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToIsizeChecked { dst, value } => {
            output.push(132);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToIsizeWrapping { dst, value } => {
            output.push(133);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU128Checked { dst, value } => {
            output.push(134);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU128Wrapping { dst, value } => {
            output.push(135);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI128Checked { dst, value } => {
            output.push(136);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI128Wrapping { dst, value } => {
            output.push(137);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::MakeCallable {
            dst,
            callee,
            captures,
            environment,
        } => {
            output.push(29);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&callee.0.as_bytes());
            output.extend_from_slice(&(captures.len() as u64).to_le_bytes());
            for capture in captures {
                output.extend_from_slice(&capture.to_le_bytes());
            }
            encode_capture_environment(environment.as_ref(), output);
        }
        VmInstruction::MakeLabel {
            dst,
            brand_owner,
            brand_label,
            target,
            destination,
        } => {
            output.push(71);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&brand_owner.0.as_bytes());
            output.extend_from_slice(&brand_label.to_le_bytes());
            output.extend_from_slice(&target.to_le_bytes());
            output.extend_from_slice(&destination.to_le_bytes());
        }
        VmInstruction::CallIndirectOwned {
            dst,
            callee,
            arguments,
        }
        | VmInstruction::CallPrepared { dst, callee, arguments }
        | VmInstruction::CallIndirect {
            dst,
            callee,
            arguments,
        } => {
            output.push(
                if matches!(value, VmInstruction::CallPrepared { .. }) { 219 }
                else if matches!(value, VmInstruction::CallIndirectOwned { .. }) {
                    206
                } else {
                    30
                },
            );
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&callee.to_le_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::Jump { target } => {
            output.push(31);
            output.extend_from_slice(&target.to_le_bytes());
        }
        VmInstruction::BranchBool {
            condition,
            then_target,
            else_target,
        } => {
            output.push(32);
            output.extend_from_slice(&condition.to_le_bytes());
            output.extend_from_slice(&then_target.to_le_bytes());
            output.extend_from_slice(&else_target.to_le_bytes());
        }
        VmInstruction::Return { value } => {
            output.push(15);
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::DestroyCallable { dst, value } => {
            output.push(199);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::RetainResumption { dst, src, fields } => {
            output.push(217);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&src.to_le_bytes());
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields { output.extend_from_slice(&field.to_le_bytes()); }
        }
        VmInstruction::PrepareInvocation { dst, src, fields, reborrow } => {
            output.push(218);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&src.to_le_bytes());
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields { output.extend_from_slice(&field.to_le_bytes()); }
            output.push(u8::from(*reborrow));
        }
        VmInstruction::Trap => output.push(43),
    }
}
fn encode_pattern(value: &VmPattern, output: &mut Vec<u8>) {
    match value {
        VmPattern::Any => output.push(0),
        VmPattern::Literal(value) => {
            output.push(1);
            output.extend_from_slice(&(value.len() as u64).to_le_bytes());
            output.extend_from_slice(value.as_bytes());
        }
        VmPattern::Tuple(values) => {
            output.push(2);
            output.extend_from_slice(&(values.len() as u64).to_le_bytes());
            for value in values {
                encode_pattern(value, output);
            }
        }
        VmPattern::Array { element, elements, rest } => {
            output.push(5);
            output.push(u8::from(rest.is_some()));
            if let Some(rest) = rest {
                output.extend_from_slice(&rest.prefix.to_le_bytes());
                output.extend_from_slice(&rest.omitted.to_le_bytes());
            }
            encode_type(element, output);
            output.extend_from_slice(&(elements.len() as u64).to_le_bytes());
            for value in elements {
                encode_pattern(value, output);
            }
        }
        VmPattern::Record {
            definition,
            field_types,
            field_count,
            fields,
        } => {
            output.push(3);
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            output.extend_from_slice(&(field_types.len() as u64).to_le_bytes());
            for field_type in field_types {
                encode_type(field_type, output);
            }
            encode_pattern_fields(fields, output);
        }
        VmPattern::Enum {
            definition,
            variant,
            field_types,
            field_count,
            fields,
        } => {
            output.push(4);
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&variant.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            output.extend_from_slice(&(field_types.len() as u64).to_le_bytes());
            for field_type in field_types {
                encode_type(field_type, output);
            }
            encode_pattern_fields(fields, output);
        }
    }
}
fn encode_cleanup_proof(value: &VmCleanupProof, output: &mut Vec<u8>) {
    output.extend_from_slice(&(value.moved_places.len() as u64).to_le_bytes());
    for place in &value.moved_places {
        output.extend_from_slice(&place.path.to_le_bytes());
        output.extend_from_slice(&place.binding.to_le_bytes());
        output.extend_from_slice(&(place.root.len() as u64).to_le_bytes());
        output.extend_from_slice(place.root.as_bytes());
        output.extend_from_slice(&(place.fields.len() as u64).to_le_bytes());
        for field in &place.fields {
            output.extend_from_slice(&field.to_le_bytes());
        }
    }
    output.extend_from_slice(&(value.active_loans.len() as u64).to_le_bytes());
    for loan in &value.active_loans {
        match &loan.owner {
            None => output.push(0),
            Some(owner) => {
                output.push(1);
                output.extend_from_slice(&(owner.len() as u64).to_le_bytes());
                output.extend_from_slice(owner.as_bytes());
            }
        }
        output.extend_from_slice(&loan.binding.to_le_bytes());
        output.extend_from_slice(&(loan.root.len() as u64).to_le_bytes());
        output.extend_from_slice(loan.root.as_bytes());
        output.extend_from_slice(&(loan.fields.len() as u64).to_le_bytes());
        for field in &loan.fields {
            output.extend_from_slice(&field.to_le_bytes());
        }
        output.push(u8::from(loan.unique));
    }
    encode_storage_erasure_witness(&value.storage_erasure, output);
}
fn encode_storage_erasure_witness(value: &VmStorageErasureWitness, output: &mut Vec<u8>) {
    match value {
        VmStorageErasureWitness::Missing => output.push(0),
        VmStorageErasureWitness::Verified {
            storages,
            actions,
            protected_registers,
        } => {
            output.push(1);
            output.extend_from_slice(&(storages.len() as u64).to_le_bytes());
            for storage in storages {
                output.extend_from_slice(&storage.storage.to_le_bytes());
                output.extend_from_slice(&storage.binding.to_le_bytes());
                output.extend_from_slice(&storage.value_register.to_le_bytes());
                output.push(u8::from(storage.initialized));
                match storage.drop_flag {
                    None => output.push(0),
                    Some(drop_flag) => {
                        output.push(1);
                        output.extend_from_slice(&drop_flag.to_le_bytes());
                    }
                }
            }
            output.extend_from_slice(&(actions.len() as u64).to_le_bytes());
            for action in actions {
                match action {
                    VmStorageErasureAction::EndBorrow { storage } => {
                        output.push(0);
                        output.extend_from_slice(&storage.to_le_bytes());
                    }
                    VmStorageErasureAction::Protect { storage, register } => {
                        output.push(1);
                        output.extend_from_slice(&storage.to_le_bytes());
                        output.extend_from_slice(&register.to_le_bytes());
                    }
                    VmStorageErasureAction::Destroy { storage } => {
                        output.push(2);
                        output.extend_from_slice(&storage.to_le_bytes());
                    }
                    VmStorageErasureAction::SetDropFlag {
                        drop_flag,
                        initialized,
                    } => {
                        output.push(3);
                        output.extend_from_slice(&drop_flag.to_le_bytes());
                        output.push(u8::from(*initialized));
                    }
                    VmStorageErasureAction::StorageDead { storage } => {
                        output.push(4);
                        output.extend_from_slice(&storage.to_le_bytes());
                    }
                }
            }
            output.extend_from_slice(&(protected_registers.len() as u64).to_le_bytes());
            for register in protected_registers {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
    }
}
fn encode_pattern_fields(fields: &[VmPatternField], output: &mut Vec<u8>) {
    output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
    for field in fields {
        output.extend_from_slice(&field.index.to_le_bytes());
        encode_type(&field.ty, output);
        encode_pattern(&field.pattern, output);
    }
}
