use super::*;

pub(crate) fn emit_operation(
    operation: &RuntimeOperation,
    transfer: Option<&RuntimeTransfer>,
) -> MirInstruction {
    let mut instruction = operation.to_backend();
    let Some(transfer) = transfer else {
        return instruction;
    };
    let arguments = transfer
        .arguments
        .iter()
        .map(|argument| argument.local)
        .collect::<Vec<_>>();
    // These operands come from the independently checked ABI contract. The
    // opcode contributes only its fixed machine leaf / protocol identity.
    match &mut instruction {
        MirInstruction::CallOwned {
            dst,
            arguments: operands,
            ..
        }
        | MirInstruction::HostCallOwned {
            dst,
            arguments: operands,
            ..
        }
        | MirInstruction::Perform {
            dst,
            arguments: operands,
            ..
        } => {
            *dst = transfer.result.expect("checked returning transfer ABI");
            *operands = arguments;
        }
        MirInstruction::CallIndirectOwned {
            dst,
            callee,
            arguments: operands,
        } => {
            *dst = transfer.result.expect("checked indirect transfer ABI");
            *callee = arguments[0];
            *operands = arguments[1..].to_vec();
        }
        MirInstruction::CaptureResumption { dst, .. } => {
            *dst = transfer.result.expect("checked capture ABI")
        }
        MirInstruction::ResumeReturn { dst, value, .. } => {
            *dst = transfer.result.expect("checked returning resumption ABI");
            *value = arguments[0];
        }
        MirInstruction::Resume { value, .. } | MirInstruction::CompleteHandler { value } => {
            *value = arguments[0]
        }
        MirInstruction::ResumeSnapshot {
            snapshot, value, ..
        } => {
            *snapshot = arguments[0];
            *value = arguments[1];
        }
        _ => {}
    }
    instruction
}
