//! The small, stable LLVM-facing portion of the generation-1 native ABI.
//!
//! Both source-MIR emission and verified-artifact emission are producers of
//! LLVM modules.  Keeping the declarations which cross that module boundary
//! here prevents a new artifact lowering slice from accidentally inventing a
//! second spelling or pointer-width convention for the bundled C runtime.
//! This module deliberately describes declarations only; it is not a runtime
//! implementation and does not make an instruction natively supported.

/// Target pointer width used by the G1 C/LLVM ABI for `size_t`, `usize`, and
/// `isize`.  Keep this in one place because it is part of every native runtime
/// declaration, not a source-backend implementation detail.
pub(crate) fn pointer_width_for_target(target_triple: &str) -> u16 {
    if target_triple.starts_with("i386")
        || target_triple.starts_with("i486")
        || target_triple.starts_with("i586")
        || target_triple.starts_with("i686")
        || target_triple.starts_with("armv7")
        || target_triple.starts_with("thumbv7")
        || target_triple.starts_with("wasm32")
    {
        32
    } else {
        64
    }
}

/// The sole language-runtime fault entry point supplied by `native_runtime.c`.
///
/// This string is intentionally shared by all LLVM producers.  Declaring it
/// does not grant a lowering permission: a producer must still explicitly
/// emit and test each runtime-using opcode.
pub(crate) fn runtime_fault_declaration(pointer_width: u16) -> String {
    format!("declare void @g1_runtime_fault(i32, i32, i32, ptr, i{pointer_width}) cold noreturn")
}

#[cfg(test)]
mod tests {
    use super::{pointer_width_for_target, runtime_fault_declaration};

    #[test]
    fn runtime_fault_declaration_tracks_target_size_t_width() {
        assert_eq!(pointer_width_for_target("i686-unknown-linux-gnu"), 32);
        assert_eq!(pointer_width_for_target("x86_64-unknown-linux-gnu"), 64);
        assert_eq!(
            runtime_fault_declaration(32),
            "declare void @g1_runtime_fault(i32, i32, i32, ptr, i32) cold noreturn"
        );
        assert_eq!(
            runtime_fault_declaration(64),
            "declare void @g1_runtime_fault(i32, i32, i32, ptr, i64) cold noreturn"
        );
    }
}
