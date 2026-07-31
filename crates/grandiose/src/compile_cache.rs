//! Persistent per-thread compilation state for the public batch API.
//!
//! Editors and servers already reuse [`CompilationDriver`] explicitly, but
//! ordinary batch callers historically rebuilt all frontend, type, MIR, and
//! exact-result caches for every call. Test harnesses are especially prone to
//! that pattern. Keep one driver per worker thread so independent callers reuse
//! unchanged standard-library segments, body inference, MIR lowering, and the
//! driver's bounded exact phase cache without serializing compilation globally.

use std::cell::RefCell;

use crate::{
    compiler::{CompileOptions, CompiledPhases},
    compiler_session::CompilationDriver,
    diagnostic::Diagnostic,
    source_bundle::SourceBundle,
};

thread_local! {
    static BATCH_DRIVER: RefCell<CompilationDriver> =
        RefCell::new(CompilationDriver::new());
}

pub(crate) fn compile_bundle_to_phases_with_options(
    bundle: &SourceBundle,
    options: CompileOptions,
) -> Result<CompiledPhases, Vec<Diagnostic>> {
    BATCH_DRIVER.with(|driver| {
        driver.borrow_mut().compile_bundle(bundle, options)
    })
}
