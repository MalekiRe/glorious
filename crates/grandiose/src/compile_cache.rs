//! Bounded exact-input memoization for the public batch compilation API.
//!
//! `CompilationDriver` already retains exact and incremental results for tools
//! that own a session. Batch callers historically constructed no session, so
//! identical bundles compiled independently in tests, build tools, and other
//! long-lived processes. This cache closes that gap without serializing misses:
//! the mutex is held only while looking up or publishing a completed result.

use std::{
    collections::VecDeque,
    sync::{Mutex, MutexGuard, OnceLock},
};

use crate::{
    CompileOptions, CompiledPhases,
    diagnostic::Diagnostic,
    source_bundle::SourceBundle,
};

const PROCESS_PHASE_CACHE_CAPACITY: usize = 4;

#[derive(Clone)]
struct CachedCompilation {
    bundle: SourceBundle,
    options: CompileOptions,
    phases: CompiledPhases,
}

#[derive(Default)]
struct ProcessPhaseCache {
    entries: VecDeque<CachedCompilation>,
}

static PROCESS_PHASE_CACHE: OnceLock<Mutex<ProcessPhaseCache>> = OnceLock::new();

fn cache() -> &'static Mutex<ProcessPhaseCache> {
    PROCESS_PHASE_CACHE.get_or_init(|| Mutex::new(ProcessPhaseCache::default()))
}

fn lock_cache() -> MutexGuard<'static, ProcessPhaseCache> {
    cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn lookup(bundle: &SourceBundle, options: CompileOptions) -> Option<CompiledPhases> {
    let mut cache = lock_cache();
    let index = cache
        .entries
        .iter()
        .position(|cached| cached.options == options && cached.bundle == *bundle)?;
    let cached = cache
        .entries
        .remove(index)
        .expect("process phase-cache entry disappeared");
    let phases = cached.phases.clone();
    cache.entries.push_front(cached);
    Some(phases)
}

fn publish(bundle: &SourceBundle, options: CompileOptions, phases: &CompiledPhases) {
    let mut cache = lock_cache();
    cache
        .entries
        .retain(|cached| cached.options != options || cached.bundle != *bundle);
    cache.entries.push_front(CachedCompilation {
        bundle: bundle.clone(),
        options,
        phases: phases.clone(),
    });
    cache.entries.truncate(PROCESS_PHASE_CACHE_CAPACITY);
}

pub(crate) fn compile_bundle_to_phases_with_options(
    bundle: &SourceBundle,
    options: CompileOptions,
) -> Result<CompiledPhases, Vec<Diagnostic>> {
    if let Some(phases) = lookup(bundle, options) {
        return Ok(phases);
    }

    let phases = crate::compiler::compile_bundle_to_phases_with_options(bundle, options)?;
    publish(bundle, options, &phases);
    Ok(phases)
}
