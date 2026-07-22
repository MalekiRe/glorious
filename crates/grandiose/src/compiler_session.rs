//! Persistent compilation driver state shared by editors, servers, and tools.
//!
//! Module/import/name context is rebuilt on body-changing requests. Provisional
//! per-body inference evidence is retained while the compiler's context
//! fingerprint (all source outside callable bodies) remains identical. The
//! A bounded set of successful, fully verified phase outputs is additionally
//! retained for exact-input retries, avoiding all downstream work for duplicate
//! checks and editor undo/redo without reusing artifacts across a semantic
//! input change.

use std::collections::{BTreeMap, VecDeque};

use grandiose_vm::{Type, TypeId};

use crate::compiler_typeck::{DeclarationKey, IncrementalTypeCache};
use crate::diagnostic::Diagnostic;
use crate::source_bundle::SourceBundle;
use crate::{CompileOptions, CompiledPhases};
use crate::{compiler_core as core, compiler_mir as mir};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct IncrementalCompilationStats {
    pub elaborated_bodies: usize,
    pub reused_bodies: usize,
    /// Exact-input checks satisfied by cloning the last successful verified
    /// Core, MIR, and bytecode phase output.
    pub reused_phase_artifacts: usize,
    /// Exact-input checks restored from an older successful revision rather
    /// than the immediately preceding revision. This is the common editor
    /// undo/redo and branch-switch case.
    pub reused_historical_phase_artifacts: usize,
    pub lowered_mir_bodies: usize,
    pub reused_mir_bodies: usize,
    pub frontend: crate::frontend_cache::FrontendCacheStats,
}

#[derive(Default)]
pub struct CompilationDriver {
    pub(crate) frontend_cache: crate::frontend_cache::IncrementalFrontendCache,
    pub(crate) type_cache: IncrementalTypeCache,
    pub(crate) mir_cache: IncrementalMirCache,
    phase_cache: VecDeque<CachedPhases>,
    stats: IncrementalCompilationStats,
}

#[derive(Clone)]
struct CachedPhases {
    bundle: SourceBundle,
    options: CompileOptions,
    phases: CompiledPhases,
    interfaces: Option<crate::interface::InterfaceBundleSnapshot>,
    reusable_bodies: usize,
    reusable_mir_bodies: usize,
}

/// Retaining a few complete revisions makes undo/redo effectively free while
/// keeping the potentially large verified bytecode artifacts strictly bounded.
const PHASE_CACHE_CAPACITY: usize = 4;

/// Compatibility name for callers that only need phase compilation.
pub type IncrementalCompilerSession = CompilationDriver;

#[derive(Clone, Debug)]
pub struct CompilationSnapshot {
    pub phases: CompiledPhases,
    pub interfaces: crate::interface::InterfaceBundleSnapshot,
}

impl CompilationDriver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn compile_bundle(
        &mut self,
        bundle: &SourceBundle,
        options: CompileOptions,
    ) -> Result<CompiledPhases, Vec<Diagnostic>> {
        self.compile_bundle_inner(bundle, options, false)
            .map(|(phases, _)| phases)
    }

    /// Check and extract both interface partitions from one parse and module
    /// resolution transaction. Successful results are cached atomically, so
    /// diagnostics and navigation can never describe different revisions.
    pub fn compile_bundle_with_interfaces(
        &mut self,
        bundle: &SourceBundle,
        options: CompileOptions,
    ) -> Result<CompilationSnapshot, Vec<Diagnostic>> {
        self.compile_bundle_inner(bundle, options, true)
            .map(|(phases, interfaces)| CompilationSnapshot {
                phases,
                interfaces: interfaces.expect("interface compilation produced no snapshot"),
            })
    }

    fn compile_bundle_inner(
        &mut self,
        bundle: &SourceBundle,
        options: CompileOptions,
        include_interfaces: bool,
    ) -> Result<
        (
            CompiledPhases,
            Option<crate::interface::InterfaceBundleSnapshot>,
        ),
        Vec<Diagnostic>,
    > {
        if let Some(index) = self.phase_cache.iter().position(|cached| {
            cached.options == options
                && cached.bundle == *bundle
                && (!include_interfaces || cached.interfaces.is_some())
        }) {
            let historical = index != 0;
            let cached = self
                .phase_cache
                .remove(index)
                .expect("phase cache index disappeared");
            self.stats = IncrementalCompilationStats {
                elaborated_bodies: 0,
                reused_bodies: cached.reusable_bodies,
                reused_phase_artifacts: 1,
                reused_historical_phase_artifacts: usize::from(historical),
                lowered_mir_bodies: 0,
                reused_mir_bodies: cached.reusable_mir_bodies,
                frontend: crate::frontend_cache::FrontendCacheStats::default(),
            };
            let result = (cached.phases.clone(), cached.interfaces.clone());
            self.phase_cache.push_front(cached);
            return Ok(result);
        }
        let checkpoint = self.type_cache.clone();
        let mir_checkpoint = self.mir_cache.clone();
        self.mir_cache.begin_revision();
        self.stats = IncrementalCompilationStats::default();
        let result = if include_interfaces {
            crate::compiler::compile_bundle_to_phases_incremental_with_interfaces(
                bundle, options, self,
            )
            .map(|(phases, interfaces)| (phases, Some(interfaces)))
        } else {
            crate::compiler::compile_bundle_to_phases_incremental(bundle, options, self)
                .map(|phases| (phases, None))
        };
        match &result {
            Ok((phases, interfaces)) => {
                // A plain phase compilation may be followed by an interface
                // request for the same input. Replace that incomplete entry
                // rather than consuming another revision slot.
                self.phase_cache
                    .retain(|cached| cached.options != options || cached.bundle != *bundle);
                self.phase_cache.push_front(CachedPhases {
                    bundle: bundle.clone(),
                    options,
                    phases: phases.clone(),
                    interfaces: interfaces.clone(),
                    reusable_bodies: self.stats.elaborated_bodies + self.stats.reused_bodies,
                    reusable_mir_bodies: self.stats.lowered_mir_bodies
                        + self.stats.reused_mir_bodies,
                });
                self.phase_cache.truncate(PHASE_CACHE_CAPACITY);
            }
            Err(_) => {
                self.type_cache = checkpoint;
                self.mir_cache = mir_checkpoint;
                self.stats = IncrementalCompilationStats::default();
            }
        }
        result
    }

    pub fn stats(&self) -> IncrementalCompilationStats {
        self.stats
    }

    pub(crate) fn publish_stats(&mut self) {
        self.stats = IncrementalCompilationStats {
            elaborated_bodies: self.type_cache.stats.elaborated_bodies,
            reused_bodies: self.type_cache.stats.reused_bodies,
            reused_phase_artifacts: 0,
            reused_historical_phase_artifacts: 0,
            lowered_mir_bodies: self.mir_cache.lowered_bodies,
            reused_mir_bodies: self.mir_cache.reused_bodies,
            frontend: self.frontend_cache.stats(),
        };
    }
}

#[derive(Clone, Default)]
pub(crate) struct IncrementalMirCache {
    types: Vec<Type>,
    custom_drop_types: Vec<TypeId>,
    entries: BTreeMap<u32, (core::Function, mir::Function)>,
    initialized: bool,
    lowered_bodies: usize,
    reused_bodies: usize,
}

impl IncrementalMirCache {
    fn begin_revision(&mut self) {
        self.lowered_bodies = 0;
        self.reused_bodies = 0;
    }

    pub(crate) fn prepare(&mut self, types: &[Type], custom_drop_types: &[TypeId]) {
        if !self.initialized
            || self.types != types
            || self.custom_drop_types.as_slice() != custom_drop_types
        {
            self.types = types.to_vec();
            self.custom_drop_types = custom_drop_types.to_vec();
            self.entries.clear();
            self.initialized = true;
        }
    }

    pub(crate) fn reuse(&mut self, function: &core::Function) -> Option<mir::Function> {
        let cached = self.entries.get(&function.declaration)?;
        if cached.0 != *function {
            return None;
        }
        self.reused_bodies += 1;
        Some(cached.1.clone())
    }

    pub(crate) fn insert(&mut self, function: core::Function, lowered: mir::Function) {
        self.lowered_bodies += 1;
        self.entries
            .insert(function.declaration, (function, lowered));
    }
}

pub(crate) struct IncrementalFingerprints {
    pub(crate) context: u64,
    pub(crate) bodies: BTreeMap<DeclarationKey, u64>,
}

pub(crate) fn fingerprints(
    bundle: &SourceBundle,
    program: &crate::ast::Program,
) -> IncrementalFingerprints {
    let mut body_ranges = program
        .functions
        .iter()
        .map(|function| (function.body.span, function.name.as_str()))
        .collect::<Vec<_>>();
    body_ranges.sort_by_key(|(span, _)| (span.start, span.end));
    let source = bundle.source().as_bytes();
    let mut context = Fnv1a::new();
    let mut cursor = 0;
    let mut bodies = BTreeMap::new();
    for (span, name) in body_ranges {
        let start = span.start.min(source.len()).max(cursor);
        let end = span.end.min(source.len()).max(start);
        context.write(&source[cursor..start]);
        context.write(b"<body>");
        let mut body = Fnv1a::new();
        body.write(&start.to_le_bytes());
        body.write(&source[start..end]);
        bodies.insert(DeclarationKey::Function(name.to_string()), body.finish());
        cursor = end;
    }
    context.write(&source[cursor..]);
    IncrementalFingerprints {
        context: context.finish(),
        bodies,
    }
}

struct Fnv1a(u64);

impl Fnv1a {
    fn new() -> Self {
        Self(0xcbf29ce484222325)
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(0x100000001b3);
        }
    }

    fn finish(self) -> u64 {
        self.0
    }
}
