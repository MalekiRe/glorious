//! Persistent compilation driver state shared by editors, servers, and tools.
//!
//! Module/import/name context is rebuilt on body-changing requests. Provisional
//! per-body inference evidence is retained while the compiler's context
//! fingerprint (all source outside callable bodies) remains identical. A
//! bounded set of successful, fully verified phase outputs and terminal
//! diagnostics is additionally retained for exact-input retries, avoiding all
//! downstream work for duplicate checks and editor undo/redo without reusing
//! results across a semantic input change.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    path::{Path, PathBuf},
};

use grandiose_vm::{Type, TypeId};

use crate::compiler_traits::{TraitDb, TrustedTraitManifest};
use crate::compiler_typeck::{DeclarationKey, IncrementalTypeCache};
use crate::diagnostic::Diagnostic;
use crate::source_bundle::SourceBundle;
use crate::{
    CompileOptions, CompiledPhases,
    llvm_backend::{LlvmFragmentCache, LlvmModule, LlvmOptions},
};
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
    /// Exact LLVM backend emissions restored from the bounded persistent
    /// backend cache. This is intentionally separate from phase reuse: LLVM
    /// emission can be avoided even when callers only observe native output.
    pub reused_llvm_ir: usize,
    /// Individual LLVM functions restored from manifest-valid cached fragments
    /// while the current module prelude/runtime/wrapper were regenerated.
    pub reused_llvm_fragments: usize,
    /// LLVM-reachable functions freshly emitted after the latest
    /// function-fragment cache lookup. This is paired with
    /// `reused_llvm_fragments` for the JSON-line incremental-native report.
    pub emitted_llvm_fragments: usize,
    /// Exact native object artifacts restored from the persistent backend
    /// cache. Object bytes are keyed by the complete generated IR and native
    /// compiler ABI/options; executable links are never eligible.
    pub reused_native_objects: usize,
    /// Independently compiled native units emitted for the current request.
    pub emitted_native_objects: usize,
    pub reused_native_function_objects: usize,
    pub emitted_native_function_objects: usize,
    pub emitted_native_shared_objects: usize,
    pub lowered_mir_bodies: usize,
    pub reused_mir_bodies: usize,
    /// Bodies restored after the ownership import and cleanup-elaboration
    /// boundary. This is deliberately separate from raw MIR lowering reuse:
    /// the entry is usable only when its consumed array-call summaries match.
    pub reused_cleanup_mir_bodies: usize,
    /// Complete O3 MIR bodies restored from the dependency-validated durable
    /// cache. These bodies bypass repeated local ownership analysis while
    /// their changed direct-call closure continues through the normal O3
    /// schedule.
    pub reused_optimized_mir_bodies: usize,
    /// Final optimized bodies whose exact ownership/cleanup proof was restored
    /// from the durable per-body validation cache.
    pub reused_final_validation_bodies: usize,
    /// Exact local O3 transformation snapshots restored after a body edit.
    /// Snapshots are segregated by the complete MIR type/drop schema and are
    /// checked again against their precise MIR input before use.
    pub reused_optimizer_body_snapshots: usize,
    /// Structural trait/nominal/impl database restored after a callable-body
    /// edit. Span-keyed source const arguments are refreshed before use.
    pub reused_trait_databases: usize,
    pub frontend: crate::frontend_cache::FrontendCacheStats,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DiagnosticCacheStats {
    /// Exact invalid-input checks satisfied by cloning terminal diagnostics.
    pub reused_results: usize,
    /// Invalid-input checks restored from an older revision. This is common for
    /// editor undo/redo across two independently invalid states.
    pub reused_historical_results: usize,
}

#[derive(Default)]
pub struct CompilationDriver {
    pub(crate) frontend_cache: crate::frontend_cache::IncrementalFrontendCache,
    pub(crate) type_cache: IncrementalTypeCache,
    pub(crate) trait_db_cache: IncrementalTraitDbCache,
    pub(crate) mir_cache: IncrementalMirCache,
    phase_cache: VecDeque<CachedPhases>,
    diagnostic_cache: VecDeque<CachedDiagnostics>,
    llvm_cache: VecDeque<CachedLlvmIr>,
    llvm_fragment_cache: LlvmFragmentCache,
    native_object_cache: VecDeque<CachedNativeObject>,
    native_function_object_cache: VecDeque<CachedNativeFunctionObject>,
    request_revision: u64,
    stats: IncrementalCompilationStats,
    diagnostic_stats: DiagnosticCacheStats,
}

#[derive(Clone, Default)]
pub(crate) struct IncrementalTraitDbCache {
    entries: VecDeque<CachedTraitDb>,
    reused_databases: usize,
}

const INCREMENTAL_TRAIT_DB_CONTEXT_CAPACITY: usize = 4;

#[derive(Clone)]
struct CachedTraitDb {
    /// Exact source with callable bodies masked byte-for-byte. Masking retains
    /// body lengths, so all declaration spans remain part of the key.
    context: Vec<u8>,
    manifest: TrustedTraitManifest,
    database: TraitDb,
}

impl IncrementalTraitDbCache {
    fn begin_revision(&mut self) {
        self.reused_databases = 0;
    }

    pub(crate) fn build_or_reuse(
        &mut self,
        program: &crate::ast::Program,
        manifest: &TrustedTraitManifest,
        context: &[u8],
    ) -> Result<TraitDb, Vec<Diagnostic>> {
        if let Some(index) = self
            .entries
            .iter()
            .position(|cached| cached.context == context && cached.manifest == *manifest)
        {
            let cached = self
                .entries
                .remove(index)
                .expect("trait-db index was found");
            self.reused_databases = self.reused_databases.saturating_add(1);
            let database = cached
                .database
                .clone()
                .with_current_type_const_arguments(program);
            self.entries.push_front(cached);
            return Ok(database);
        }
        let database = TraitDb::build_with_manifest(program, manifest)?;
        self.entries
            .retain(|cached| cached.context != context || cached.manifest != *manifest);
        self.entries.push_front(CachedTraitDb {
            context: context.to_vec(),
            manifest: manifest.clone(),
            database: database.clone(),
        });
        self.entries.truncate(INCREMENTAL_TRAIT_DB_CONTEXT_CAPACITY);
        Ok(database)
    }
}

#[derive(Clone)]
struct CachedPhases {
    bundle: SourceBundle,
    options: CompileOptions,
    phases: CompiledPhases,
    interfaces: Option<crate::interface::InterfaceBundleSnapshot>,
    reusable_bodies: usize,
    reusable_mir_bodies: usize,
    last_used_revision: u64,
}

#[derive(Clone)]
struct CachedDiagnostics {
    bundle: SourceBundle,
    options: CompileOptions,
    include_interfaces: bool,
    diagnostics: Vec<Diagnostic>,
    last_used_revision: u64,
}

/// Cache schema is independent of the bytecode artifact version.  Bumping it
/// deliberately invalidates all retained LLVM text after backend changes.
const LLVM_CACHE_SCHEMA: u32 = 1;
const LLVM_CACHE_CAPACITY: usize = 4;
const NATIVE_OBJECT_CACHE_CAPACITY: usize = 4;
/// Function units are intentionally independent of a source revision. Their
/// exact IR and native compiler ABI are the complete cache authority.
const NATIVE_FUNCTION_OBJECT_CACHE_CAPACITY: usize = 128;

/// Cached native units are process-local, but they are still treated as
/// untrusted bytes at the materialization boundary.  Recognize the portable
/// object-file container magics emitted by Clang; a truncated or otherwise
/// corrupt cache entry is evicted and recompiled rather than handed to Wild.
fn native_object_bytes_are_plausible(bytes: &[u8]) -> bool {
    bytes.starts_with(b"\x7fELF")
        || bytes.starts_with(&[0xfe, 0xed, 0xfa, 0xce])
        || bytes.starts_with(&[0xfe, 0xed, 0xfa, 0xcf])
        || bytes.starts_with(&[0xce, 0xfa, 0xed, 0xfe])
        || bytes.starts_with(&[0xcf, 0xfa, 0xed, 0xfe])
        || bytes.starts_with(&[0x4c, 0x01]) // COFF i386
        || bytes.starts_with(&[0x64, 0x86]) // COFF x86_64
        || bytes.starts_with(&[0xaa, 0x64]) // COFF arm64
}

#[derive(Clone)]
struct CachedLlvmIr {
    schema: u32,
    bundle: SourceBundle,
    source_fingerprint: [u8; 32],
    options: CompileOptions,
    target: LlvmOptions,
    module: LlvmModule,
    last_used_revision: u64,
}

#[derive(Clone)]
struct CachedNativeObject {
    /// The source/options/target values are retained in addition to the exact
    /// IR so cache retention remains inspectable and an object cannot survive
    /// a backend-cache schema change accidentally.
    schema: u32,
    bundle: SourceBundle,
    source_fingerprint: [u8; 32],
    options: CompileOptions,
    target: LlvmOptions,
    ir: String,
    toolchain_abi: String,
    bytes: Vec<u8>,
    last_used_revision: u64,
}

#[derive(Clone)]
struct CachedNativeFunctionObject {
    schema: u32,
    target: LlvmOptions,
    ir: String,
    toolchain_abi: String,
    bytes: Vec<u8>,
    last_used_revision: u64,
}

/// Retaining a few complete revisions makes undo/redo effectively free while
/// keeping the potentially large verified bytecode artifacts strictly bounded.
const PHASE_CACHE_CAPACITY: usize = 4;

/// Invalid revisions are also bounded because each key retains its exact source
/// bundle to make cache hits collision-free.
const DIAGNOSTIC_CACHE_CAPACITY: usize = 4;

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

    /// Restore only validated, per-body type evidence from a durable compiler
    /// cache.  Higher layers remain ordinary cache misses until they gain
    /// their own independently versioned on-disk formats.
    pub fn restore_persistent_type_cache(&mut self, bytes: &[u8]) -> bool {
        let Some(cache) = IncrementalTypeCache::decode_persistent(bytes) else {
            return false;
        };
        self.type_cache = cache;
        true
    }

    pub fn persistent_type_cache(&self) -> Result<Vec<u8>, bincode::Error> {
        self.type_cache.encode_persistent()
    }

    /// Incorporate a concurrently published durable type cache.  Entries
    /// produced by this driver remain authoritative for matching bodies.
    pub fn merge_persistent_type_cache(&mut self, bytes: &[u8]) -> bool {
        let Some(cache) = IncrementalTypeCache::decode_persistent(bytes) else {
            return false;
        };
        self.type_cache.merge_persistent(cache);
        true
    }

    /// Restore validated, independently emitted LLVM function fragments. The
    /// backend replays their exact post-specialization/post-inlining text and
    /// regenerates only the current module-level scaffolding.
    pub fn restore_persistent_llvm_fragment_cache(&mut self, bytes: &[u8]) -> bool {
        let Some(cache) = LlvmFragmentCache::decode_persistent(bytes) else {
            return false;
        };
        self.llvm_fragment_cache = cache;
        true
    }

    /// Configure lazy, independently validated LLVM fragment files. Unlike
    /// the historical blob cache, this does not deserialize unrelated
    /// functions before a request can start compiling.
    pub fn configure_persistent_llvm_fragment_directory(&mut self, directory: std::path::PathBuf) {
        self.llvm_fragment_cache
            .configure_persistent_directory(directory);
    }

    pub fn persist_persistent_llvm_fragment_directory(&self) -> Result<(), String> {
        self.llvm_fragment_cache.persist_to_directory()
    }

    pub fn persistent_llvm_fragment_cache(&self) -> Result<Vec<u8>, bincode::Error> {
        self.llvm_fragment_cache.encode_persistent()
    }

    /// Merge concurrent durable fragment publication while retaining this
    /// driver's freshly generated optimized fragments as the authority.
    pub fn merge_persistent_llvm_fragment_cache(&mut self, bytes: &[u8]) -> bool {
        self.llvm_fragment_cache.merge_persistent(bytes)
    }

    /// Restore exact per-function MIR, cleanup facts, and local O3 pass
    /// snapshots from the durable compiler cache.
    pub fn restore_persistent_mir_cache(&mut self, bytes: &[u8]) -> bool {
        let Some(cache) = IncrementalMirCache::decode_persistent(bytes) else {
            return false;
        };
        self.mir_cache = cache;
        true
    }

    pub fn persistent_mir_cache(&self) -> Result<Vec<u8>, bincode::Error> {
        self.mir_cache.encode_persistent()
    }

    /// Configure lazy per-function final O3 snapshots beside the durable MIR
    /// cache. This does not hydrate the directory; bodies are read only after
    /// their exact dependency key is known.
    pub fn configure_persistent_optimized_mir_directory(&mut self, directory: PathBuf) {
        self.mir_cache
            .configure_persistent_optimized_directory(directory);
    }

    pub fn persist_persistent_optimized_mir_directory(&self) -> Result<(), String> {
        self.mir_cache.persist_optimized_to_directory()
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

    /// Emit LLVM IR with a bounded exact-input cache owned by this persistent
    /// driver. The key contains both a collision-resistant source/dependency
    /// fingerprint and the complete bundle/options values, so a digest can
    /// never authorize reuse by itself. Target layout and entry-wrapper ABI
    /// are included because either changes generated IR.
    pub fn emit_llvm_ir(
        &mut self,
        bundle: &SourceBundle,
        options: CompileOptions,
        phases: &CompiledPhases,
        target: &LlvmOptions,
    ) -> Result<LlvmModule, Vec<Diagnostic>> {
        let source_fingerprint = llvm_source_fingerprint(bundle);
        if let Some(index) = self.llvm_cache.iter().position(|cached| {
            cached.schema == LLVM_CACHE_SCHEMA
                && cached.source_fingerprint == source_fingerprint
                && cached.bundle == *bundle
                && cached.options == options
                && cached.target == *target
        }) {
            let mut cached = self
                .llvm_cache
                .remove(index)
                .expect("LLVM cache index disappeared");
            cached.last_used_revision = self.request_revision;
            let module = cached.module.clone();
            self.llvm_cache.push_front(cached);
            self.stats.reused_llvm_ir = self.stats.reused_llvm_ir.saturating_add(1);
            self.stats.reused_llvm_fragments = 0;
            return Ok(module);
        }

        let module =
            crate::emit_llvm_ir_with_fragment_cache(phases, target, &mut self.llvm_fragment_cache)?;
        self.llvm_cache.push_front(CachedLlvmIr {
            schema: LLVM_CACHE_SCHEMA,
            bundle: bundle.clone(),
            source_fingerprint,
            options,
            target: target.clone(),
            module: module.clone(),
            last_used_revision: self.request_revision,
        });
        self.llvm_cache.truncate(LLVM_CACHE_CAPACITY);
        self.stats.reused_llvm_ir = 0;
        self.stats.reused_llvm_fragments = self.llvm_fragment_cache.reused_fragments();
        self.stats.emitted_llvm_fragments = self.llvm_fragment_cache.emitted_fragments();
        Ok(module)
    }

    /// Emit native object partitions while retaining reusable LLVM function
    /// fragments for later `--serve` requests.  This is separate from the
    /// exact whole-module cache: partitioned native output still needs a
    /// current shared unit and final link after a body edit.
    pub fn emit_llvm_native_object_units(
        &mut self,
        phases: &CompiledPhases,
        target: &LlvmOptions,
    ) -> Result<crate::llvm_backend::LlvmNativeObjectUnits, Vec<Diagnostic>> {
        let units = crate::llvm_backend::emit_llvm_native_object_units_with_fragment_cache(
            phases,
            target,
            &mut self.llvm_fragment_cache,
        )?;
        self.stats.reused_llvm_ir = 0;
        self.stats.reused_llvm_fragments = self.llvm_fragment_cache.reused_fragments();
        self.stats.emitted_llvm_fragments = self.llvm_fragment_cache.emitted_fragments();
        Ok(units)
    }

    /// Return immutable native object bytes only for the exact emitted IR and
    /// complete native compiler ABI/options. The caller owns writing bytes to
    /// its current `-o` path; paths and executables are deliberately absent
    /// from this cache.
    pub fn cached_native_object(
        &mut self,
        bundle: &SourceBundle,
        options: CompileOptions,
        target: &LlvmOptions,
        ir: &str,
        toolchain_abi: &str,
    ) -> Option<Vec<u8>> {
        let source_fingerprint = llvm_source_fingerprint(bundle);
        let index = self.native_object_cache.iter().position(|cached| {
            cached.schema == LLVM_CACHE_SCHEMA
                && cached.source_fingerprint == source_fingerprint
                && cached.bundle == *bundle
                && cached.options == options
                && cached.target == *target
                && cached.ir == ir
                && cached.toolchain_abi == toolchain_abi
        })?;
        let mut cached = self
            .native_object_cache
            .remove(index)
            .expect("native object cache index disappeared");
        if !native_object_bytes_are_plausible(&cached.bytes) {
            return None;
        }
        cached.last_used_revision = self.request_revision;
        let bytes = cached.bytes.clone();
        self.native_object_cache.push_front(cached);
        self.stats.reused_native_objects = self.stats.reused_native_objects.saturating_add(1);
        Some(bytes)
    }

    pub fn cache_native_object(
        &mut self,
        bundle: &SourceBundle,
        options: CompileOptions,
        target: &LlvmOptions,
        ir: &str,
        toolchain_abi: String,
        bytes: Vec<u8>,
    ) {
        let source_fingerprint = llvm_source_fingerprint(bundle);
        self.native_object_cache.retain(|cached| {
            cached.schema != LLVM_CACHE_SCHEMA
                || cached.source_fingerprint != source_fingerprint
                || cached.bundle != *bundle
                || cached.options != options
                || cached.target != *target
                || cached.ir != ir
                || cached.toolchain_abi != toolchain_abi
        });
        self.native_object_cache.push_front(CachedNativeObject {
            schema: LLVM_CACHE_SCHEMA,
            bundle: bundle.clone(),
            source_fingerprint,
            options,
            target: target.clone(),
            ir: ir.to_owned(),
            toolchain_abi,
            bytes,
            last_used_revision: self.request_revision,
        });
        self.native_object_cache
            .truncate(NATIVE_OBJECT_CACHE_CAPACITY);
    }

    /// Restore one independently compiled native unit. Unlike the monolithic
    /// object cache this deliberately does not include the source bundle: a
    /// body-only edit may retain a byte-identical sibling function object.
    pub fn cached_native_partitioned_object(
        &mut self,
        target: &LlvmOptions,
        ir: &str,
        toolchain_abi: &str,
        source_function: bool,
    ) -> Option<Vec<u8>> {
        let index = self
            .native_function_object_cache
            .iter()
            .position(|cached| {
                cached.schema == LLVM_CACHE_SCHEMA
                    && cached.target == *target
                    && cached.ir == ir
                    && cached.toolchain_abi == toolchain_abi
            })?;
        let mut cached = self
            .native_function_object_cache
            .remove(index)
            .expect("native function object cache index disappeared");
        if !native_object_bytes_are_plausible(&cached.bytes) {
            return None;
        }
        cached.last_used_revision = self.request_revision;
        let bytes = cached.bytes.clone();
        self.native_function_object_cache.push_front(cached);
        self.stats.reused_native_objects = self.stats.reused_native_objects.saturating_add(1);
        if source_function {
            self.stats.reused_native_function_objects =
                self.stats.reused_native_function_objects.saturating_add(1);
        }
        Some(bytes)
    }

    pub fn cache_native_partitioned_object(
        &mut self,
        target: &LlvmOptions,
        ir: &str,
        toolchain_abi: String,
        bytes: Vec<u8>,
    ) {
        self.native_function_object_cache.retain(|cached| {
            cached.schema != LLVM_CACHE_SCHEMA
                || cached.target != *target
                || cached.ir != ir
                || cached.toolchain_abi != toolchain_abi
        });
        self.native_function_object_cache
            .push_front(CachedNativeFunctionObject {
                schema: LLVM_CACHE_SCHEMA,
                target: target.clone(),
                ir: ir.to_owned(),
                toolchain_abi,
                bytes,
                last_used_revision: self.request_revision,
            });
        self.native_function_object_cache
            .truncate(NATIVE_FUNCTION_OBJECT_CACHE_CAPACITY);
    }

    pub fn record_native_partitioned_object_emitted(&mut self, source_function: bool) {
        self.stats.emitted_native_objects = self.stats.emitted_native_objects.saturating_add(1);
        if source_function {
            self.stats.emitted_native_function_objects =
                self.stats.emitted_native_function_objects.saturating_add(1);
        } else {
            self.stats.emitted_native_shared_objects =
                self.stats.emitted_native_shared_objects.saturating_add(1);
        }
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
        self.request_revision = self.request_revision.wrapping_add(1);
        let request_revision = self.request_revision;
        if let Some(index) = self.phase_cache.iter().position(|cached| {
            cached.options == options
                && cached.bundle == *bundle
                && (!include_interfaces || cached.interfaces.is_some())
        }) {
            let cached = self
                .phase_cache
                .remove(index)
                .expect("phase cache index disappeared");
            let historical = cached.last_used_revision != request_revision.wrapping_sub(1);
            let mut cached = cached;
            cached.last_used_revision = request_revision;
            self.stats = IncrementalCompilationStats {
                elaborated_bodies: 0,
                reused_bodies: cached.reusable_bodies,
                reused_phase_artifacts: 1,
                reused_historical_phase_artifacts: usize::from(historical),
                reused_llvm_ir: 0,
                reused_llvm_fragments: 0,
                emitted_llvm_fragments: 0,
                reused_native_objects: 0,
                emitted_native_objects: 0,
                reused_native_function_objects: 0,
                emitted_native_function_objects: 0,
                emitted_native_shared_objects: 0,
                lowered_mir_bodies: 0,
                reused_mir_bodies: cached.reusable_mir_bodies,
                reused_cleanup_mir_bodies: 0,
                reused_optimized_mir_bodies: 0,
                reused_final_validation_bodies: 0,
                reused_optimizer_body_snapshots: 0,
                reused_trait_databases: 0,
                frontend: crate::frontend_cache::FrontendCacheStats::default(),
            };
            self.diagnostic_stats = DiagnosticCacheStats::default();
            let result = (cached.phases.clone(), cached.interfaces.clone());
            self.phase_cache.push_front(cached);
            return Ok(result);
        }
        if let Some(index) = self.diagnostic_cache.iter().position(|cached| {
            cached.options == options
                && cached.include_interfaces == include_interfaces
                && cached.bundle == *bundle
        }) {
            let cached = self
                .diagnostic_cache
                .remove(index)
                .expect("diagnostic cache index disappeared");
            let historical = cached.last_used_revision != request_revision.wrapping_sub(1);
            let mut cached = cached;
            cached.last_used_revision = request_revision;
            self.stats = IncrementalCompilationStats::default();
            self.diagnostic_stats = DiagnosticCacheStats {
                reused_results: 1,
                reused_historical_results: usize::from(historical),
            };
            let diagnostics = cached.diagnostics.clone();
            self.diagnostic_cache.push_front(cached);
            return Err(diagnostics);
        }

        let checkpoint = self.type_cache.clone();
        let mir_checkpoint = self.mir_cache.clone();
        self.mir_cache.begin_revision();
        self.trait_db_cache.begin_revision();
        self.stats = IncrementalCompilationStats::default();
        self.diagnostic_stats = DiagnosticCacheStats::default();
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
                    last_used_revision: request_revision,
                });
                self.phase_cache.truncate(PHASE_CACHE_CAPACITY);
                // A successful revision supersedes any terminal-diagnostic
                // entry for the same exact semantic input.
                self.diagnostic_cache
                    .retain(|cached| cached.options != options || cached.bundle != *bundle);
            }
            Err(diagnostics) => {
                self.type_cache = checkpoint;
                self.mir_cache = mir_checkpoint;
                self.stats = IncrementalCompilationStats::default();
                self.diagnostic_cache.retain(|cached| {
                    cached.options != options
                        || cached.include_interfaces != include_interfaces
                        || cached.bundle != *bundle
                });
                self.diagnostic_cache.push_front(CachedDiagnostics {
                    bundle: bundle.clone(),
                    options,
                    include_interfaces,
                    diagnostics: diagnostics.clone(),
                    last_used_revision: request_revision,
                });
                self.diagnostic_cache.truncate(DIAGNOSTIC_CACHE_CAPACITY);
            }
        }
        result
    }

    pub fn stats(&self) -> IncrementalCompilationStats {
        self.stats
    }

    pub fn diagnostic_cache_stats(&self) -> DiagnosticCacheStats {
        self.diagnostic_stats
    }

    pub(crate) fn publish_stats(&mut self) {
        self.stats = IncrementalCompilationStats {
            elaborated_bodies: self.type_cache.stats.elaborated_bodies,
            reused_bodies: self.type_cache.stats.reused_bodies,
            reused_phase_artifacts: 0,
            reused_historical_phase_artifacts: 0,
            reused_llvm_ir: 0,
            reused_llvm_fragments: 0,
            emitted_llvm_fragments: 0,
            reused_native_objects: 0,
            emitted_native_objects: 0,
            reused_native_function_objects: 0,
            emitted_native_function_objects: 0,
            emitted_native_shared_objects: 0,
            lowered_mir_bodies: self.mir_cache.lowered_bodies,
            reused_mir_bodies: self.mir_cache.reused_bodies,
            reused_cleanup_mir_bodies: self.mir_cache.reused_cleanup_bodies,
            reused_optimized_mir_bodies: self.mir_cache.reused_optimized_bodies,
            reused_final_validation_bodies: self.mir_cache.reused_final_validation_bodies,
            reused_optimizer_body_snapshots: self.mir_cache.reused_optimizer_body_snapshots,
            reused_trait_databases: self.trait_db_cache.reused_databases,
            frontend: self.frontend_cache.stats(),
        };
    }
}

fn llvm_source_fingerprint(bundle: &SourceBundle) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"grandiose:llvm-ir-cache:source-v1\0");
    for segment in bundle.segments() {
        for field in [
            segment.name().as_bytes(),
            segment.package_root().unwrap_or_default().as_bytes(),
            segment.source().as_bytes(),
        ] {
            hasher.update(&(field.len() as u64).to_le_bytes());
            hasher.update(field);
        }
    }
    *hasher.finalize().as_bytes()
}

#[derive(Clone, Default)]
pub(crate) struct IncrementalMirCache {
    schemas: VecDeque<CachedMirSchema>,
    entries: BTreeMap<(u64, u32), CachedMirBody>,
    local_pass_snapshots: BTreeMap<
        (u64, u32, crate::compiler_mir::optimizer::PassId),
        VecDeque<crate::compiler_mir::optimizer::TransactionalPassBodySnapshot>,
    >,
    optimized: BTreeMap<OptimizedMirKey, OptimizedMirEntry>,
    optimized_disk_directory: Option<PathBuf>,
    final_validation: BTreeMap<FinalValidationKey, FinalValidationEntry>,
    final_validation_disk_directory: Option<PathBuf>,
    active_schema: Option<u64>,
    next_schema: u64,
    lowered_bodies: usize,
    reused_bodies: usize,
    reused_cleanup_bodies: usize,
    reused_optimized_bodies: usize,
    reused_final_validation_bodies: usize,
    reused_optimizer_body_snapshots: usize,
}

#[derive(Clone, serde::Deserialize, serde::Serialize)]
struct CachedMirSchema {
    id: u64,
    types: Vec<Type>,
    custom_drop_types: Vec<TypeId>,
}

const INCREMENTAL_MIR_SCHEMA_CAPACITY: usize = 4;
const PERSISTENT_MIR_CACHE_SCHEMA: u32 = 1;

#[derive(Clone)]
struct CachedMirBody {
    core: Option<core::Function>,
    core_debug: String,
    lowered: mir::Function,
    /// Cleanup MIR is only valid under the exact summary fingerprint for the
    /// direct array-call facts consumed while ownership was imported.
    cleanup: Option<(u64, mir::Function)>,
}

#[derive(serde::Deserialize, serde::Serialize)]
struct PersistentMirCache {
    schema: u32,
    schemas: VecDeque<CachedMirSchema>,
    entries: BTreeMap<(u64, u32), PersistentMirBody>,
    local_pass_snapshots: BTreeMap<
        (u64, u32, crate::compiler_mir::optimizer::PassId),
        VecDeque<crate::compiler_mir::optimizer::TransactionalPassBodySnapshot>,
    >,
}

#[derive(serde::Deserialize, serde::Serialize)]
struct PersistentMirBody {
    core_debug: String,
    lowered: mir::Function,
    cleanup: Option<(u64, mir::Function)>,
}

/// A final O3 body is retained separately from the monolithic raw-MIR cache.
/// Its key includes the exact pre-optimization body and the complete direct
/// dependency closure, letting an unrelated source edit keep already
/// specialized and inlined compiler functions intact.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, serde::Deserialize, serde::Serialize)]
struct OptimizedMirKey {
    schema: u64,
    declaration: u32,
    dependency_fingerprint: u64,
    namespace_fingerprint: u64,
}

#[derive(Clone, serde::Deserialize, serde::Serialize)]
struct OptimizedMirEntry {
    input: mir::Function,
    output: mir::Function,
}

#[derive(serde::Deserialize, serde::Serialize)]
struct PersistentOptimizedMirEntry {
    schema: u32,
    key: OptimizedMirKey,
    input: mir::Function,
    output: mir::Function,
}

const PERSISTENT_OPTIMIZED_MIR_ENTRY_SCHEMA: u32 = 1;

/// A completed final ownership/cleanup proof is reusable independently of O3
/// output reuse. This intentionally accepts generated and handler bodies: the
/// exact post-O3 MIR input, its active type schema, and the summaries it can
/// consume are all checked again before a proof is trusted.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, serde::Deserialize, serde::Serialize)]
struct FinalValidationKey {
    schema: u64,
    declaration: u32,
    dependency_fingerprint: u64,
    body_fingerprint: [u8; 32],
}

#[derive(Clone, serde::Deserialize, serde::Serialize)]
struct FinalValidationEntry {
    input: mir::Function,
}

#[derive(serde::Deserialize, serde::Serialize)]
struct PersistentFinalValidationEntry {
    schema: u32,
    key: FinalValidationKey,
    input: mir::Function,
}

const PERSISTENT_FINAL_VALIDATION_ENTRY_SCHEMA: u32 = 1;

fn optimized_mir_entry_path(directory: &Path, key: &OptimizedMirKey) -> Result<PathBuf, String> {
    let bytes = bincode::serialize(key)
        .map_err(|error| format!("could not encode optimized MIR cache key: {error}"))?;
    Ok(directory.join(format!("{}.bin", blake3::hash(&bytes).to_hex())))
}

fn final_validation_key(
    schema: u64,
    input: &mir::Function,
    dependency_fingerprint: u64,
) -> Option<FinalValidationKey> {
    let body = bincode::serialize(input).ok()?;
    Some(FinalValidationKey {
        schema,
        declaration: input.declaration,
        dependency_fingerprint,
        body_fingerprint: *blake3::hash(&body).as_bytes(),
    })
}

fn final_validation_entry_path(
    directory: &Path,
    key: &FinalValidationKey,
) -> Result<PathBuf, String> {
    let bytes = bincode::serialize(key)
        .map_err(|error| format!("could not encode final validation cache key: {error}"))?;
    Ok(directory.join(format!("{}.bin", blake3::hash(&bytes).to_hex())))
}

impl IncrementalMirCache {
    fn begin_revision(&mut self) {
        self.lowered_bodies = 0;
        self.reused_bodies = 0;
        self.reused_cleanup_bodies = 0;
        self.reused_optimized_bodies = 0;
        self.reused_final_validation_bodies = 0;
        self.reused_optimizer_body_snapshots = 0;
    }

    pub(crate) fn prepare(&mut self, types: &[Type], custom_drop_types: &[TypeId]) {
        if let Some(position) = self.schemas.iter().position(|schema| {
            schema.types == types && schema.custom_drop_types.as_slice() == custom_drop_types
        }) {
            let schema = self
                .schemas
                .remove(position)
                .expect("schema index was found");
            self.active_schema = Some(schema.id);
            self.schemas.push_front(schema);
            return;
        }
        self.next_schema = self.next_schema.wrapping_add(1);
        let schema = CachedMirSchema {
            id: self.next_schema,
            types: types.to_vec(),
            custom_drop_types: custom_drop_types.to_vec(),
        };
        self.active_schema = Some(schema.id);
        self.schemas.push_front(schema);
        while self.schemas.len() > INCREMENTAL_MIR_SCHEMA_CAPACITY {
            let evicted = self.schemas.pop_back().expect("length was checked");
            self.entries.retain(|(schema, _), _| *schema != evicted.id);
            self.local_pass_snapshots
                .retain(|(schema, _, _), _| *schema != evicted.id);
            self.optimized.retain(|key, _| key.schema != evicted.id);
            self.final_validation.retain(|key, _| key.schema != evicted.id);
        }
    }

    fn active_key(&self, declaration: u32) -> Option<(u64, u32)> {
        self.active_schema.map(|schema| (schema, declaration))
    }

    pub(crate) fn reuse(&mut self, function: &core::Function) -> Option<mir::Function> {
        let cached = self.entries.get(&self.active_key(function.declaration)?)?;
        let matches = cached.core.as_ref().is_some_and(|core| *core == *function)
            || cached.core_debug == format!("{function:?}");
        if !matches {
            return None;
        }
        self.reused_bodies += 1;
        Some(cached.lowered.clone())
    }

    /// Restore a post-cleanup body only after the caller has completely
    /// accounted for every interprocedural array summary it consumes.
    pub(crate) fn reuse_cleanup(
        &mut self,
        function: &mir::Function,
        dependency_fingerprint: Option<u64>,
    ) -> Option<mir::Function> {
        let dependency_fingerprint = dependency_fingerprint?;
        let cached = self.entries.get(&self.active_key(function.declaration)?)?;
        let (cached_fingerprint, cleanup) = cached.cleanup.as_ref()?;
        // The dependency fingerprint protects interprocedural ownership
        // summaries, but it is not a body identity. A body-only source edit
        // must never recover the previous function's cleanup facts merely
        // because its direct callees happened not to change.
        if cached.lowered != *function || *cached_fingerprint != dependency_fingerprint {
            return None;
        }
        self.reused_cleanup_bodies += 1;
        Some(cleanup.clone())
    }

    pub(crate) fn cache_cleanup(
        &mut self,
        function: &mir::Function,
        dependency_fingerprint: Option<u64>,
    ) {
        let Some(dependency_fingerprint) = dependency_fingerprint else {
            return;
        };
        let Some(key) = self.active_key(function.declaration) else {
            return;
        };
        let Some(cached) = self.entries.get_mut(&key) else {
            // Pattern/synthesized bodies have no exact raw-Core authority.
            return;
        };
        cached.cleanup = Some((dependency_fingerprint, function.clone()));
    }

    /// Assign a worktree-local directory holding independently readable final
    /// O3 bodies. Unlike the historical monolithic caches, configuring this
    /// directory does not read or deserialize any body.
    pub(crate) fn configure_persistent_optimized_directory(&mut self, directory: PathBuf) {
        self.final_validation_disk_directory = Some(directory.join("final-validation-v1"));
        self.optimized_disk_directory = Some(directory);
    }

    fn optimized_key(
        &self,
        declaration: u32,
        dependency_fingerprint: u64,
        namespace_fingerprint: u64,
    ) -> Option<OptimizedMirKey> {
        Some(OptimizedMirKey {
            schema: self.active_schema?,
            declaration,
            dependency_fingerprint,
            namespace_fingerprint,
        })
    }

    /// Recover an exact final O3 body. The caller supplies the current
    /// cleanup-boundary body as well as its complete direct-call dependency
    /// fingerprint; both values must match the entry before it becomes
    /// eligible to bypass the optimizer.
    pub(crate) fn reuse_optimized(
        &mut self,
        input: &mir::Function,
        dependency_fingerprint: u64,
        namespace_fingerprint: u64,
    ) -> Option<mir::Function> {
        let key = self.optimized_key(
            input.declaration,
            dependency_fingerprint,
            namespace_fingerprint,
        )?;
        if let Some(entry) = self.optimized.get(&key) {
            if entry.input == *input && entry.output.phase == mir::MirPhase::Optimized {
                self.reused_optimized_bodies = self.reused_optimized_bodies.saturating_add(1);
                return Some(entry.output.clone());
            }
        }
        let directory = self.optimized_disk_directory.as_ref()?;
        let path = optimized_mir_entry_path(directory, &key).ok()?;
        let bytes = std::fs::read(path).ok()?;
        let entry = bincode::deserialize::<PersistentOptimizedMirEntry>(&bytes).ok()?;
        if entry.schema != PERSISTENT_OPTIMIZED_MIR_ENTRY_SCHEMA
            || entry.key != key
            || entry.input != *input
            || entry.output.declaration != input.declaration
            || entry.output.phase != mir::MirPhase::Optimized
        {
            return None;
        }
        let output = entry.output.clone();
        self.optimized.insert(
            key,
            OptimizedMirEntry {
                input: entry.input,
                output: entry.output,
            },
        );
        self.reused_optimized_bodies = self.reused_optimized_bodies.saturating_add(1);
        Some(output)
    }

    /// Retain an output only when its source function has a current exact
    /// cleanup cache entry. Pattern-generated bodies intentionally have no
    /// durable Core identity and are left on the ordinary optimizer path.
    pub(crate) fn cache_optimized(
        &mut self,
        output: &mir::Function,
        dependency_fingerprint: u64,
        namespace_fingerprint: u64,
    ) {
        let Some(key) = self.optimized_key(
            output.declaration,
            dependency_fingerprint,
            namespace_fingerprint,
        ) else {
            return;
        };
        let Some(active_key) = self.active_key(output.declaration) else {
            return;
        };
        let Some(cached) = self.entries.get(&active_key) else {
            return;
        };
        let Some((_, input)) = &cached.cleanup else {
            return;
        };
        self.optimized.insert(
            key,
            OptimizedMirEntry {
                input: input.clone(),
                output: output.clone(),
            },
        );
    }

    /// Reuse a completed final optimized-MIR ownership/cleanup proof. The
    /// body comparison is deliberately exact after the BLAKE3-addressed disk
    /// lookup, so a hash collision can only turn into a cache miss.
    pub(crate) fn reuse_final_validation(
        &mut self,
        input: &mir::Function,
        dependency_fingerprint: u64,
    ) -> bool {
        let Some(schema) = self.active_schema else {
            return false;
        };
        let Some(key) = final_validation_key(schema, input, dependency_fingerprint) else {
            return false;
        };
        if let Some(entry) = self.final_validation.get(&key) {
            if entry.input == *input {
                self.reused_final_validation_bodies =
                    self.reused_final_validation_bodies.saturating_add(1);
                return true;
            }
        }
        let Some(directory) = self.final_validation_disk_directory.as_ref() else {
            return false;
        };
        let Ok(path) = final_validation_entry_path(directory, &key) else {
            return false;
        };
        let Ok(bytes) = std::fs::read(path) else {
            return false;
        };
        let Ok(entry) = bincode::deserialize::<PersistentFinalValidationEntry>(&bytes) else {
            return false;
        };
        if entry.schema != PERSISTENT_FINAL_VALIDATION_ENTRY_SCHEMA
            || entry.key != key
            || entry.input != *input
            || entry.input.phase != mir::MirPhase::Optimized
        {
            return false;
        }
        self.final_validation
            .insert(key, FinalValidationEntry { input: entry.input });
        self.reused_final_validation_bodies =
            self.reused_final_validation_bodies.saturating_add(1);
        true
    }

    /// Record one exact final checkpoint input after its ownership/cleanup
    /// proof succeeds. Unlike the O3 output cache, this includes generated
    /// declarations because the body itself anchors their current IDs.
    pub(crate) fn cache_final_validation(
        &mut self,
        input: &mir::Function,
        dependency_fingerprint: u64,
    ) {
        let Some(schema) = self.active_schema else {
            return;
        };
        let Some(key) = final_validation_key(schema, input, dependency_fingerprint) else {
            return;
        };
        self.final_validation.insert(
            key,
            FinalValidationEntry {
                input: input.clone(),
            },
        );
    }

    /// Publish each newly produced final O3 body separately. Cache files are
    /// addressed by every semantic input in `OptimizedMirKey`, so retaining a
    /// previous source revision never invalidates unrelated entries.
    pub(crate) fn persist_optimized_to_directory(&self) -> Result<(), String> {
        let Some(directory) = &self.optimized_disk_directory else {
            return Ok(());
        };
        std::fs::create_dir_all(directory).map_err(|error| {
            format!(
                "could not create optimized MIR directory {}: {error}",
                directory.display()
            )
        })?;
        for (key, entry) in &self.optimized {
            let path = optimized_mir_entry_path(directory, key)?;
            if path.exists() {
                continue;
            }
            let bytes = bincode::serialize(&PersistentOptimizedMirEntry {
                schema: PERSISTENT_OPTIMIZED_MIR_ENTRY_SCHEMA,
                key: key.clone(),
                input: entry.input.clone(),
                output: entry.output.clone(),
            })
            .map_err(|error| format!("could not encode optimized MIR body: {error}"))?;
            let temporary = path.with_extension(format!("{}.tmp", std::process::id()));
            std::fs::write(&temporary, bytes).map_err(|error| {
                format!(
                    "could not write optimized MIR body {}: {error}",
                    temporary.display()
                )
            })?;
            if let Err(error) = std::fs::rename(&temporary, &path) {
                let _ = std::fs::remove_file(&temporary);
                if !path.exists() {
                    return Err(format!(
                        "could not publish optimized MIR body {}: {error}",
                        path.display()
                    ));
                }
            }
        }
        let Some(directory) = &self.final_validation_disk_directory else {
            return Ok(());
        };
        std::fs::create_dir_all(directory).map_err(|error| {
            format!(
                "could not create final validation cache directory {}: {error}",
                directory.display()
            )
        })?;
        for (key, entry) in &self.final_validation {
            let path = final_validation_entry_path(directory, key)?;
            if path.exists() {
                continue;
            }
            let bytes = bincode::serialize(&PersistentFinalValidationEntry {
                schema: PERSISTENT_FINAL_VALIDATION_ENTRY_SCHEMA,
                key: key.clone(),
                input: entry.input.clone(),
            })
            .map_err(|error| format!("could not encode final validation body: {error}"))?;
            let temporary = path.with_extension(format!("{}.tmp", std::process::id()));
            std::fs::write(&temporary, bytes).map_err(|error| {
                format!(
                    "could not write final validation body {}: {error}",
                    temporary.display()
                )
            })?;
            if let Err(error) = std::fs::rename(&temporary, &path) {
                let _ = std::fs::remove_file(&temporary);
                if !path.exists() {
                    return Err(format!(
                        "could not publish final validation body {}: {error}",
                        path.display()
                    ));
                }
            }
        }
        Ok(())
    }

    pub(crate) fn insert(&mut self, function: core::Function, lowered: mir::Function) {
        self.lowered_bodies += 1;
        let Some(key) = self.active_key(function.declaration) else {
            return;
        };
        self.entries.insert(
            key,
            CachedMirBody {
                core_debug: format!("{function:?}"),
                core: Some(function),
                lowered,
                cleanup: None,
            },
        );
    }

    /// Persist exact per-function raw/cleanup MIR plus transactional local
    /// optimizer snapshots. Core validity is bound to its deterministic
    /// structural representation, while MIR remains binary data.
    pub(crate) fn encode_persistent(&self) -> Result<Vec<u8>, bincode::Error> {
        let entries = self
            .entries
            .iter()
            .map(|(key, entry)| {
                (
                    *key,
                    PersistentMirBody {
                        core_debug: entry.core_debug.clone(),
                        lowered: entry.lowered.clone(),
                        cleanup: entry.cleanup.clone(),
                    },
                )
            })
            .collect();
        bincode::serialize(&PersistentMirCache {
            schema: PERSISTENT_MIR_CACHE_SCHEMA,
            schemas: self.schemas.clone(),
            entries,
            local_pass_snapshots: self.local_pass_snapshots.clone(),
        })
    }

    pub(crate) fn decode_persistent(bytes: &[u8]) -> Option<Self> {
        let persisted = bincode::deserialize::<PersistentMirCache>(bytes).ok()?;
        if persisted.schema != PERSISTENT_MIR_CACHE_SCHEMA
            || persisted.schemas.len() > INCREMENTAL_MIR_SCHEMA_CAPACITY
        {
            return None;
        }
        let known_schemas = persisted
            .schemas
            .iter()
            .map(|schema| schema.id)
            .collect::<BTreeSet<_>>();
        if persisted
            .entries
            .keys()
            .any(|(schema, _)| !known_schemas.contains(schema))
            || persisted
                .local_pass_snapshots
                .keys()
                .any(|(schema, _, _)| !known_schemas.contains(schema))
        {
            return None;
        }
        let next_schema = persisted
            .schemas
            .iter()
            .map(|schema| schema.id)
            .max()
            .unwrap_or_default();
        Some(Self {
            schemas: persisted.schemas,
            entries: persisted
                .entries
                .into_iter()
                .map(|(key, entry)| {
                    (
                        key,
                        CachedMirBody {
                            core: None,
                            core_debug: entry.core_debug,
                            lowered: entry.lowered,
                            cleanup: entry.cleanup,
                        },
                    )
                })
                .collect(),
            local_pass_snapshots: persisted.local_pass_snapshots,
            optimized: BTreeMap::new(),
            optimized_disk_directory: None,
            final_validation: BTreeMap::new(),
            final_validation_disk_directory: None,
            active_schema: None,
            next_schema,
            lowered_bodies: 0,
            reused_bodies: 0,
            reused_cleanup_bodies: 0,
            reused_optimized_bodies: 0,
            reused_final_validation_bodies: 0,
            reused_optimizer_body_snapshots: 0,
        })
    }
}

impl crate::compiler_mir::optimizer::TransactionalPassBodyCache for IncrementalMirCache {
    fn restore(
        &mut self,
        pass: crate::compiler_mir::optimizer::PassId,
        input: &mir::Function,
        work_limit: u64,
    ) -> Option<crate::compiler_mir::optimizer::TransactionalPassBodySnapshot> {
        let (schema, declaration) = self.active_key(input.declaration)?;
        let key = (schema, declaration, pass);
        let snapshots = self.local_pass_snapshots.get_mut(&key)?;
        let position = snapshots.iter().position(|snapshot| {
            snapshot.input == *input
                && snapshot.work_units <= work_limit
                && snapshot.outcome != crate::compiler_mir::optimizer::PassOutcome::BudgetExhausted
        })?;
        let snapshot = snapshots
            .remove(position)
            .expect("snapshot index was found");
        snapshots.push_front(snapshot.clone());
        self.reused_optimizer_body_snapshots += 1;
        Some(snapshot)
    }

    fn record(
        &mut self,
        pass: crate::compiler_mir::optimizer::PassId,
        snapshot: crate::compiler_mir::optimizer::TransactionalPassBodySnapshot,
    ) {
        let Some((schema, declaration)) = self.active_key(snapshot.input.declaration) else {
            return;
        };
        let snapshots = self
            .local_pass_snapshots
            .entry((schema, declaration, pass))
            .or_default();
        if let Some(position) = snapshots
            .iter()
            .position(|cached| cached.input == snapshot.input)
        {
            snapshots.remove(position);
        }
        snapshots.push_front(snapshot);
        snapshots.truncate(3);
    }
}

pub(crate) struct IncrementalFingerprints {
    pub(crate) context: u64,
    /// Exact source context for structural trait-db reuse. Callable-body bytes
    /// are masked but their byte positions are retained, so edits that shift a
    /// later declaration cannot accidentally reuse stale span-keyed facts.
    pub(crate) trait_db_context: Vec<u8>,
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
    let mut trait_db_context = source.to_vec();
    let mut callable_ranges = program
        .functions
        .iter()
        .map(|function| function.body.span)
        .chain(
            program
                .impls
                .iter()
                .flat_map(|implementation| &implementation.methods)
                .filter_map(|method| method.body.as_ref().map(|body| body.span)),
        )
        .collect::<Vec<_>>();
    callable_ranges.sort_by_key(|span| (span.start, span.end));
    for span in callable_ranges {
        let start = span.start.min(trait_db_context.len());
        let end = span.end.min(trait_db_context.len()).max(start);
        trait_db_context[start..end].fill(0);
    }
    IncrementalFingerprints {
        context: context.finish(),
        trait_db_context,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{compiler_mir::OptimizationLevel, source_bundle::Segment};

    fn invalid_bundle(source: &str) -> SourceBundle {
        SourceBundle::raw_for_conformance(
            Segment::new("std.glorious", ""),
            Segment::new("main.glorious", source),
            [],
        )
    }

    #[test]
    fn terminal_diagnostics_are_reused_for_exact_inputs_and_undo() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O0,
        };
        let first = invalid_bundle("main() { let value = ; }");
        let second = invalid_bundle("main() { missing( } ");
        let mut driver = CompilationDriver::new();

        let first_diagnostics = driver.compile_bundle(&first, options).unwrap_err();
        assert_eq!(driver.diagnostic_cache_stats().reused_results, 0);

        assert_eq!(
            format!("{:?}", driver.compile_bundle(&first, options).unwrap_err()),
            format!("{first_diagnostics:?}")
        );
        assert_eq!(driver.diagnostic_cache_stats().reused_results, 1);
        assert_eq!(driver.diagnostic_cache_stats().reused_historical_results, 0);

        assert!(driver.compile_bundle(&second, options).is_err());
        assert!(driver.compile_bundle(&first, options).is_err());
        assert_eq!(driver.diagnostic_cache_stats().reused_results, 1);
        assert_eq!(driver.diagnostic_cache_stats().reused_historical_results, 1);
    }

    #[test]
    fn diagnostic_cache_keys_modes_options_and_evicts_old_entries() {
        let o0 = CompileOptions {
            optimization_level: OptimizationLevel::O0,
        };
        let o1 = CompileOptions {
            optimization_level: OptimizationLevel::O1,
        };
        let first = invalid_bundle("main() { missing_a( }");
        let mut driver = CompilationDriver::new();

        assert!(driver.compile_bundle(&first, o0).is_err());
        assert!(driver.compile_bundle(&first, o1).is_err());
        assert_eq!(driver.diagnostic_cache_stats().reused_results, 0);
        assert!(driver.compile_bundle_with_interfaces(&first, o0).is_err());
        assert_eq!(driver.diagnostic_cache_stats().reused_results, 0);

        for suffix in ["b", "c", "d", "e"] {
            let bundle = invalid_bundle(&format!("main() {{ missing_{suffix}( }}"));
            assert!(driver.compile_bundle(&bundle, o0).is_err());
        }
        assert!(driver.compile_bundle(&first, o0).is_err());
        assert_eq!(driver.diagnostic_cache_stats().reused_results, 0);
    }

    #[test]
    fn diagnostic_reuse_is_historical_after_a_successful_revision() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O0,
        };
        let invalid = invalid_bundle("main() { missing( }");
        let valid = invalid_bundle("main() -> () { () }");
        let mut driver = CompilationDriver::new();

        assert!(driver.compile_bundle(&invalid, options).is_err());
        assert!(driver.compile_bundle(&valid, options).is_ok());
        assert!(driver.compile_bundle(&invalid, options).is_err());
        assert_eq!(driver.diagnostic_cache_stats().reused_results, 1);
        assert_eq!(driver.diagnostic_cache_stats().reused_historical_results, 1);
    }

    #[test]
    fn llvm_ir_cache_hits_only_for_exact_bundle_and_target_options() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O2,
        };
        let first = invalid_bundle("main() -> { () }");
        let second = invalid_bundle("main() -> { let marker = 2; () }");
        let target = LlvmOptions::default();
        let mut driver = CompilationDriver::new();

        let first_phases = driver.compile_bundle(&first, options).unwrap();
        let first_ir = driver
            .emit_llvm_ir(&first, options, &first_phases, &target)
            .unwrap();
        assert_eq!(driver.stats().reused_llvm_ir, 0);
        let cached_ir = driver
            .emit_llvm_ir(&first, options, &first_phases, &target)
            .unwrap();
        assert_eq!(cached_ir, first_ir);
        assert_eq!(driver.stats().reused_llvm_ir, 1);

        // A content change has a distinct fingerprint and exact bundle value;
        // it must re-emit rather than returning stale IR for the first body.
        let second_phases = driver.compile_bundle(&second, options).unwrap();
        let second_ir = driver
            .emit_llvm_ir(&second, options, &second_phases, &target)
            .unwrap();
        assert_eq!(driver.stats().reused_llvm_ir, 0);
        assert_eq!(
            second_ir,
            crate::emit_llvm_ir(&second_phases, &target).unwrap(),
            "a cache miss must return the current phases' IR, never stale text"
        );

        // The allocation ceiling is embedded in native runtime helpers.  It
        // is target ABI, not merely a driver preference, so it must also miss
        // the persistent IR/fragment cache.
        let mut different_allocation_limit = target.clone();
        different_allocation_limit.native_allocation_limit *= 2;
        driver
            .emit_llvm_ir(
                &second,
                options,
                &second_phases,
                &different_allocation_limit,
            )
            .unwrap();
        assert_eq!(driver.stats().reused_llvm_ir, 0);
        assert_eq!(driver.stats().reused_llvm_fragments, 0);

        let mut different_target = target.clone();
        different_target.emit_entry_wrapper = false;
        driver
            .emit_llvm_ir(&second, options, &second_phases, &different_target)
            .unwrap();
        assert_eq!(driver.stats().reused_llvm_ir, 0);

        // Dependency segments participate in the same source fingerprint.
        // Changing an otherwise inert dependency comment must still miss:
        // package/module topology affects resolution and backend reachability.
        let dependency_changed = SourceBundle::raw_for_conformance(
            Segment::new("std.glorious", ""),
            Segment::new("main.glorious", "main() -> { let marker = 2; () }"),
            [Segment::new("dependency.glorious", "// changed dependency")],
        );
        let dependency_phases = driver.compile_bundle(&dependency_changed, options).unwrap();
        let dependency_ir = driver
            .emit_llvm_ir(&dependency_changed, options, &dependency_phases, &target)
            .unwrap();
        assert_eq!(driver.stats().reused_llvm_ir, 0);
        assert_eq!(
            dependency_ir,
            crate::emit_llvm_ir(&dependency_phases, &target).unwrap()
        );
    }

    #[test]
    fn native_partitions_reuse_unchanged_llvm_fragments_after_a_body_edit() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O3,
        };
        let target = LlvmOptions::default();
        let before = invalid_bundle(
            "leaf() -> i64 { 1 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
        );
        let after = invalid_bundle(
            "leaf() -> i64 { 2 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
        );
        let mut driver = CompilationDriver::new();

        let before_phases = driver.compile_bundle(&before, options).unwrap();
        let cold = driver
            .emit_llvm_native_object_units(&before_phases, &target)
            .unwrap();
        assert_eq!(driver.stats().reused_llvm_fragments, 0);
        assert_eq!(driver.stats().emitted_llvm_fragments, 3);

        let after_phases = driver.compile_bundle(&after, options).unwrap();
        let warm = driver
            .emit_llvm_native_object_units(&after_phases, &target)
            .unwrap();
        assert_eq!(driver.stats().reused_llvm_fragments, 2);
        assert_eq!(driver.stats().emitted_llvm_fragments, 1);
        assert_eq!(
            warm,
            crate::llvm_backend::emit_llvm_native_object_units(&after_phases, &target).unwrap(),
            "cache-backed native partitions must remain byte-for-byte canonical"
        );
        assert_ne!(
            cold, warm,
            "the changed leaf must produce fresh native units"
        );
    }

    #[test]
    fn llvm_fragments_retain_unrelated_bodies_after_a_literal_edit() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O3,
        };
        let target = LlvmOptions::default();
        // Keep the changed literal's source width fixed so this test isolates
        // the old global-literal-table dependency rather than source spans.
        let before = invalid_bundle(
            "stable() -> Text { \"steady\" } changed() -> Text { \"before\" } main() -> () { stable(); changed(); () }",
        );
        let after = invalid_bundle(
            "stable() -> Text { \"steady\" } changed() -> Text { \"alter!\" } main() -> () { stable(); changed(); () }",
        );
        let before_phases = crate::compile_bundle_to_phases_with_options(&before, options).unwrap();
        let before_manifest =
            crate::llvm_backend::llvm_incremental_manifest(&before_phases, &target);
        let before_ir = crate::emit_llvm_ir(&before_phases, &target).unwrap();
        let after_phases = crate::compile_bundle_to_phases_with_options(&after, options).unwrap();
        let after_manifest = crate::llvm_backend::llvm_incremental_manifest(&after_phases, &target);
        let after_ir = crate::emit_llvm_ir(&after_phases, &target).unwrap();
        assert_eq!(
            before_manifest.runtime_abi_fingerprint, after_manifest.runtime_abi_fingerprint,
            "content-addressed literal globals must not be a module ABI change"
        );
        let invalidated = after_manifest.invalidated_functions(&before_manifest);
        // O3 has inlined `changed` into `main`, so its real dependent caller
        // also changes. `stable` remains independently reusable; the old
        // ordinal global table incorrectly invalidated all three bodies.
        assert_eq!(
            invalidated.len(),
            2,
            "only the edit and its inlined caller may miss"
        );
        let stable_symbol = format!("@g1.bytes.{}", blake3::hash(b"steady").to_hex());
        assert!(before_ir.ir.contains(&stable_symbol));
        assert!(after_ir.ir.contains(&stable_symbol));
        let partitions =
            crate::llvm_backend::emit_llvm_native_object_units(&before_phases, &target).unwrap();
        assert!(
            !partitions.shared.ir.contains(&stable_symbol),
            "the shared partition must not inherit source-literal cache dependencies"
        );
        assert_eq!(
            partitions
                .functions
                .iter()
                .filter(|function| function.module.ir.contains(&stable_symbol))
                .count(),
            1,
            "only the source fragment that references a literal receives its definition"
        );
    }

    #[test]
    fn persistent_type_cache_reuses_unchanged_bodies_after_driver_restart() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O2,
        };
        let before = invalid_bundle(
            "leaf() -> i64 { 1 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
        );
        // Keep the edited body byte length stable. The two other callable
        // bodies are eligible for reuse after the fresh driver restores its
        // serialized state, exactly as a new CLI invocation does.
        let after = invalid_bundle(
            "leaf() -> i64 { 2 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
        );
        let mut first_driver = CompilationDriver::new();
        assert!(first_driver.compile_bundle(&before, options).is_ok());
        let persisted = first_driver.persistent_type_cache().unwrap();
        assert!(!persisted.is_empty());

        let mut restarted_driver = CompilationDriver::new();
        assert!(restarted_driver.restore_persistent_type_cache(&persisted));
        let warm = restarted_driver.compile_bundle(&after, options).unwrap();
        assert_eq!(restarted_driver.stats().reused_bodies, 2);

        let cold = crate::compile_bundle_to_phases_with_options(&after, options).unwrap();
        assert_eq!(
            warm.provisional_fingerprint(),
            cold.provisional_fingerprint()
        );
        assert_eq!(warm.core_fingerprint(), cold.core_fingerprint());
        assert_eq!(warm.mir_fingerprint(), cold.mir_fingerprint());
    }

    #[test]
    fn persistent_llvm_fragments_reuse_post_inlining_bodies_after_restart() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O3,
        };
        let target = LlvmOptions::default();
        let before = invalid_bundle(
            "leaf() -> i64 { 1 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
        );
        let after = invalid_bundle(
            "leaf() -> i64 { 2 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
        );
        let mut first_driver = CompilationDriver::new();
        let before_phases = first_driver.compile_bundle(&before, options).unwrap();
        first_driver
            .emit_llvm_native_object_units(&before_phases, &target)
            .unwrap();
        let persisted = first_driver.persistent_llvm_fragment_cache().unwrap();
        assert!(!persisted.is_empty());

        let mut restarted_driver = CompilationDriver::new();
        assert!(restarted_driver.restore_persistent_llvm_fragment_cache(&persisted));
        let after_phases = restarted_driver.compile_bundle(&after, options).unwrap();
        let warm = restarted_driver
            .emit_llvm_native_object_units(&after_phases, &target)
            .unwrap();
        assert_eq!(restarted_driver.stats().reused_llvm_fragments, 2);
        assert_eq!(restarted_driver.stats().emitted_llvm_fragments, 1);
        assert_eq!(
            warm,
            crate::llvm_backend::emit_llvm_native_object_units(&after_phases, &target).unwrap()
        );
    }

    #[test]
    fn persistent_mir_cache_reuses_raw_and_cleanup_bodies_after_restart() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O3,
        };
        let before = invalid_bundle(
            "leaf() -> i64 { 1 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
        );
        let after = invalid_bundle(
            "leaf() -> i64 { 2 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
        );
        let mut first_driver = CompilationDriver::new();
        assert!(first_driver.compile_bundle(&before, options).is_ok());
        let persisted = first_driver.persistent_mir_cache().unwrap();
        assert!(!persisted.is_empty());

        let mut restarted_driver = CompilationDriver::new();
        assert!(restarted_driver.restore_persistent_mir_cache(&persisted));
        let warm = restarted_driver.compile_bundle(&after, options).unwrap();
        assert_eq!(restarted_driver.stats().reused_mir_bodies, 2);
        assert!(
            restarted_driver.stats().reused_optimizer_body_snapshots > 0,
            "unchanged O3 local-pass slots should replay their exact snapshots"
        );

        let cold = crate::compile_bundle_to_phases_with_options(&after, options).unwrap();
        assert_eq!(warm.core_fingerprint(), cold.core_fingerprint());
        assert_eq!(warm.mir_fingerprint(), cold.mir_fingerprint());
    }

    #[test]
    fn optimized_mir_cache_reuses_unrelated_o3_body_after_callee_edit() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O3,
        };
        let before = invalid_bundle(
            "leaf() -> i64 { 1 } caller() -> i64 { leaf() } unrelated() -> i64 { 9 } main() -> () { caller(); unrelated(); () }",
        );
        let after = invalid_bundle(
            "leaf() -> i64 { 2 } caller() -> i64 { leaf() } unrelated() -> i64 { 9 } main() -> () { caller(); unrelated(); () }",
        );
        let mut driver = CompilationDriver::new();
        assert!(driver.compile_bundle(&before, options).is_ok());
        let warm = driver.compile_bundle(&after, options).unwrap();
        assert!(
            driver.stats().reused_optimized_mir_bodies > 0,
            "unrelated O3 bodies should bypass the optimizer: {:?}",
            driver.stats()
        );
        if !cfg!(debug_assertions) {
            assert!(
                driver.stats().reused_final_validation_bodies > 0,
                "unchanged optimized bodies should bypass the repeated final ownership proof: {:?}",
                driver.stats()
            );
        }

        let cold = crate::compile_bundle_to_phases_with_options(&after, options).unwrap();
        assert_eq!(warm.core_fingerprint(), cold.core_fingerprint());
        assert_eq!(warm.mir_fingerprint(), cold.mir_fingerprint());
    }

    #[test]
    fn structural_trait_db_reuses_after_body_edit_and_invalidates_on_impl_edit() {
        let options = CompileOptions {
            optimization_level: OptimizationLevel::O2,
        };
        let before = invalid_bundle(
            "struct Ticket { value: i64 } impl Use<[0,1]> for Ticket {} leaf() -> i64 { 1 } main() -> () { leaf(); () }",
        );
        let body_edit = invalid_bundle(
            "struct Ticket { value: i64 } impl Use<[0,1]> for Ticket {} leaf() -> i64 { 2 } main() -> () { leaf(); () }",
        );
        let impl_edit = invalid_bundle(
            "struct Ticket { value: i64 } impl Use<[1,1]> for Ticket {} leaf() -> i64 { 2 } main() -> () { leaf(); () }",
        );
        let mut driver = CompilationDriver::new();

        assert!(driver.compile_bundle(&before, options).is_ok());
        let cached = driver.compile_bundle(&body_edit, options).unwrap();
        assert_eq!(driver.stats().reused_trait_databases, 1);
        let fresh = crate::compile_bundle_to_phases_with_options(&body_edit, options).unwrap();
        assert_eq!(
            cached.provisional_fingerprint(),
            fresh.provisional_fingerprint()
        );
        assert_eq!(cached.core_fingerprint(), fresh.core_fingerprint());
        assert_eq!(cached.mir_fingerprint(), fresh.mir_fingerprint());

        assert!(driver.compile_bundle(&impl_edit, options).is_ok());
        assert_eq!(driver.stats().reused_trait_databases, 0);
    }

    #[test]
    fn native_object_cache_requires_exact_ir_options_and_toolchain_abi() {
        let o2 = CompileOptions {
            optimization_level: OptimizationLevel::O2,
        };
        let o3 = CompileOptions {
            optimization_level: OptimizationLevel::O3,
        };
        let bundle = invalid_bundle("main() -> () { () }");
        let changed_bundle = invalid_bundle("main() -> () { let value = (); value }");
        let target = LlvmOptions::default();
        let ir = "; exact generated IR";
        let abi = "clang=example;target=example;opt=-O2";
        let bytes = vec![0x7f, b'E', b'L', b'F'];
        let mut driver = CompilationDriver::new();

        assert_eq!(
            driver.cached_native_object(&bundle, o2, &target, ir, abi),
            None
        );
        driver.cache_native_object(&bundle, o2, &target, ir, abi.into(), bytes.clone());
        assert_eq!(
            driver.cached_native_object(&bundle, o2, &target, ir, abi),
            Some(bytes),
            "cache values are artifact bytes, never an output path"
        );
        assert_eq!(
            driver.cached_native_object(&bundle, o3, &target, ir, abi),
            None,
            "optimization options are part of the native object ABI"
        );
        assert_eq!(
            driver.cached_native_object(&changed_bundle, o2, &target, ir, abi),
            None,
            "source bundle identity is retained alongside exact IR"
        );
        assert_eq!(
            driver.cached_native_object(&bundle, o2, &target, "; changed IR", abi),
            None
        );
        assert_eq!(
            driver.cached_native_object(&bundle, o2, &target, ir, "clang=changed"),
            None
        );
    }

    #[test]
    fn corrupt_partitioned_native_object_is_evicted_before_reuse() {
        let mut driver = CompilationDriver::new();
        let target = LlvmOptions::default();
        driver.cache_native_partitioned_object(
            &target,
            "; function fragment",
            "clang=example;opt=-O3".into(),
            vec![0, 1, 2],
        );
        assert_eq!(
            driver.cached_native_partitioned_object(
                &target,
                "; function fragment",
                "clang=example;opt=-O3",
                true,
            ),
            None,
            "corrupt bytes must be dropped so the caller recompiles the unit"
        );
        assert!(driver.native_function_object_cache.is_empty());
    }
}
