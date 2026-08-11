//! Persistent compilation driver state shared by editors, servers, and tools.
//!
//! Module/import/name context is rebuilt on body-changing requests. Provisional
//! per-body inference evidence is retained while the compiler's context
//! fingerprint (all source outside callable bodies) remains identical. A
//! bounded set of successful, fully verified phase outputs and terminal
//! diagnostics is additionally retained for exact-input retries, avoiding all
//! downstream work for duplicate checks and editor undo/redo without reusing
//! results across a semantic input change.

use std::collections::{BTreeMap, VecDeque};

use grandiose_vm::{Type, TypeId};

use crate::compiler_typeck::{DeclarationKey, IncrementalTypeCache};
use crate::diagnostic::Diagnostic;
use crate::source_bundle::SourceBundle;
use crate::{compiler_core as core, compiler_mir as mir};
use crate::{
    llvm_backend::{LlvmFragmentCache, LlvmModule, LlvmOptions},
    CompileOptions, CompiledPhases,
};

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
    /// Exact native object artifacts restored from the persistent backend
    /// cache. Object bytes are keyed by the complete generated IR and native
    /// compiler ABI/options; executable links are never eligible.
    pub reused_native_objects: usize,
    pub lowered_mir_bodies: usize,
    pub reused_mir_bodies: usize,
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
    pub(crate) mir_cache: IncrementalMirCache,
    phase_cache: VecDeque<CachedPhases>,
    diagnostic_cache: VecDeque<CachedDiagnostics>,
    llvm_cache: VecDeque<CachedLlvmIr>,
    llvm_fragment_cache: LlvmFragmentCache,
    native_object_cache: VecDeque<CachedNativeObject>,
    request_revision: u64,
    stats: IncrementalCompilationStats,
    diagnostic_stats: DiagnosticCacheStats,
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
        Ok(module)
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
                reused_native_objects: 0,
                lowered_mir_bodies: 0,
                reused_mir_bodies: cached.reusable_mir_bodies,
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
            reused_native_objects: 0,
            lowered_mir_bodies: self.mir_cache.lowered_bodies,
            reused_mir_bodies: self.mir_cache.reused_bodies,
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
}
