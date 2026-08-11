//! LLVM IR emission from optimized Grandiose MIR.
//!
//! This first backend slice deliberately supports the pure scalar/control-flow
//! core. Unsupported ownership-heavy operations are diagnosed instead of being
//! assigned an accidental ABI.

use std::collections::{BTreeMap, BTreeSet};

use grandiose_vm::{Constant, Primitive, Type, TypeId};

use crate::{
    compiler_core::stable_fingerprint,
    compiler_mir::{self as mir, InstructionKind, Terminator},
    compiler_traits::HostImportRole,
    diagnostic::Diagnostic,
    llvm_runtime_abi::{pointer_width_for_target, runtime_fault_declaration},
    CompiledPhases,
};

const RUNTIME_FAULT_ARITHMETIC_OVERFLOW: u32 = 1;
const RUNTIME_FAULT_DIVISION_BY_ZERO: u32 = 2;
const RUNTIME_FAULT_INVALID_SHIFT_COUNT: u32 = 3;
const RUNTIME_FAULT_INVALID_CHARACTER: u32 = 4;
const RUNTIME_FAULT_INVALID_UTF8: u32 = 5;
const RUNTIME_FAULT_INDEX_OUT_OF_BOUNDS: u32 = 6;
const RUNTIME_FAULT_EMPTY_ARRAY_SLOT: u32 = 7;
const RUNTIME_FAULT_ARRAY_SLOT_ALREADY_INITIALIZED: u32 = 8;
const RUNTIME_FAULT_ARRAY_NOT_DRAINED: u32 = 9;
const RUNTIME_FAULT_ALLOCATION_OVERFLOW: u32 = 10;
const RUNTIME_FAULT_ALLOCATION_LIMIT: u32 = 11;
const RUNTIME_FAULT_UNHANDLED_EFFECT: u32 = 12;
const RUNTIME_FAULT_EXPLICIT_ABORT: u32 = 13;
/// Default maximum size of one native-runtime bytes or array allocation.
///
/// Ordinary native programs retain this conservative ceiling. The self-host
/// compiler may opt into a larger, still bounded ceiling through `LlvmOptions`
/// because its compiler-internal tables exceed this per-allocation size.
pub const DEFAULT_NATIVE_ALLOCATION_LIMIT: u64 = 64 * 1024 * 1024;

/// Bump this whenever LLVM fragment generation changes independently of MIR.
/// Cached fragments with another schema are never reusable.
pub const LLVM_INCREMENTAL_MANIFEST_SCHEMA: u32 = 2;

/// The ABI-facing identity of a direct callee used by one emitted fragment.
/// A callee body change alone deliberately does not invalidate its callers.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LlvmCalleeDependency {
    pub declaration: u32,
    pub interface_fingerprint: u64,
}

/// Cache key for one independently emitted LLVM function fragment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmFunctionManifest {
    pub declaration: u32,
    pub interface_fingerprint: u64,
    pub body_fingerprint: u64,
    pub callee_interfaces: Vec<LlvmCalleeDependency>,
    /// Includes the selected target/runtime ABI and every interface dependency.
    pub fragment_fingerprint: u64,
}

/// Deterministic cache/invalidation manifest for function-granular LLVM IR.
///
/// This intentionally describes reusable fragments rather than caching the
/// current monolithic IR string. A future cache can retain a matching function
/// body while rebuilding declarations, runtime support, globals, and the entry
/// wrapper for every module invocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmIncrementalManifest {
    pub schema: u32,
    pub target_triple: String,
    pub target_data_layout: Option<String>,
    pub emit_entry_wrapper: bool,
    /// Embedded per-allocation runtime ceiling.  This changes runtime helper
    /// IR, so fragment reuse across limits would produce an incoherent module.
    pub native_allocation_limit: u64,
    /// Changes to the global type/runtime ABI invalidate every fragment.
    pub runtime_abi_fingerprint: u64,
    pub functions: Vec<LlvmFunctionManifest>,
}

/// Reusable text and side metadata for one independently emitted function.
///
/// LLVM intrinsic declarations are emitted at module scope.  Consequently a
/// fragment is not valid text by itself unless its metadata is replayed into
/// the enclosing module before those declarations are written.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmFunctionFragment {
    pub fingerprint: u64,
    pub emitted_text: String,
    pub overflow_widths: BTreeSet<(u16, &'static str)>,
    snapshot_capture_fix_types: BTreeSet<TypeId>,
}

/// Bounded-by-owner cache for independently emitted LLVM functions.  The
/// owner chooses its lifetime (the persistent compilation driver retains one
/// across `--serve` requests); this type deliberately owns no filesystem
/// state and never serializes unchecked IR.
#[derive(Clone, Debug, Default)]
pub struct LlvmFragmentCache {
    manifest: Option<LlvmIncrementalManifest>,
    fragments: BTreeMap<u32, LlvmFunctionFragment>,
    reused_fragments: usize,
}

impl LlvmFragmentCache {
    pub fn reused_fragments(&self) -> usize {
        self.reused_fragments
    }

    pub fn clear(&mut self) {
        self.manifest = None;
        self.fragments.clear();
        self.reused_fragments = 0;
    }
}

impl LlvmIncrementalManifest {
    /// Functions whose cached fragment cannot be reused from `previous`.
    /// An option or runtime ABI change conservatively invalidates all bodies.
    pub fn invalidated_functions(&self, previous: &Self) -> BTreeSet<u32> {
        if self.schema != previous.schema
            || self.target_triple != previous.target_triple
            || self.target_data_layout != previous.target_data_layout
            || self.emit_entry_wrapper != previous.emit_entry_wrapper
            || self.native_allocation_limit != previous.native_allocation_limit
            || self.runtime_abi_fingerprint != previous.runtime_abi_fingerprint
        {
            return self
                .functions
                .iter()
                .map(|function| function.declaration)
                .collect();
        }
        let previous = previous
            .functions
            .iter()
            .map(|function| (function.declaration, function.fragment_fingerprint))
            .collect::<BTreeMap<_, _>>();
        self.functions
            .iter()
            .filter_map(|function| {
                (previous.get(&function.declaration) != Some(&function.fragment_fingerprint))
                    .then_some(function.declaration)
            })
            .collect()
    }
}

fn fingerprint_text(text: impl std::fmt::Display) -> u64 {
    stable_fingerprint(text.to_string().as_bytes())
}

fn function_interface_fingerprint(function: &mir::Function) -> u64 {
    fingerprint_text(format!(
        "decl={} params={:?} result={} receiver={:?}:{} no_return={} outward={:?}",
        function.declaration,
        function.params,
        function.result,
        function.receiver_mode,
        function.receiver_type,
        function.no_return,
        function.outward_protocols,
    ))
}

fn function_body_fingerprint(function: &mir::Function) -> u64 {
    // Blocks and ownership/flow evidence are all consumed by LLVM emission.
    // Source spans are retained in this representation, so harmless source
    // edits may rebuild a fragment, but no semantic edit can accidentally
    // reuse stale native code.
    fingerprint_text(format!(
        "regs={:?} entry={} blocks={:?} phase={:?} features={:?} cleanup={:?} flow={:?} invalid={}",
        function.register_types,
        function.entry,
        function.blocks,
        function.phase,
        function.features,
        function.return_cleanup,
        function.flow,
        function.invalid_analyses,
    ))
}

/// Build cache keys for independently emitted LLVM function fragments.
pub fn llvm_incremental_manifest(
    phases: &CompiledPhases,
    options: &LlvmOptions,
) -> LlvmIncrementalManifest {
    let interfaces = phases
        .mir
        .functions
        .iter()
        .map(|function| {
            (
                function.declaration,
                function_interface_fingerprint(function),
            )
        })
        .collect::<BTreeMap<_, _>>();
    // LLVM layout/runtime helpers inspect the artifact type table globally.
    // Treating it as a module ABI input keeps fragment reuse fail-closed until
    // type-level dependency slicing is available.
    let runtime_abi_fingerprint = fingerprint_text(format!(
        "types={:?};imports={:?};protocols={:?};handlers={:?}",
        phases.artifact.types,
        phases.artifact.imports,
        phases.artifact.protocols,
        phases.artifact.handler_defs,
    ));
    let functions = phases
        .mir
        .functions
        .iter()
        .map(|function| {
            let mut callees = function
                .blocks
                .iter()
                .filter_map(|block| known_direct_call_target(&block.terminator, function.declaration))
                .filter_map(|declaration| {
                    interfaces.get(&declaration).copied().map(|interface_fingerprint| {
                        LlvmCalleeDependency {
                            declaration,
                            interface_fingerprint,
                        }
                    })
                })
                .collect::<Vec<_>>();
            callees.sort();
            callees.dedup();
            let interface_fingerprint = interfaces[&function.declaration];
            let body_fingerprint = function_body_fingerprint(function);
            let fragment_fingerprint = fingerprint_text(format!(
                "schema={LLVM_INCREMENTAL_MANIFEST_SCHEMA};target={:?};layout={:?};entry={};allocation-limit={};runtime={runtime_abi_fingerprint};interface={interface_fingerprint};body={body_fingerprint};callees={callees:?}",
                options.target_triple,
                options.target_data_layout,
                options.emit_entry_wrapper,
                options.native_allocation_limit,
            ));
            LlvmFunctionManifest {
                declaration: function.declaration,
                interface_fingerprint,
                body_fingerprint,
                callee_interfaces: callees,
                fragment_fingerprint,
            }
        })
        .collect();
    LlvmIncrementalManifest {
        schema: LLVM_INCREMENTAL_MANIFEST_SCHEMA,
        target_triple: options.target_triple.clone(),
        target_data_layout: options.target_data_layout.clone(),
        emit_entry_wrapper: options.emit_entry_wrapper,
        native_allocation_limit: options.native_allocation_limit,
        runtime_abi_fingerprint,
        functions,
    }
}

fn effect_frame_tail_target(terminator: &Terminator) -> Option<u32> {
    match terminator {
        Terminator::TailCall { function, .. }
        | Terminator::TailCallKnownReceiver { function, .. } => Some(*function),
        Terminator::TailCallIndirect {
            known_function: Some(function),
            ..
        } => Some(*function),
        _ => None,
    }
}

fn known_direct_call_target(terminator: &Terminator, self_declaration: u32) -> Option<u32> {
    match terminator {
        Terminator::Call { function, .. }
        | Terminator::CallKnownReceiver { function, .. }
        | Terminator::TailCall { function, .. }
        | Terminator::TailCallKnownReceiver { function, .. } => Some(*function),
        Terminator::CallSelf { .. } | Terminator::TailCallSelf { .. } => Some(self_declaration),
        Terminator::CallIndirect {
            known_function: Some(function),
            ..
        }
        | Terminator::TailCallIndirect {
            known_function: Some(function),
            ..
        } => Some(*function),
        _ => None,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmModule {
    pub ir: String,
    pub target_triple: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmOptions {
    pub target_triple: String,
    pub target_data_layout: Option<String>,
    pub emit_entry_wrapper: bool,
    /// Embedded maximum size of one bytes/array native-runtime allocation.
    pub native_allocation_limit: u64,
}

impl Default for LlvmOptions {
    fn default() -> Self {
        let target_triple = default_target_triple();
        Self {
            target_data_layout: default_target_data_layout(&target_triple).map(str::to_owned),
            target_triple,
            emit_entry_wrapper: true,
            native_allocation_limit: DEFAULT_NATIVE_ALLOCATION_LIMIT,
        }
    }
}

pub fn default_target_triple() -> String {
    match (std::env::consts::ARCH, std::env::consts::OS) {
        ("x86_64", "linux") => "x86_64-unknown-linux-gnu",
        ("aarch64", "linux") => "aarch64-unknown-linux-gnu",
        ("x86_64", "macos") => "x86_64-apple-darwin",
        ("aarch64", "macos") => "arm64-apple-darwin",
        ("x86_64", "windows") => "x86_64-pc-windows-msvc",
        (arch, os) => return format!("{arch}-unknown-{os}"),
    }
    .into()
}

pub fn default_target_data_layout(target_triple: &str) -> Option<&'static str> {
    Some(match target_triple {
        "x86_64-unknown-linux-gnu" => {
            "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
        }
        "i686-unknown-linux-gnu" => "e-m:e-p:32:32-i64:64-i128:128-f80:128-n8:16:32-S128",
        "aarch64-unknown-linux-gnu" => "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128",
        "x86_64-apple-darwin" => "e-m:o-i64:64-i128:128-f80:128-n8:16:32:64-S128",
        "arm64-apple-darwin" => "e-m:o-i64:64-i128:128-n32:64-S128",
        "x86_64-pc-windows-msvc" => {
            "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
        }
        _ => return None,
    })
}

pub fn emit_llvm_ir(
    phases: &CompiledPhases,
    options: &LlvmOptions,
) -> Result<LlvmModule, Vec<Diagnostic>> {
    Emitter::new(phases, options).emit()
}

/// Emit a complete module while reusing only manifest-valid function bodies.
/// Module globals, runtime support, effects callbacks, and the entry wrapper
/// are always regenerated from the current phases.
pub fn emit_llvm_ir_with_fragment_cache(
    phases: &CompiledPhases,
    options: &LlvmOptions,
    cache: &mut LlvmFragmentCache,
) -> Result<LlvmModule, Vec<Diagnostic>> {
    Emitter::new(phases, options).emit_with_fragment_cache(cache)
}

struct Emitter<'a> {
    phases: &'a CompiledPhases,
    options: &'a LlvmOptions,
    output: String,
    temporary: u32,
    overflow_widths: BTreeSet<(u16, &'static str)>,
    byte_literals: BTreeMap<Vec<u8>, u32>,
    runtime_fault_literals: BTreeMap<Vec<u8>, u32>,
    uses_byte_runtime: bool,
    uses_array_runtime: bool,
    uses_callable_runtime: bool,
    uses_handler_runtime: bool,
    uses_effect_runtime: bool,
    host_imports: BTreeSet<HostImportRole>,
    snapshot_capture_fix_types: BTreeSet<TypeId>,
    llvm_reachable_functions: BTreeSet<usize>,
}

/// A function-local LLVM SSA name.  Keep generated names alphabetic rather
/// than numeric: numeric `%0` identifiers share LLVM's implicit numbering
/// space with unnamed blocks and parameters.
#[derive(Clone, Copy, Debug)]
struct Temporary(u32);

impl std::fmt::Display for Temporary {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "g1.tmp.{}", self.0)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum EffectRoutingMode {
    Initial,
    ReplayBorrowed,
    ReplayConditional(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct AggregateFieldLayout {
    nominal_index: usize,
    physical_index: usize,
    runtime_type: TypeId,
    owned_mask_index: usize,
}

impl EffectRoutingMode {
    fn preserves_clauses(&self) -> bool {
        matches!(self, Self::ReplayBorrowed)
    }
}

impl<'a> Emitter<'a> {
    fn new(phases: &'a CompiledPhases, options: &'a LlvmOptions) -> Self {
        Self {
            phases,
            options,
            output: String::new(),
            temporary: 0,
            overflow_widths: BTreeSet::new(),
            byte_literals: BTreeMap::new(),
            runtime_fault_literals: BTreeMap::new(),
            uses_byte_runtime: false,
            uses_array_runtime: false,
            uses_callable_runtime: false,
            uses_handler_runtime: false,
            uses_effect_runtime: false,
            host_imports: BTreeSet::new(),
            snapshot_capture_fix_types: BTreeSet::new(),
            llvm_reachable_functions: BTreeSet::new(),
        }
    }

    fn emit(self) -> Result<LlvmModule, Vec<Diagnostic>> {
        self.emit_inner(None)
    }

    fn emit_with_fragment_cache(
        self,
        cache: &mut LlvmFragmentCache,
    ) -> Result<LlvmModule, Vec<Diagnostic>> {
        self.emit_inner(Some(cache))
    }

    fn emit_inner(
        mut self,
        mut cache: Option<&mut LlvmFragmentCache>,
    ) -> Result<LlvmModule, Vec<Diagnostic>> {
        if let Some(cache) = cache.as_deref_mut() {
            cache.reused_fragments = 0;
        }
        let reachable = self.reachable_functions()?;
        self.llvm_reachable_functions = reachable.iter().copied().collect();
        self.prepare_runtime(&reachable)?;
        let manifest = cache
            .as_ref()
            .map(|_| llvm_incremental_manifest(self.phases, self.options));
        let invalidated = match (cache.as_ref(), manifest.as_ref()) {
            (Some(cache), Some(manifest)) => cache
                .manifest
                .as_ref()
                .map_or_else(BTreeSet::new, |previous| {
                    manifest.invalidated_functions(previous)
                }),
            _ => BTreeSet::new(),
        };
        self.line("; Grandiose LLVM backend");
        self.line(&format!(
            "target triple = \"{}\"",
            llvm_string(&self.options.target_triple)
        ));
        if let Some(layout) = &self.options.target_data_layout {
            self.line(&format!("target datalayout = \"{}\"", llvm_string(layout)));
        }
        self.line("");
        self.line("declare void @llvm.trap() cold noreturn nounwind");
        self.line(&runtime_fault_declaration(self.pointer_width()));
        for (bytes, index) in self.runtime_fault_literals.clone() {
            self.line(&format!(
                "@g1.runtime_fault.{index} = private constant [{} x i8] c\"{}\"",
                bytes.len(),
                llvm_bytes(&bytes)
            ));
        }
        if self.uses_byte_runtime {
            self.emit_byte_runtime();
        }
        if self.uses_array_runtime {
            self.emit_array_runtime();
        }
        if self.uses_callable_runtime {
            self.emit_callable_runtime();
        }
        if self.uses_handler_runtime {
            self.emit_handler_runtime();
        }
        if self.uses_effect_runtime {
            self.emit_effect_runtime();
        }
        if self.uses_effect_runtime && self.uses_handler_runtime {
            self.emit_handler_guard_drop_callbacks(&reachable)?;
        }
        self.emit_host_import_declarations();
        self.line("");

        for function in &reachable {
            let declaration = self.phases.mir.functions[*function].declaration;
            let fingerprint = manifest.as_ref().and_then(|manifest| {
                manifest
                    .functions
                    .iter()
                    .find(|entry| entry.declaration == declaration)
                    .map(|entry| entry.fragment_fingerprint)
            });
            let cached = cache.as_deref_mut().and_then(|cache| {
                (!invalidated.contains(&declaration))
                    .then(|| cache.fragments.get(&declaration))
                    .flatten()
                    .filter(|fragment| Some(fragment.fingerprint) == fingerprint)
                    .cloned()
            });
            if let Some(fragment) = cached {
                self.output.push_str(&fragment.emitted_text);
                self.overflow_widths.extend(fragment.overflow_widths);
                self.snapshot_capture_fix_types
                    .extend(fragment.snapshot_capture_fix_types);
                if let Some(cache) = cache.as_deref_mut() {
                    cache.reused_fragments = cache.reused_fragments.saturating_add(1);
                }
                continue;
            }

            // SSA temporary names are function-local. Reset them for every
            // fragment so fresh and reused emission have identical canonical
            // text, then isolate all per-function side metadata for replay.
            let module_output = std::mem::take(&mut self.output);
            let module_overflow_widths = std::mem::take(&mut self.overflow_widths);
            let module_snapshot_capture_fix_types =
                std::mem::take(&mut self.snapshot_capture_fix_types);
            self.temporary = 0;
            self.emit_function(*function)?;
            let emitted_text = std::mem::take(&mut self.output);
            let overflow_widths = std::mem::take(&mut self.overflow_widths);
            let snapshot_capture_fix_types = std::mem::take(&mut self.snapshot_capture_fix_types);
            self.output = module_output;
            self.overflow_widths = module_overflow_widths;
            self.snapshot_capture_fix_types = module_snapshot_capture_fix_types;
            self.output.push_str(&emitted_text);
            self.overflow_widths.extend(overflow_widths.iter().copied());
            self.snapshot_capture_fix_types
                .extend(snapshot_capture_fix_types.iter().copied());
            if let (Some(cache), Some(fingerprint)) = (cache.as_deref_mut(), fingerprint) {
                cache.fragments.insert(
                    declaration,
                    LlvmFunctionFragment {
                        fingerprint,
                        emitted_text,
                        overflow_widths,
                        snapshot_capture_fix_types,
                    },
                );
            }
        }
        if self.uses_effect_runtime {
            self.emit_snapshot_capture_fix_callbacks(&reachable)?;
        }
        if self.options.emit_entry_wrapper {
            self.emit_entry_wrapper(&reachable)?;
        }

        let declarations = self
            .overflow_widths
            .iter()
            .map(|(width, operation)| {
                format!(
                    "declare {{ i{width}, i1 }} @llvm.{operation}.with.overflow.i{width}(i{width}, i{width}) nounwind readnone"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        if !declarations.is_empty() {
            self.output.push_str(&declarations);
            self.output.push('\n');
        }
        if let (Some(cache), Some(manifest)) = (cache, manifest) {
            cache.manifest = Some(manifest);
            cache.fragments.retain(|declaration, _| {
                self.phases
                    .mir
                    .functions
                    .iter()
                    .any(|function| function.declaration == *declaration)
            });
        }
        Ok(LlvmModule {
            ir: self.output,
            target_triple: self.options.target_triple.clone(),
        })
    }

    fn reachable_functions(&self) -> Result<Vec<usize>, Vec<Diagnostic>> {
        let Some(entry) = self
            .phases
            .mir
            .functions
            .iter()
            .position(|function| function.name == "main")
        else {
            return Err(vec![backend_error(
                "LLVM emission requires a source `main` function",
            )]);
        };
        let mut pending = vec![entry];
        let mut reachable = BTreeSet::new();
        while let Some(index) = pending.pop() {
            if !reachable.insert(index) {
                continue;
            }
            let Some(function) = self.phases.mir.functions.get(index) else {
                return Err(vec![backend_error(format!(
                    "MIR references missing function {index}"
                ))]);
            };
            for ty in function
                .register_types
                .iter()
                .chain(function.params.iter())
                .chain(std::iter::once(&function.result))
            {
                self.collect_drop_glue_functions(*ty, &mut BTreeSet::new(), &mut pending)?;
            }
            for block in &function.blocks {
                for instruction in &block.statements {
                    if let InstructionKind::MakeCallable {
                        function: target, ..
                    } = &instruction.kind
                    {
                        pending.push(*target as usize);
                    }
                    if let InstructionKind::MakeHandlerShared { functions, .. } = &instruction.kind
                    {
                        pending.extend(functions.iter().map(|function| *function as usize));
                    }
                }
                match &block.terminator {
                    Terminator::Call {
                        function,
                        normal: _,
                        ..
                    }
                    | Terminator::TailCall { function, .. }
                    | Terminator::CallKnownReceiver { function, .. }
                    | Terminator::TailCallKnownReceiver { function, .. } => {
                        pending.push(*function as usize);
                    }
                    Terminator::CallIndirect {
                        known_function: Some(function),
                        ..
                    }
                    | Terminator::TailCallIndirect {
                        known_function: Some(function),
                        ..
                    } => pending.push(*function as usize),
                    _ => {}
                }
            }
        }
        Ok(reachable.into_iter().collect())
    }

    fn collect_drop_glue_functions(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
        pending: &mut Vec<usize>,
    ) -> Result<(), Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(());
        }
        if let Some(glue) = self
            .phases
            .artifact
            .drop_glue
            .iter()
            .find(|glue| glue.ty == ty)
        {
            pending.push(glue.function as usize);
        }
        match self.runtime_type(ty)? {
            Type::Array { element } => {
                self.collect_drop_glue_functions(*element, visiting, pending)?;
            }
            Type::Callable { capture_type, .. }
            | Type::Handler { capture_type, .. }
            | Type::BindingPack {
                payload_type: capture_type,
                ..
            } => {
                self.collect_drop_glue_functions(*capture_type, visiting, pending)?;
            }
            Type::Tuple { fields, .. } => {
                for field in fields {
                    self.collect_drop_glue_functions(*field, visiting, pending)?;
                }
            }
            Type::Struct { fields, .. } => {
                for field in fields {
                    self.collect_drop_glue_functions(field.ty, visiting, pending)?;
                }
            }
            Type::Enum { variants, .. } => {
                for field in variants.iter().flat_map(|variant| &variant.fields) {
                    self.collect_drop_glue_functions(field.ty, visiting, pending)?;
                }
            }
            _ => {}
        }
        visiting.remove(&ty);
        Ok(())
    }

    fn prepare_runtime(&mut self, reachable: &[usize]) -> Result<(), Vec<Diagnostic>> {
        let mut literals = BTreeSet::new();
        let mut runtime_fault_literals = BTreeSet::new();
        for &index in reachable {
            let function = &self.phases.mir.functions[index];
            for &ty in function
                .register_types
                .iter()
                .chain(function.params.iter())
                .chain(std::iter::once(&function.result))
            {
                self.uses_byte_runtime |=
                    self.type_contains_byte_object(ty, &mut BTreeSet::new())?;
                self.uses_array_runtime |= self.type_contains_array(ty, &mut BTreeSet::new())?;
                self.uses_callable_runtime |=
                    self.type_contains_callable(ty, &mut BTreeSet::new())?;
                self.uses_handler_runtime |=
                    self.type_contains_handler(ty, &mut BTreeSet::new())?;
                self.uses_effect_runtime |=
                    self.type_contains_resumption(ty, &mut BTreeSet::new())?;
            }
            let needs_effect_frame = self.function_needs_effect_frame(function);
            self.uses_effect_runtime |= needs_effect_frame;
            // Every directly callable effect-frame function gets a request
            // router. The router walks the active handler chain even when
            // optimized MIR contains neither a handler-typed register nor a
            // local MakeHandler instruction.
            self.uses_handler_runtime |= needs_effect_frame;
            for block in &function.blocks {
                self.uses_handler_runtime |= block.statements.iter().any(|instruction| {
                    matches!(
                        instruction.kind,
                        InstructionKind::MakeHandler { .. }
                            | InstructionKind::MakeHandlerShared { .. }
                    )
                });
                self.uses_handler_runtime |= matches!(
                    block.terminator,
                    Terminator::Handle { .. }
                        | Terminator::Perform { .. }
                        | Terminator::Resume { .. }
                        | Terminator::TailResume { .. }
                        | Terminator::Cancel { .. }
                );
                if let Terminator::HostCall { import, .. } = &block.terminator {
                    self.host_imports.insert(*import);
                }
                if let Terminator::Abort {
                    message: Some(message),
                } = &block.terminator
                {
                    runtime_fault_literals.insert(message.as_bytes().to_vec());
                }
                for instruction in &block.statements {
                    if let InstructionKind::Const { value, .. } = &instruction.kind {
                        match value {
                            Constant::Text(value) => {
                                literals.insert(value.as_bytes().to_vec());
                            }
                            Constant::Bytes(value) => {
                                literals.insert(value.clone());
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        self.byte_literals = literals
            .into_iter()
            .enumerate()
            .map(|(index, bytes)| (bytes, index as u32))
            .collect();
        self.runtime_fault_literals = runtime_fault_literals
            .into_iter()
            .enumerate()
            .map(|(index, bytes)| (bytes, index as u32))
            .collect();
        Ok(())
    }

    fn function_needs_effect_frame(&self, function: &mir::Function) -> bool {
        let is_seed = |function: &mir::Function| {
            !function.outward_protocols.is_empty()
                || function
                    .blocks
                    .iter()
                    .any(|block| matches!(block.terminator, Terminator::Handle { .. }))
        };
        if is_seed(function) {
            return true;
        }
        let mut pending = function
            .blocks
            .iter()
            .filter_map(|block| effect_frame_tail_target(&block.terminator))
            .collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(target) = pending.pop() {
            if target == function.declaration {
                // A direct tail-call cycle is a stackless source loop even
                // when it performs no effects. Route the SCC through the same
                // heap-frame scheduler used by effects so native stack safety
                // does not depend on target-specific tail-call eligibility.
                return true;
            }
            if !visited.insert(target) {
                continue;
            }
            let Some(target) = self.phases.mir.functions.get(target as usize) else {
                continue;
            };
            if is_seed(target) {
                return true;
            }
            pending.extend(
                target
                    .blocks
                    .iter()
                    .filter_map(|block| effect_frame_tail_target(&block.terminator)),
            );
        }
        // A source recursion cycle can mix terminal and ordinary calls. If
        // only its tail-call members are framed, an ordinary member invokes a
        // fresh scheduler wrapper on every trip around the cycle and still
        // exhausts the native stack. Frame every member of a statically known
        // direct-call SCC so ordinary calls become heap-frame continuations in
        // the existing scheduler.
        let mut pending = function
            .blocks
            .iter()
            .filter_map(|block| known_direct_call_target(&block.terminator, function.declaration))
            .collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(target) = pending.pop() {
            if target == function.declaration {
                return true;
            }
            if !visited.insert(target) {
                continue;
            }
            let Some(target) = self.phases.mir.functions.get(target as usize) else {
                continue;
            };
            pending.extend(target.blocks.iter().filter_map(|block| {
                known_direct_call_target(&block.terminator, target.declaration)
            }));
        }
        false
    }

    fn emit_host_import_declarations(&mut self) {
        let imports = self.host_imports.iter().copied().collect::<Vec<_>>();
        if !imports.is_empty() {
            self.line("declare void @g1_host_fault(i32) cold noreturn");
        }
        for import in imports {
            match import {
                HostImportRole::ProcessArgsGet => {
                    self.line("declare void @g1_host_process_init(i32, ptr)");
                    self.line("declare ptr @g1_host_process_args_get()");
                }
                HostImportRole::FsRead => {
                    self.line("declare ptr @g1_host_fs_read(ptr)");
                }
                HostImportRole::FsWrite => {
                    self.line("declare i32 @g1_host_fs_write(ptr, ptr)");
                }
                HostImportRole::DiagnosticWrite => {
                    self.line("declare i32 @g1_host_diagnostic_write(ptr)");
                }
            }
        }
    }

    fn emit_byte_runtime(&mut self) {
        let usize_ty = format!("i{}", self.pointer_width());
        self.overflow_widths.insert((self.pointer_width(), "uadd"));
        self.line(&format!("%g1.bytes = type {{ i64, {usize_ty}, [0 x i8] }}"));
        let literals = self
            .byte_literals
            .iter()
            .map(|(bytes, index)| (bytes.clone(), *index))
            .collect::<Vec<_>>();
        for (bytes, index) in literals {
            self.line(&format!(
                "@g1.bytes.{index} = private constant {{ i64, {usize_ty}, [{} x i8] }} {{ i64 -1, {usize_ty} {}, [{} x i8] c\"{}\" }}, align 8",
                bytes.len(),
                bytes.len(),
                bytes.len(),
                llvm_bytes(&bytes)
            ));
        }
        self.line(&format!("declare ptr @malloc({usize_ty})"));
        self.line("declare void @free(ptr)");
        self.line(&format!(
            "declare void @llvm.memcpy.p0.p0.{usize_ty}(ptr nocapture writeonly, ptr nocapture readonly, {usize_ty}, i1 immarg)"
        ));
        self.line(&format!("declare i32 @memcmp(ptr, ptr, {usize_ty})"));
        self.line("");
        self.line("define internal void @g1_bytes_retain(ptr %object) {");
        self.line("entry:");
        self.line("  %count.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 0");
        self.line("  %count = load i64, ptr %count.address");
        self.line("  %immortal = icmp eq i64 %count, -1");
        self.line("  br i1 %immortal, label %return, label %owned");
        self.line("owned:");
        self.line("  %incremented = add i64 %count, 1");
        self.line("  store i64 %incremented, ptr %count.address");
        self.line("  br label %return");
        self.line("return:");
        self.line("  ret void");
        self.line("}");
        self.line("");
        self.line("define internal void @g1_bytes_release(ptr %object) {");
        self.line("entry:");
        self.line("  %count.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 0");
        self.line("  %count = load i64, ptr %count.address");
        self.line("  %immortal = icmp eq i64 %count, -1");
        self.line("  br i1 %immortal, label %return, label %owned");
        self.line("owned:");
        self.line("  %last = icmp eq i64 %count, 1");
        self.line("  br i1 %last, label %destroy, label %decrement");
        self.line("decrement:");
        self.line("  %next = sub i64 %count, 1");
        self.line("  store i64 %next, ptr %count.address");
        self.line("  br label %return");
        self.line("destroy:");
        self.line("  call void @free(ptr %object)");
        self.line("  br label %return");
        self.line("return:");
        self.line("  ret void");
        self.line("}");
        self.line("");
        self.line(&format!(
            "define internal ptr @g1_bytes_allocate({usize_ty} %length) {{"
        ));
        self.line("entry:");
        self.line(&format!(
            "  %end = getelementptr %g1.bytes, ptr null, {usize_ty} 1"
        ));
        self.line(&format!("  %header = ptrtoint ptr %end to {usize_ty}"));
        self.line(&format!(
            "  %size.pair = call {{ {usize_ty}, i1 }} @llvm.uadd.with.overflow.{usize_ty}({usize_ty} %header, {usize_ty} %length)"
        ));
        self.line(&format!(
            "  %size = extractvalue {{ {usize_ty}, i1 }} %size.pair, 0"
        ));
        self.line(&format!(
            "  %size.overflow = extractvalue {{ {usize_ty}, i1 }} %size.pair, 1"
        ));
        self.line("  br i1 %size.overflow, label %size.overflow.fault, label %limit.check");
        self.line("size.overflow.fault:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_OVERFLOW, "0", "0", "null", "0");
        self.line("limit.check:");
        self.line(&format!(
            "  %over.limit = icmp ugt {usize_ty} %length, {}",
            self.options.native_allocation_limit,
        ));
        self.line("  br i1 %over.limit, label %limit.fault, label %allocate");
        self.line("limit.fault:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_LIMIT, "0", "0", "null", "0");
        self.line("allocate:");
        self.line(&format!("  %object = call ptr @malloc({usize_ty} %size)"));
        self.line("  %allocation.failed = icmp eq ptr %object, null");
        self.line("  br i1 %allocation.failed, label %allocation.trap, label %allocation.ready");
        self.line("allocation.trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_LIMIT, "0", "0", "null", "0");
        self.line("allocation.ready:");
        self.line("  %count.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 0");
        self.line("  store i64 1, ptr %count.address");
        self.line(
            "  %length.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 1",
        );
        self.line(&format!("  store {usize_ty} %length, ptr %length.address"));
        self.line("  ret ptr %object");
        self.line("}");
        self.line("");
        self.line("define internal ptr @g1_bytes_data(ptr %object) {");
        self.line("entry:");
        self.line("  %data = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 2, i32 0");
        self.line("  ret ptr %data");
        self.line("}");
        self.line("");
        self.line("define internal i32 @g1_bytes_equal(ptr %left, ptr %right) {");
        self.line("entry:");
        self.line(
            "  %left.length.address = getelementptr inbounds %g1.bytes, ptr %left, i32 0, i32 1",
        );
        self.line(&format!(
            "  %left.length = load {usize_ty}, ptr %left.length.address"
        ));
        self.line(
            "  %right.length.address = getelementptr inbounds %g1.bytes, ptr %right, i32 0, i32 1",
        );
        self.line(&format!(
            "  %right.length = load {usize_ty}, ptr %right.length.address"
        ));
        self.line(&format!(
            "  %same.length = icmp eq {usize_ty} %left.length, %right.length"
        ));
        self.line("  br i1 %same.length, label %compare, label %different");
        self.line("compare:");
        self.line("  %left.data = call ptr @g1_bytes_data(ptr %left)");
        self.line("  %right.data = call ptr @g1_bytes_data(ptr %right)");
        self.line(&format!(
            "  %ordering = call i32 @memcmp(ptr %left.data, ptr %right.data, {usize_ty} %left.length)"
        ));
        self.line("  %same.bytes = icmp eq i32 %ordering, 0");
        self.line("  %same = zext i1 %same.bytes to i32");
        self.line("  ret i32 %same");
        self.line("different:");
        self.line("  ret i32 0");
        self.line("}");
        self.emit_utf8_runtime();
    }

    fn emit_utf8_runtime(&mut self) {
        let usize_ty = format!("i{}", self.pointer_width());
        self.line("");
        self.line(&format!(
            "define internal {usize_ty} @g1_utf8_valid_up_to(ptr %object) {{"
        ));
        self.line("entry:");
        self.line(
            "  %length.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 1",
        );
        self.line(&format!("  %length = load {usize_ty}, ptr %length.address"));
        self.line("  %data = call ptr @g1_bytes_data(ptr %object)");
        self.line("  br label %loop");
        self.line("loop:");
        self.line(&format!(
            "  %index = phi {usize_ty} [ 0, %entry ], [ %next.1, %accept.1 ], [ %next.2, %accept.2 ], [ %next.3, %accept.3 ], [ %next.4, %accept.4 ]"
        ));
        self.line(&format!("  %done = icmp eq {usize_ty} %index, %length"));
        self.line("  br i1 %done, label %valid, label %read");
        self.line("read:");
        self.line(&format!(
            "  %first.address = getelementptr inbounds i8, ptr %data, {usize_ty} %index"
        ));
        self.line("  %first = load i8, ptr %first.address");
        self.line("  %ascii = icmp ult i8 %first, -128");
        self.line("  br i1 %ascii, label %accept.1, label %classify.2");
        self.line("classify.2:");
        self.line("  %at.least.c2 = icmp uge i8 %first, -62");
        self.line("  %at.most.df = icmp ule i8 %first, -33");
        self.line("  %is.2 = and i1 %at.least.c2, %at.most.df");
        self.line("  br i1 %is.2, label %check.2, label %classify.3");
        self.line("classify.3:");
        self.line("  %at.least.e0 = icmp uge i8 %first, -32");
        self.line("  %at.most.ef = icmp ule i8 %first, -17");
        self.line("  %is.3 = and i1 %at.least.e0, %at.most.ef");
        self.line("  br i1 %is.3, label %check.3, label %classify.4");
        self.line("classify.4:");
        self.line("  %at.least.f0 = icmp uge i8 %first, -16");
        self.line("  %at.most.f4 = icmp ule i8 %first, -12");
        self.line("  %is.4 = and i1 %at.least.f0, %at.most.f4");
        self.line("  br i1 %is.4, label %check.4, label %invalid");
        self.line("check.2:");
        self.line(&format!("  %remaining.2 = sub {usize_ty} %length, %index"));
        self.line(&format!(
            "  %enough.2 = icmp uge {usize_ty} %remaining.2, 2"
        ));
        self.line("  br i1 %enough.2, label %bytes.2, label %invalid");
        self.line("bytes.2:");
        self.line(&format!("  %second.index.2 = add {usize_ty} %index, 1"));
        self.line(&format!(
            "  %second.address.2 = getelementptr inbounds i8, ptr %data, {usize_ty} %second.index.2"
        ));
        self.line("  %second.2 = load i8, ptr %second.address.2");
        self.line("  %second.valid.2 = icmp slt i8 %second.2, -64");
        self.line("  br i1 %second.valid.2, label %accept.2, label %invalid");
        self.line("check.3:");
        self.line(&format!("  %remaining.3 = sub {usize_ty} %length, %index"));
        self.line(&format!(
            "  %enough.3 = icmp uge {usize_ty} %remaining.3, 3"
        ));
        self.line("  br i1 %enough.3, label %bytes.3, label %invalid");
        self.line("bytes.3:");
        self.line(&format!("  %second.index.3 = add {usize_ty} %index, 1"));
        self.line(&format!("  %third.index.3 = add {usize_ty} %index, 2"));
        self.line(&format!(
            "  %second.address.3 = getelementptr inbounds i8, ptr %data, {usize_ty} %second.index.3"
        ));
        self.line(&format!(
            "  %third.address.3 = getelementptr inbounds i8, ptr %data, {usize_ty} %third.index.3"
        ));
        self.line("  %second.3 = load i8, ptr %second.address.3");
        self.line("  %third.3 = load i8, ptr %third.address.3");
        self.line("  %second.cont.3 = icmp slt i8 %second.3, -64");
        self.line("  %third.cont.3 = icmp slt i8 %third.3, -64");
        self.line("  %continuations.3 = and i1 %second.cont.3, %third.cont.3");
        self.line("  %is.e0 = icmp eq i8 %first, -32");
        self.line("  %not.e0 = xor i1 %is.e0, true");
        self.line("  %e0.second = icmp uge i8 %second.3, -96");
        self.line("  %not.overlong.3 = or i1 %e0.second, %not.e0");
        self.line("  %is.ed = icmp eq i8 %first, -19");
        self.line("  %not.ed = xor i1 %is.ed, true");
        self.line("  %ed.second = icmp ule i8 %second.3, -97");
        self.line("  %not.surrogate = or i1 %ed.second, %not.ed");
        self.line("  %canonical.3 = and i1 %not.overlong.3, %not.surrogate");
        self.line("  %valid.3 = and i1 %continuations.3, %canonical.3");
        self.line("  br i1 %valid.3, label %accept.3, label %invalid");
        self.line("check.4:");
        self.line(&format!("  %remaining.4 = sub {usize_ty} %length, %index"));
        self.line(&format!(
            "  %enough.4 = icmp uge {usize_ty} %remaining.4, 4"
        ));
        self.line("  br i1 %enough.4, label %bytes.4, label %invalid");
        self.line("bytes.4:");
        for (name, offset) in [("second", 1), ("third", 2), ("fourth", 3)] {
            self.line(&format!(
                "  %{name}.index.4 = add {usize_ty} %index, {offset}"
            ));
            self.line(&format!(
                "  %{name}.address.4 = getelementptr inbounds i8, ptr %data, {usize_ty} %{name}.index.4"
            ));
            self.line(&format!("  %{name}.4 = load i8, ptr %{name}.address.4"));
            self.line(&format!("  %{name}.cont.4 = icmp slt i8 %{name}.4, -64"));
        }
        self.line("  %last.cont.4 = and i1 %third.cont.4, %fourth.cont.4");
        self.line("  %continuations.4 = and i1 %second.cont.4, %last.cont.4");
        self.line("  %is.f0 = icmp eq i8 %first, -16");
        self.line("  %not.f0 = xor i1 %is.f0, true");
        self.line("  %f0.second = icmp uge i8 %second.4, -112");
        self.line("  %not.overlong.4 = or i1 %f0.second, %not.f0");
        self.line("  %is.f4 = icmp eq i8 %first, -12");
        self.line("  %not.f4 = xor i1 %is.f4, true");
        self.line("  %f4.second = icmp ule i8 %second.4, -113");
        self.line("  %not.too.large = or i1 %f4.second, %not.f4");
        self.line("  %canonical.4 = and i1 %not.overlong.4, %not.too.large");
        self.line("  %valid.4 = and i1 %continuations.4, %canonical.4");
        self.line("  br i1 %valid.4, label %accept.4, label %invalid");
        for (suffix, width) in [(1, 1), (2, 2), (3, 3), (4, 4)] {
            self.line(&format!("accept.{suffix}:"));
            self.line(&format!(
                "  %next.{suffix} = add {usize_ty} %index, {width}"
            ));
            self.line("  br label %loop");
        }
        self.line("valid:");
        self.line(&format!("  ret {usize_ty} %length"));
        self.line("invalid:");
        self.line(&format!("  ret {usize_ty} %index"));
        self.line("}");
        self.line("");
        self.line("define internal i1 @g1_utf8_validate(ptr %object) {");
        self.line("entry:");
        self.line(
            "  %length.address = getelementptr inbounds %g1.bytes, ptr %object, i32 0, i32 1",
        );
        self.line(&format!("  %length = load {usize_ty}, ptr %length.address"));
        self.line(&format!(
            "  %valid.up.to = call {usize_ty} @g1_utf8_valid_up_to(ptr %object)"
        ));
        self.line(&format!(
            "  %valid = icmp eq {usize_ty} %valid.up.to, %length"
        ));
        self.line("  ret i1 %valid");
        self.line("}");
    }

    fn emit_array_runtime(&mut self) {
        let usize_ty = format!("i{}", self.pointer_width());
        self.overflow_widths.insert((self.pointer_width(), "umul"));
        self.overflow_widths.insert((self.pointer_width(), "uadd"));
        self.line(&format!(
            "%g1.array = type {{ {usize_ty}, {usize_ty}, {usize_ty}, ptr, ptr }}"
        ));
        if !self.uses_byte_runtime {
            self.line(&format!("declare ptr @malloc({usize_ty})"));
            self.line("declare void @free(ptr)");
        }
        self.line(&format!("declare ptr @realloc(ptr, {usize_ty})"));
        self.line(&format!(
            "declare void @llvm.memset.p0.{usize_ty}(ptr nocapture writeonly, i8, {usize_ty}, i1 immarg)"
        ));
        self.line("");
        self.line(&format!(
            "define internal ptr @g1_array_allocate({usize_ty} %capacity, {usize_ty} %element.size) {{"
        ));
        self.line("entry:");
        self.line(&format!(
            "  %header.end = getelementptr %g1.array, ptr null, {usize_ty} 1"
        ));
        self.line(&format!(
            "  %header.size = ptrtoint ptr %header.end to {usize_ty}"
        ));
        self.line(&format!(
            "  %array = call ptr @malloc({usize_ty} %header.size)"
        ));
        self.line("  %header.failed = icmp eq ptr %array, null");
        self.line("  br i1 %header.failed, label %header.trap, label %header.ready");
        self.line("header.trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_LIMIT, "0", "0", "null", "0");
        self.line("header.ready:");
        self.line("  %length.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 0");
        self.line(&format!("  store {usize_ty} 0, ptr %length.address"));
        self.line(
            "  %capacity.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 1",
        );
        self.line(&format!(
            "  store {usize_ty} %capacity, ptr %capacity.address"
        ));
        self.line(
            "  %element.size.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 2",
        );
        self.line(&format!(
            "  store {usize_ty} %element.size, ptr %element.size.address"
        ));
        self.line(&format!("  %empty = icmp eq {usize_ty} %capacity, 0"));
        self.line("  br i1 %empty, label %zero, label %allocate");
        self.line("zero:");
        self.line("  br label %finish");
        self.line("allocate:");
        self.line(&format!(
            "  %size.pair = call {{ {usize_ty}, i1 }} @llvm.umul.with.overflow.{usize_ty}({usize_ty} %capacity, {usize_ty} %element.size)"
        ));
        self.line(&format!(
            "  %data.size = extractvalue {{ {usize_ty}, i1 }} %size.pair, 0"
        ));
        self.line(&format!(
            "  %size.overflow = extractvalue {{ {usize_ty}, i1 }} %size.pair, 1"
        ));
        self.line("  br i1 %size.overflow, label %trap, label %allocate.storage");
        self.line("trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_OVERFLOW, "0", "0", "null", "0");
        self.line("allocate.storage:");
        self.line(&format!(
            "  %total.pair = call {{ {usize_ty}, i1 }} @llvm.uadd.with.overflow.{usize_ty}({usize_ty} %data.size, {usize_ty} %capacity)"
        ));
        self.line(&format!(
            "  %total.size = extractvalue {{ {usize_ty}, i1 }} %total.pair, 0"
        ));
        self.line(&format!(
            "  %total.overflow = extractvalue {{ {usize_ty}, i1 }} %total.pair, 1"
        ));
        self.line("  br i1 %total.overflow, label %total.overflow.trap, label %limit.check");
        self.line("total.overflow.trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_OVERFLOW, "0", "0", "null", "0");
        self.line("limit.check:");
        self.line(&format!(
            "  %over.limit = icmp ugt {usize_ty} %total.size, {}",
            self.options.native_allocation_limit,
        ));
        self.line("  br i1 %over.limit, label %limit.trap, label %allocate.storage.checked");
        self.line("limit.trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_LIMIT, "0", "0", "null", "0");
        self.line("allocate.storage.checked:");
        self.line(&format!(
            "  %data = call ptr @malloc({usize_ty} %data.size)"
        ));
        self.line(&format!(
            "  %initialized = call ptr @malloc({usize_ty} %capacity)"
        ));
        self.line("  %data.failed = icmp eq ptr %data, null");
        self.line("  %initialized.failed = icmp eq ptr %initialized, null");
        self.line("  %storage.failed = or i1 %data.failed, %initialized.failed");
        self.line("  br i1 %storage.failed, label %storage.trap, label %initialize.storage");
        self.line("storage.trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_LIMIT, "0", "0", "null", "0");
        self.line("initialize.storage:");
        self.line(&format!(
            "  call void @llvm.memset.p0.{usize_ty}(ptr %initialized, i8 0, {usize_ty} %capacity, i1 false)"
        ));
        self.line("  br label %finish");
        self.line("finish:");
        self.line("  %final.data = phi ptr [ null, %zero ], [ %data, %initialize.storage ]");
        self.line(
            "  %final.initialized = phi ptr [ null, %zero ], [ %initialized, %initialize.storage ]",
        );
        self.line("  %data.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 3");
        self.line("  store ptr %final.data, ptr %data.address");
        self.line(
            "  %initialized.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 4",
        );
        self.line("  store ptr %final.initialized, ptr %initialized.address");
        self.line("  ret ptr %array");
        self.line("}");
        self.line("");
        self.line(&format!(
            "define internal void @g1_array_grow(ptr %array, {usize_ty} %required) {{"
        ));
        self.line("entry:");
        self.line(
            "  %capacity.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 1",
        );
        self.line(&format!(
            "  %capacity = load {usize_ty}, ptr %capacity.address"
        ));
        self.line(&format!(
            "  %enough = icmp uge {usize_ty} %capacity, %required"
        ));
        self.line("  br i1 %enough, label %return, label %grow");
        self.line("grow:");
        self.line(&format!(
            "  %double.pair = call {{ {usize_ty}, i1 }} @llvm.uadd.with.overflow.{usize_ty}({usize_ty} %capacity, {usize_ty} %capacity)"
        ));
        self.line(&format!(
            "  %doubled = extractvalue {{ {usize_ty}, i1 }} %double.pair, 0"
        ));
        self.line(&format!(
            "  %double.overflow = extractvalue {{ {usize_ty}, i1 }} %double.pair, 1"
        ));
        self.line(&format!("  %minimum = icmp ult {usize_ty} %doubled, 1"));
        self.line(&format!(
            "  %at.least.one = select i1 %minimum, {usize_ty} 1, {usize_ty} %doubled"
        ));
        self.line(&format!(
            "  %below.required = icmp ult {usize_ty} %at.least.one, %required"
        ));
        self.line(&format!(
            "  %grown = select i1 %below.required, {usize_ty} %required, {usize_ty} %at.least.one"
        ));
        self.line(&format!(
            "  %new.capacity = select i1 %double.overflow, {usize_ty} %required, {usize_ty} %grown"
        ));
        self.line(
            "  %element.size.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 2",
        );
        self.line(&format!(
            "  %element.size = load {usize_ty}, ptr %element.size.address"
        ));
        self.line(&format!(
            "  %size.pair = call {{ {usize_ty}, i1 }} @llvm.umul.with.overflow.{usize_ty}({usize_ty} %new.capacity, {usize_ty} %element.size)"
        ));
        self.line(&format!(
            "  %data.size = extractvalue {{ {usize_ty}, i1 }} %size.pair, 0"
        ));
        self.line(&format!(
            "  %size.overflow = extractvalue {{ {usize_ty}, i1 }} %size.pair, 1"
        ));
        self.line("  br i1 %size.overflow, label %trap, label %resize");
        self.line("trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_OVERFLOW, "0", "0", "null", "0");
        self.line("resize:");
        self.line(&format!(
            "  %total.pair = call {{ {usize_ty}, i1 }} @llvm.uadd.with.overflow.{usize_ty}({usize_ty} %data.size, {usize_ty} %new.capacity)"
        ));
        self.line(&format!(
            "  %total.size = extractvalue {{ {usize_ty}, i1 }} %total.pair, 0"
        ));
        self.line(&format!(
            "  %total.overflow = extractvalue {{ {usize_ty}, i1 }} %total.pair, 1"
        ));
        self.line("  br i1 %total.overflow, label %total.overflow.trap, label %limit.check");
        self.line("total.overflow.trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_OVERFLOW, "0", "0", "null", "0");
        self.line("limit.check:");
        self.line(&format!(
            "  %over.limit = icmp ugt {usize_ty} %total.size, {}",
            self.options.native_allocation_limit,
        ));
        self.line("  br i1 %over.limit, label %limit.trap, label %resize.checked");
        self.line("limit.trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_LIMIT, "0", "0", "null", "0");
        self.line("resize.checked:");
        self.line("  %data.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 3");
        self.line("  %data = load ptr, ptr %data.address");
        self.line(&format!(
            "  %new.data = call ptr @realloc(ptr %data, {usize_ty} %data.size)"
        ));
        self.line("  %data.failed = icmp eq ptr %new.data, null");
        self.line("  br i1 %data.failed, label %allocation.trap, label %data.ready");
        self.line("allocation.trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_LIMIT, "0", "0", "null", "0");
        self.line("data.ready:");
        self.line("  store ptr %new.data, ptr %data.address");
        self.line(
            "  %initialized.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 4",
        );
        self.line("  %initialized = load ptr, ptr %initialized.address");
        self.line(&format!(
            "  %new.initialized = call ptr @realloc(ptr %initialized, {usize_ty} %new.capacity)"
        ));
        self.line("  %initialized.failed = icmp eq ptr %new.initialized, null");
        self.line("  br i1 %initialized.failed, label %initialized.trap, label %initialized.ready");
        self.line("initialized.trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_LIMIT, "0", "0", "null", "0");
        self.line("initialized.ready:");
        self.line(&format!(
            "  %added = sub {usize_ty} %new.capacity, %capacity"
        ));
        self.line(&format!(
            "  %new.initialized.start = getelementptr inbounds i8, ptr %new.initialized, {usize_ty} %capacity"
        ));
        self.line(&format!(
            "  call void @llvm.memset.p0.{usize_ty}(ptr %new.initialized.start, i8 0, {usize_ty} %added, i1 false)"
        ));
        self.line("  store ptr %new.initialized, ptr %initialized.address");
        self.line(&format!(
            "  store {usize_ty} %new.capacity, ptr %capacity.address"
        ));
        self.line("  br label %return");
        self.line("return:");
        self.line("  ret void");
        self.line("}");
        self.line("");
        self.line("define internal void @g1_array_free(ptr %array) {");
        self.line("entry:");
        self.line("  %data.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 3");
        self.line("  %data = load ptr, ptr %data.address");
        self.line("  call void @free(ptr %data)");
        self.line(
            "  %initialized.address = getelementptr inbounds %g1.array, ptr %array, i32 0, i32 4",
        );
        self.line("  %initialized = load ptr, ptr %initialized.address");
        self.line("  call void @free(ptr %initialized)");
        self.line("  call void @free(ptr %array)");
        self.line("  ret void");
        self.line("}");
    }

    fn emit_callable_runtime(&mut self) {
        let usize_ty = format!("i{}", self.pointer_width());
        self.line("%g1.capture = type { i64, ptr }");
        self.line("%g1.callable = type { i64, ptr, ptr, ptr }");
        if !self.uses_byte_runtime && !self.uses_array_runtime {
            self.line(&format!("declare ptr @malloc({usize_ty})"));
            self.line("declare void @free(ptr)");
        }
    }

    fn emit_handler_runtime(&mut self) {
        let usize_ty = format!("i{}", self.pointer_width());
        self.line(&format!(
            "%g1.handler = type {{ i64, i32, {usize_ty}, ptr }}"
        ));
        if !self.uses_byte_runtime && !self.uses_array_runtime && !self.uses_callable_runtime {
            self.line(&format!("declare ptr @malloc({usize_ty})"));
            self.line("declare void @free(ptr)");
        }
    }

    fn handler_capture_type(&self, handler_def: u32) -> Result<TypeId, Vec<Diagnostic>> {
        self.phases
            .artifact
            .types
            .iter()
            .find_map(|ty| match ty.representation() {
                Type::Handler {
                    handler_def: described,
                    capture_type,
                    ..
                } if *described == handler_def => Some(*capture_type),
                _ => None,
            })
            .ok_or_else(|| {
                vec![backend_error(format!(
                    "handler#{handler_def} has no runtime handler type"
                ))]
            })
    }

    fn handler_runtime_type(&self, handler_def: u32) -> Result<TypeId, Vec<Diagnostic>> {
        self.phases
            .artifact
            .types
            .iter()
            .enumerate()
            .find_map(|(index, ty)| match ty.representation() {
                Type::Handler {
                    handler_def: described,
                    ..
                } if *described == handler_def => Some(index as TypeId),
                _ => None,
            })
            .ok_or_else(|| {
                vec![backend_error(format!(
                    "handler#{handler_def} has no runtime handler type"
                ))]
            })
    }

    fn emit_handler_guard_drop_callbacks(
        &mut self,
        reachable: &[usize],
    ) -> Result<(), Vec<Diagnostic>> {
        let Some(&context) = reachable.first() else {
            return Ok(());
        };
        let function = self.phases.mir.functions[context].clone();
        for handler_def in 0..self.phases.artifact.handler_defs.len() {
            let capture_type = self.handler_capture_type(handler_def as u32)?;
            self.line(&format!(
                "define internal void @g1_effect_handler_drop_h{handler_def}(ptr %handler) {{"
            ));
            self.line("entry:");
            self.emit_destroy_handler("%handler", capture_type, &function)?;
            self.line("  ret void");
            self.line("}");
        }
        Ok(())
    }

    fn emit_effect_runtime(&mut self) {
        let usize_ty = format!("i{}", self.pointer_width());
        self.line(
            "%g1.effect_frame = type { ptr, ptr, ptr, ptr, i32, ptr, ptr, ptr, ptr, ptr, i1 }",
        );
        self.line(&format!(
            "%g1.snapshot_range = type {{ ptr, ptr, {usize_ty}, ptr, ptr }}"
        ));
        self.line("%g1.effect_guard = type { i64, ptr, ptr, ptr }");
        self.line("%g1.effect_runtime = type { ptr, i32, i32, i32, ptr, ptr, ptr, ptr, i1 }");
        // Fields 0..4 are the frozen resumption ABI. Reference ownership and
        // shared-handler provenance are
        // append-only so existing field accesses retain their meaning.
        self.line("%g1.resumption = type { ptr, ptr, ptr, ptr, ptr, i64, i1 }");
        self.line("define internal void @g1_effect_guard_retain(ptr %guard) {");
        self.line("entry:");
        self.line("  %present = icmp ne ptr %guard, null");
        self.line("  br i1 %present, label %retain, label %done");
        self.line("retain:");
        self.line(
            "  %count.address = getelementptr inbounds %g1.effect_guard, ptr %guard, i32 0, i32 0",
        );
        self.line("  %count = load i64, ptr %count.address");
        self.line("  %next = add i64 %count, 1");
        self.line("  store i64 %next, ptr %count.address");
        self.line("  br label %done");
        self.line("done:");
        self.line("  ret void");
        self.line("}");
        self.line("define internal void @g1_effect_guard_release(ptr %guard) {");
        self.line("entry:");
        self.line("  %present = icmp ne ptr %guard, null");
        self.line("  br i1 %present, label %inspect, label %done");
        self.line("inspect:");
        self.line(
            "  %count.address = getelementptr inbounds %g1.effect_guard, ptr %guard, i32 0, i32 0",
        );
        self.line("  %count = load i64, ptr %count.address");
        self.line("  %last = icmp eq i64 %count, 1");
        self.line("  br i1 %last, label %destroy, label %decrement");
        self.line("decrement:");
        self.line("  %next.count = sub i64 %count, 1");
        self.line("  store i64 %next.count, ptr %count.address");
        self.line("  br label %done");
        self.line("destroy:");
        self.line("  %payload.address = getelementptr inbounds %g1.effect_guard, ptr %guard, i32 0, i32 1");
        self.line("  %payload = load ptr, ptr %payload.address");
        self.line(
            "  %drop.address = getelementptr inbounds %g1.effect_guard, ptr %guard, i32 0, i32 2",
        );
        self.line("  %drop = load ptr, ptr %drop.address");
        self.line(
            "  %next.address = getelementptr inbounds %g1.effect_guard, ptr %guard, i32 0, i32 3",
        );
        self.line("  %next.guard = load ptr, ptr %next.address");
        self.line("  call void @free(ptr %guard)");
        self.line("  call void %drop(ptr %payload)");
        self.line("  call void @g1_effect_guard_release(ptr %next.guard)");
        self.line("  br label %done");
        self.line("done:");
        self.line("  ret void");
        self.line("}");
        if !self.uses_byte_runtime
            && !self.uses_array_runtime
            && !self.uses_callable_runtime
            && !self.uses_handler_runtime
        {
            self.line(&format!("declare ptr @malloc({usize_ty})"));
            self.line("declare void @free(ptr)");
        }
        if !self.uses_byte_runtime && !self.uses_array_runtime {
            self.line(&format!(
                "declare void @llvm.memcpy.p0.p0.{usize_ty}(ptr nocapture writeonly, ptr nocapture readonly, {usize_ty}, i1 immarg)"
            ));
        }
        self.line(&format!(
            "define internal void @g1_snapshot_record(ptr %context, ptr %source, {usize_ty} %size, ptr %clone, ptr %fix) {{"
        ));
        self.line("entry:");
        self.line(&format!(
            "  %node.end = getelementptr %g1.snapshot_range, ptr null, {usize_ty} 1"
        ));
        self.line(&format!(
            "  %node.size = ptrtoint ptr %node.end to {usize_ty}"
        ));
        self.line(&format!(
            "  %node = call ptr @malloc({usize_ty} %node.size)"
        ));
        self.line("  %failed = icmp eq ptr %node, null");
        self.line("  br i1 %failed, label %trap, label %ready");
        self.line("trap:");
        self.emit_runtime_fault(RUNTIME_FAULT_ALLOCATION_LIMIT, "0", "0", "null", "0");
        self.line("ready:");
        self.line("  %head = load ptr, ptr %context");
        for (field, ty, value) in [
            (0, "ptr", "%head"),
            (1, "ptr", "%source"),
            (2, usize_ty.as_str(), "%size"),
            (3, "ptr", "%clone"),
            (4, "ptr", "%fix"),
        ] {
            self.line(&format!(
                "  %record.{field} = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 {field}"
            ));
            self.line(&format!("  store {ty} {value}, ptr %record.{field}"));
        }
        self.line("  store ptr %node, ptr %context");
        self.line("  ret void");
        self.line("}");
        self.line("define internal ptr @g1_snapshot_lookup_exact(ptr %context, ptr %source) {");
        self.line("entry:");
        self.line("  %head = load ptr, ptr %context");
        self.line("  br label %walk");
        self.line("walk:");
        self.line("  %node = phi ptr [ %head, %entry ], [ %next, %advance ]");
        self.line("  %done = icmp eq ptr %node, null");
        self.line("  br i1 %done, label %missing, label %inspect");
        self.line("inspect:");
        self.line("  %record.source.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 1");
        self.line("  %record.source = load ptr, ptr %record.source.address");
        self.line("  %matches = icmp eq ptr %record.source, %source");
        self.line("  br i1 %matches, label %found, label %advance");
        self.line("found:");
        self.line(
            "  %clone.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 3",
        );
        self.line("  %clone = load ptr, ptr %clone.address");
        self.line("  ret ptr %clone");
        self.line("advance:");
        self.line(
            "  %next.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 0",
        );
        self.line("  %next = load ptr, ptr %next.address");
        self.line("  br label %walk");
        self.line("missing:");
        self.line("  ret ptr null");
        self.line("}");
        self.line("define internal ptr @g1_snapshot_remap(ptr %context, ptr %value) {");
        self.line("entry:");
        self.line("  %head = load ptr, ptr %context");
        self.line("  %value.null = icmp eq ptr %value, null");
        self.line("  br i1 %value.null, label %unchanged, label %walk");
        self.line("walk:");
        self.line("  %node = phi ptr [ %head, %entry ], [ %next, %advance ]");
        self.line("  %done = icmp eq ptr %node, null");
        self.line("  br i1 %done, label %unchanged, label %inspect");
        self.line("inspect:");
        self.line("  %source.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 1");
        self.line("  %source = load ptr, ptr %source.address");
        self.line(
            "  %size.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 2",
        );
        self.line(&format!("  %size = load {usize_ty}, ptr %size.address"));
        self.line(&format!(
            "  %source.integer = ptrtoint ptr %source to {usize_ty}"
        ));
        self.line(&format!(
            "  %value.integer = ptrtoint ptr %value to {usize_ty}"
        ));
        self.line(&format!(
            "  %offset = sub {usize_ty} %value.integer, %source.integer"
        ));
        self.line(&format!("  %inside = icmp ult {usize_ty} %offset, %size"));
        self.line("  br i1 %inside, label %mapped, label %advance");
        self.line("mapped:");
        self.line(
            "  %clone.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 3",
        );
        self.line("  %clone = load ptr, ptr %clone.address");
        self.line(&format!(
            "  %result = getelementptr inbounds i8, ptr %clone, {usize_ty} %offset"
        ));
        self.line("  ret ptr %result");
        self.line("advance:");
        self.line(
            "  %next.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 0",
        );
        self.line("  %next = load ptr, ptr %next.address");
        self.line("  br label %walk");
        self.line("unchanged:");
        self.line("  ret ptr %value");
        self.line("}");
        self.line("define internal void @g1_snapshot_fix_all(ptr %context) {");
        self.line("entry:");
        self.line("  %head = load ptr, ptr %context");
        self.line("  br label %walk");
        self.line("walk:");
        self.line("  %node = phi ptr [ %head, %entry ], [ %next, %advance ]");
        self.line("  %done = icmp eq ptr %node, null");
        self.line("  br i1 %done, label %return, label %inspect");
        self.line("inspect:");
        self.line(
            "  %fix.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 4",
        );
        self.line("  %fix = load ptr, ptr %fix.address");
        self.line("  %has.fix = icmp ne ptr %fix, null");
        self.line("  br i1 %has.fix, label %apply, label %advance");
        self.line("apply:");
        self.line("  %source.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 1");
        self.line("  %source = load ptr, ptr %source.address");
        self.line(
            "  %clone.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 3",
        );
        self.line("  %clone = load ptr, ptr %clone.address");
        self.line("  call void %fix(ptr %source, ptr %clone, ptr %context)");
        self.line("  br label %advance");
        self.line("advance:");
        self.line(
            "  %next.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 0",
        );
        self.line("  %next = load ptr, ptr %next.address");
        self.line("  br label %walk");
        self.line("return:");
        self.line("  ret void");
        self.line("}");
        self.line("define internal void @g1_snapshot_dispose(ptr %context) {");
        self.line("entry:");
        self.line("  %head = load ptr, ptr %context");
        self.line("  br label %walk");
        self.line("walk:");
        self.line("  %node = phi ptr [ %head, %entry ], [ %next, %drop ]");
        self.line("  %done = icmp eq ptr %node, null");
        self.line("  br i1 %done, label %return, label %drop");
        self.line("drop:");
        self.line(
            "  %next.address = getelementptr inbounds %g1.snapshot_range, ptr %node, i32 0, i32 0",
        );
        self.line("  %next = load ptr, ptr %next.address");
        self.line("  call void @free(ptr %node)");
        self.line("  br label %walk");
        self.line("return:");
        self.line("  ret void");
        self.line("}");
        self.line("define internal ptr @g1_effect_clone_chain_owners(ptr %source, ptr %context) {");
        self.line("entry:");
        self.line("  %empty = icmp eq ptr %source, null");
        self.line("  br i1 %empty, label %done.empty, label %clone");
        self.line("clone:");
        self.line("  %previous.address = getelementptr inbounds %g1.effect_frame, ptr %source, i32 0, i32 0");
        self.line("  %previous = load ptr, ptr %previous.address");
        self.line("  %cloned.previous = call ptr @g1_effect_clone_chain_owners(ptr %previous, ptr %context)");
        self.line("  %callback.address = getelementptr inbounds %g1.effect_frame, ptr %source, i32 0, i32 8");
        self.line("  %callback = load ptr, ptr %callback.address");
        self.line(
            "  %cloned = call ptr %callback(ptr %source, ptr %cloned.previous, ptr %context)",
        );
        self.line("  ret ptr %cloned");
        self.line("done.empty:");
        self.line("  ret ptr null");
        self.line("}");
        self.line("define internal void @g1_effect_fix_snapshot_chain(ptr %source, ptr %clone, ptr %context) {");
        self.line("entry:");
        self.line("  %empty = icmp eq ptr %source, null");
        self.line("  br i1 %empty, label %done, label %fix");
        self.line("fix:");
        self.line(
            "  %fix.address = getelementptr inbounds %g1.effect_frame, ptr %source, i32 0, i32 9",
        );
        self.line("  %fix.callback = load ptr, ptr %fix.address");
        self.line("  call void %fix.callback(ptr %source, ptr %clone, ptr %context)");
        self.line("  %source.previous.address = getelementptr inbounds %g1.effect_frame, ptr %source, i32 0, i32 0");
        self.line("  %source.previous = load ptr, ptr %source.previous.address");
        self.line("  %clone.previous.address = getelementptr inbounds %g1.effect_frame, ptr %clone, i32 0, i32 0");
        self.line("  %clone.previous = load ptr, ptr %clone.previous.address");
        self.line("  call void @g1_effect_fix_snapshot_chain(ptr %source.previous, ptr %clone.previous, ptr %context)");
        self.line("  br label %done");
        self.line("done:");
        self.line("  ret void");
        self.line("}");
        self.line("define internal ptr @g1_effect_clone_chain(ptr %source) {");
        self.line("entry:");
        self.line("  %context = alloca ptr");
        self.line("  store ptr null, ptr %context");
        self.line("  %clone = call ptr @g1_effect_clone_chain_owners(ptr %source, ptr %context)");
        self.line("  call void @g1_snapshot_fix_all(ptr %context)");
        self.line("  call void @g1_snapshot_dispose(ptr %context)");
        self.line("  ret ptr %clone");
        self.line("}");
        self.line("define internal ptr @g1_effect_chain_bottom(ptr %top) {");
        self.line("entry:");
        self.line("  br label %walk");
        self.line("walk:");
        self.line("  %current = phi ptr [ %top, %entry ], [ %previous, %advance ]");
        self.line("  %previous.address = getelementptr inbounds %g1.effect_frame, ptr %current, i32 0, i32 0");
        self.line("  %previous = load ptr, ptr %previous.address");
        self.line("  %bottom = icmp eq ptr %previous, null");
        self.line("  br i1 %bottom, label %done, label %advance");
        self.line("advance:");
        self.line("  br label %walk");
        self.line("done:");
        self.line("  ret ptr %current");
        self.line("}");
        self.line("define internal void @g1_effect_guard_drop_chain(ptr %top) {");
        self.line("entry:");
        self.line("  br label %walk");
        self.line("walk:");
        self.line("  %current = phi ptr [ %top, %entry ], [ %previous, %drop ]");
        self.line("  %present = icmp ne ptr %current, null");
        self.line("  br i1 %present, label %drop, label %done");
        self.line("drop:");
        self.line("  %previous.address = getelementptr inbounds %g1.effect_frame, ptr %current, i32 0, i32 0");
        self.line("  %previous = load ptr, ptr %previous.address");
        self.line(
            "  %drop.address = getelementptr inbounds %g1.effect_frame, ptr %current, i32 0, i32 2",
        );
        self.line("  %drop.callback = load ptr, ptr %drop.address");
        self.line("  call void %drop.callback(ptr %current)");
        self.line("  br label %walk");
        self.line("done:");
        self.line("  ret void");
        self.line("}");
    }

    fn emit_allocate_effect_frame_chain_guard(&mut self, top: &str, next: &str) -> String {
        let usize_ty = format!("i{}", self.pointer_width());
        let size = self.emit_array_element_size("%g1.effect_guard");
        let guard = self.temp();
        let failed = self.temp();
        self.line(&format!("  %{guard} = call ptr @malloc({usize_ty} {size})"));
        self.line(&format!("  %{failed} = icmp eq ptr %{guard}, null"));
        self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        for (field, ty, value) in [
            (0, "i64", "1".to_owned()),
            (1, "ptr", top.to_owned()),
            (2, "ptr", "@g1_effect_guard_drop_chain".to_owned()),
            (3, "ptr", next.to_owned()),
        ] {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_guard, ptr %{guard}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store {ty} {value}, ptr %{address}"));
        }
        format!("%{guard}")
    }

    fn emit_allocate_handler_activation(
        &mut self,
        handler: &str,
        handler_def: u32,
        next: &str,
        retain_next: bool,
    ) -> String {
        if retain_next {
            self.line(&format!("  call void @g1_effect_guard_retain(ptr {next})"));
        }
        let usize_ty = format!("i{}", self.pointer_width());
        let size = self.emit_array_element_size("%g1.effect_guard");
        let activation = self.temp();
        let failed = self.temp();
        self.line(&format!(
            "  %{activation} = call ptr @malloc({usize_ty} {size})"
        ));
        self.line(&format!("  %{failed} = icmp eq ptr %{activation}, null"));
        self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        for (field, ty, value) in [
            (0, "i64", "1".to_owned()),
            (1, "ptr", handler.to_owned()),
            (2, "ptr", format!("@g1_effect_handler_drop_h{handler_def}")),
            (3, "ptr", next.to_owned()),
        ] {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_guard, ptr %{activation}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store {ty} {value}, ptr %{address}"));
        }
        format!("%{activation}")
    }

    fn emit_make_callable(
        &mut self,
        caller: &mir::Function,
        callable_type: TypeId,
        target: usize,
        captures: &[mir::Operand],
    ) -> Result<String, Vec<Diagnostic>> {
        let Type::Callable {
            capture_type,
            receiver_mode,
            ..
        } = self.runtime_type(callable_type)?.clone()
        else {
            return Err(vec![unsupported(
                caller,
                "MakeCallable with a non-callable runtime type",
            )]);
        };
        let target_function = self
            .phases
            .mir
            .functions
            .get(target)
            .ok_or_else(|| vec![unsupported(caller, "MakeCallable target is missing")])?;
        if target_function.receiver_mode != Some(receiver_mode) {
            return Err(vec![unsupported(
                caller,
                "MakeCallable receiver mode does not match its target",
            )]);
        }

        let capture_ty = self.llvm_type(capture_type)?;
        let capture_value = match self.runtime_type(capture_type)? {
            Type::Unit => {
                if !captures.is_empty() {
                    return Err(vec![unsupported(
                        caller,
                        "captureless callable with capture operands",
                    )]);
                }
                "0".to_owned()
            }
            Type::Tuple { .. } | Type::Struct { .. } => {
                let fields = self.runtime_aggregate_fields(capture_type)?;
                if fields.len() != captures.len() {
                    return Err(vec![unsupported(caller, "callable capture count mismatch")]);
                }
                self.emit_capture_aggregate(caller, &capture_ty, &fields, captures)?
            }
            other => {
                return Err(vec![unsupported(
                    caller,
                    format!("callable capture layout {other:?}"),
                )]);
            }
        };

        let usize_ty = format!("i{}", self.pointer_width());
        let callable_end = self.temp();
        self.line(&format!(
            "  %{callable_end} = getelementptr %g1.callable, ptr null, {usize_ty} 1"
        ));
        let callable_size = self.temp();
        self.line(&format!(
            "  %{callable_size} = ptrtoint ptr %{callable_end} to {usize_ty}"
        ));
        let callable = self.temp();
        self.line(&format!(
            "  %{callable} = call ptr @malloc({usize_ty} %{callable_size})"
        ));
        let callable_failed = self.temp();
        self.line(&format!(
            "  %{callable_failed} = icmp eq ptr %{callable}, null"
        ));
        self.emit_runtime_fault_if(callable_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        let capture_size = self.emit_array_element_size(&capture_ty);
        let capture = self.temp();
        self.line(&format!(
            "  %{capture} = call ptr @malloc({usize_ty} {capture_size})"
        ));
        let capture_failed = self.temp();
        self.line(&format!(
            "  %{capture_failed} = icmp eq ptr %{capture}, null"
        ));
        self.emit_runtime_fault_if(capture_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        self.line(&format!(
            "  store {capture_ty} {capture_value}, ptr %{capture}"
        ));
        let capture_handle_end = self.temp();
        self.line(&format!(
            "  %{capture_handle_end} = getelementptr %g1.capture, ptr null, {usize_ty} 1"
        ));
        let capture_handle_size = self.temp();
        self.line(&format!(
            "  %{capture_handle_size} = ptrtoint ptr %{capture_handle_end} to {usize_ty}"
        ));
        let capture_handle = self.temp();
        self.line(&format!(
            "  %{capture_handle} = call ptr @malloc({usize_ty} %{capture_handle_size})"
        ));
        let capture_handle_failed = self.temp();
        self.line(&format!(
            "  %{capture_handle_failed} = icmp eq ptr %{capture_handle}, null"
        ));
        self.emit_runtime_fault_if(capture_handle_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        let capture_count_address = self.temp();
        self.line(&format!(
            "  %{capture_count_address} = getelementptr inbounds %g1.capture, ptr %{capture_handle}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{capture_count_address}"));
        let capture_data_address = self.temp();
        self.line(&format!(
            "  %{capture_data_address} = getelementptr inbounds %g1.capture, ptr %{capture_handle}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  store ptr %{capture}, ptr %{capture_data_address}"
        ));
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{count_address}"));
        let function_address = self.temp();
        self.line(&format!(
            "  %{function_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  store ptr @g1_f{target}, ptr %{function_address}"
        ));
        let capture_address = self.temp();
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 2"
        ));
        self.line(&format!(
            "  store ptr %{capture_handle}, ptr %{capture_address}"
        ));
        let starter_address = self.temp();
        self.line(&format!(
            "  %{starter_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 3"
        ));
        let starter = if self.function_needs_effect_frame(target_function) {
            format!("@g1_effect_start_f{target}")
        } else {
            "null".to_owned()
        };
        self.line(&format!("  store ptr {starter}, ptr %{starter_address}"));
        Ok(format!("%{callable}"))
    }

    fn emit_capture_aggregate(
        &mut self,
        caller: &mir::Function,
        aggregate_ty: &str,
        fields: &[TypeId],
        captures: &[mir::Operand],
    ) -> Result<String, Vec<Diagnostic>> {
        let mut aggregate = "zeroinitializer".to_owned();
        for (index, (expected, capture)) in fields.iter().zip(captures).enumerate() {
            let actual = self.register_runtime_type(caller, capture.register)?;
            if actual != *expected {
                return Err(vec![unsupported(caller, "callable capture type mismatch")]);
            }
            let field_ty = self.llvm_type(*expected)?;
            let value = self.load_operand(caller, capture)?;
            if capture.mode == mir::UseMode::Copy {
                self.emit_retain(*expected, &value, caller)?;
            }
            let inserted = self.temp();
            self.line(&format!(
                "  %{inserted} = insertvalue {aggregate_ty} {aggregate}, {field_ty} {value}, {index}"
            ));
            aggregate = format!("%{inserted}");
        }
        Ok(aggregate)
    }

    fn emit_allocate_shared_capture(
        &mut self,
        capture_ty: &str,
        capture_value: &str,
        references: usize,
    ) -> String {
        let usize_ty = format!("i{}", self.pointer_width());
        let capture_size = self.emit_array_element_size(capture_ty);
        let capture = self.temp();
        self.line(&format!(
            "  %{capture} = call ptr @malloc({usize_ty} {capture_size})"
        ));
        let capture_failed = self.temp();
        self.line(&format!(
            "  %{capture_failed} = icmp eq ptr %{capture}, null"
        ));
        self.emit_runtime_fault_if(capture_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        self.line(&format!(
            "  store {capture_ty} {capture_value}, ptr %{capture}"
        ));
        let handle_end = self.temp();
        self.line(&format!(
            "  %{handle_end} = getelementptr %g1.capture, ptr null, {usize_ty} 1"
        ));
        let handle_size = self.temp();
        self.line(&format!(
            "  %{handle_size} = ptrtoint ptr %{handle_end} to {usize_ty}"
        ));
        let handle = self.temp();
        self.line(&format!(
            "  %{handle} = call ptr @malloc({usize_ty} %{handle_size})"
        ));
        let handle_failed = self.temp();
        self.line(&format!("  %{handle_failed} = icmp eq ptr %{handle}, null"));
        self.emit_runtime_fault_if(handle_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.capture, ptr %{handle}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 {references}, ptr %{count_address}"));
        let data_address = self.temp();
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.capture, ptr %{handle}, i32 0, i32 1"
        ));
        self.line(&format!("  store ptr %{capture}, ptr %{data_address}"));
        format!("%{handle}")
    }

    fn emit_allocate_callable_shell(&mut self, target: usize, capture: &str) -> String {
        let usize_ty = format!("i{}", self.pointer_width());
        let end = self.temp();
        self.line(&format!(
            "  %{end} = getelementptr %g1.callable, ptr null, {usize_ty} 1"
        ));
        let size = self.temp();
        self.line(&format!("  %{size} = ptrtoint ptr %{end} to {usize_ty}"));
        let callable = self.temp();
        self.line(&format!(
            "  %{callable} = call ptr @malloc({usize_ty} %{size})"
        ));
        let failed = self.temp();
        self.line(&format!("  %{failed} = icmp eq ptr %{callable}, null"));
        self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{count_address}"));
        let function_address = self.temp();
        self.line(&format!(
            "  %{function_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  store ptr @g1_f{target}, ptr %{function_address}"
        ));
        let capture_address = self.temp();
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 2"
        ));
        self.line(&format!("  store ptr {capture}, ptr %{capture_address}"));
        let starter_address = self.temp();
        self.line(&format!(
            "  %{starter_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 3"
        ));
        let starter = self
            .phases
            .mir
            .functions
            .get(target)
            .filter(|function| self.function_needs_effect_frame(function))
            .map_or_else(
                || "null".to_owned(),
                |_| format!("@g1_effect_start_f{target}"),
            );
        self.line(&format!("  store ptr {starter}, ptr %{starter_address}"));
        format!("%{callable}")
    }

    fn emit_make_handler(
        &mut self,
        function: &mir::Function,
        handler_type: TypeId,
        handler_def: u32,
        clauses: &[mir::Operand],
    ) -> Result<String, Vec<Diagnostic>> {
        let Type::Handler {
            handler_def: described_def,
            capture_type,
            ..
        } = self.runtime_type(handler_type)?.clone()
        else {
            return Err(vec![unsupported(
                function,
                "MakeHandler with a non-handler runtime type",
            )]);
        };
        if described_def != handler_def {
            return Err(vec![unsupported(
                function,
                "MakeHandler descriptor identity mismatch",
            )]);
        }
        let clause_types = self.runtime_aggregate_fields(capture_type)?;
        if clause_types.len() != clauses.len() {
            return Err(vec![unsupported(
                function,
                "MakeHandler clause count mismatch",
            )]);
        }
        for (clause, expected) in clauses.iter().zip(&clause_types) {
            let actual = self.register_runtime_type(function, clause.register)?;
            if actual != *expected || !matches!(self.runtime_type(actual)?, Type::Callable { .. }) {
                return Err(vec![unsupported(
                    function,
                    "MakeHandler clause type mismatch",
                )]);
            }
        }

        let usize_ty = format!("i{}", self.pointer_width());
        let handler_end = self.temp();
        self.line(&format!(
            "  %{handler_end} = getelementptr %g1.handler, ptr null, {usize_ty} 1"
        ));
        let handler_size = self.temp();
        self.line(&format!(
            "  %{handler_size} = ptrtoint ptr %{handler_end} to {usize_ty}"
        ));
        let handler = self.temp();
        self.line(&format!(
            "  %{handler} = call ptr @malloc({usize_ty} %{handler_size})"
        ));
        let handler_failed = self.temp();
        self.line(&format!(
            "  %{handler_failed} = icmp eq ptr %{handler}, null"
        ));
        self.emit_runtime_fault_if(handler_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        let clauses_storage = if clauses.is_empty() {
            "null".to_owned()
        } else {
            let pointer_size = usize::from(self.pointer_width() / 8);
            let clauses_storage = self.temp();
            self.line(&format!(
                "  %{clauses_storage} = call ptr @malloc({usize_ty} {})",
                clauses.len() * pointer_size
            ));
            let clauses_failed = self.temp();
            self.line(&format!(
                "  %{clauses_failed} = icmp eq ptr %{clauses_storage}, null"
            ));
            self.emit_runtime_fault_if(clauses_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
            format!("%{clauses_storage}")
        };
        let definition_address = self.temp();
        self.line(&format!(
            "  %{definition_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 1"
        ));
        let references_address = self.temp();
        self.line(&format!(
            "  %{references_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{references_address}"));
        self.line(&format!(
            "  store i32 {handler_def}, ptr %{definition_address}"
        ));
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 2"
        ));
        self.line(&format!(
            "  store {usize_ty} {}, ptr %{count_address}",
            clauses.len()
        ));
        let clauses_address = self.temp();
        self.line(&format!(
            "  %{clauses_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 3"
        ));
        self.line(&format!(
            "  store ptr {clauses_storage}, ptr %{clauses_address}"
        ));
        for (index, (clause, clause_type)) in clauses.iter().zip(clause_types).enumerate() {
            let callable = self.load_operand(function, clause)?;
            if clause.mode == mir::UseMode::Copy {
                self.emit_retain(clause_type, &callable, function)?;
            }
            let slot = self.temp();
            self.line(&format!(
                "  %{slot} = getelementptr inbounds ptr, ptr {clauses_storage}, {usize_ty} {index}"
            ));
            self.line(&format!("  store ptr {callable}, ptr %{slot}"));
        }
        Ok(format!("%{handler}"))
    }

    fn emit_make_handler_shared(
        &mut self,
        function: &mir::Function,
        handler_type: TypeId,
        handler_def: u32,
        targets: &[u32],
        captures: &[mir::Operand],
    ) -> Result<String, Vec<Diagnostic>> {
        let Type::Handler {
            handler_def: described_def,
            capture_type: clause_tuple,
            ..
        } = self.runtime_type(handler_type)?.clone()
        else {
            return Err(vec![unsupported(
                function,
                "MakeHandlerShared with a non-handler runtime type",
            )]);
        };
        if described_def != handler_def {
            return Err(vec![unsupported(
                function,
                "shared handler descriptor identity mismatch",
            )]);
        }
        let clause_types = self.runtime_aggregate_fields(clause_tuple)?;
        if clause_types.len() != targets.len() || targets.is_empty() {
            return Err(vec![unsupported(
                function,
                "shared handler clause count mismatch",
            )]);
        }
        let mut environment_type = None;
        for (clause_type, target) in clause_types.iter().zip(targets) {
            let Type::Callable {
                capture_type,
                receiver_mode,
                ..
            } = self.runtime_type(*clause_type)?
            else {
                return Err(vec![unsupported(
                    function,
                    "shared handler clause is not callable",
                )]);
            };
            if environment_type
                .replace(*capture_type)
                .is_some_and(|known| known != *capture_type)
            {
                return Err(vec![unsupported(
                    function,
                    "shared handler clauses disagree on their environment type",
                )]);
            }
            let target_function = self
                .phases
                .mir
                .functions
                .get(*target as usize)
                .ok_or_else(|| vec![unsupported(function, "shared handler target is missing")])?;
            if target_function.receiver_mode != Some(*receiver_mode) {
                return Err(vec![unsupported(
                    function,
                    "shared handler target receiver mismatch",
                )]);
            }
        }
        let environment_type = environment_type.expect("nonempty clause list");
        let environment_ty = self.llvm_type(environment_type)?;
        let environment_value = match self.runtime_type(environment_type)? {
            Type::Unit => {
                if !captures.is_empty() {
                    return Err(vec![unsupported(
                        function,
                        "captureless shared handler with capture operands",
                    )]);
                }
                "0".to_owned()
            }
            Type::Tuple { .. } | Type::Struct { .. } => {
                let fields = self.runtime_aggregate_fields(environment_type)?;
                if fields.len() != captures.len() {
                    return Err(vec![unsupported(
                        function,
                        "shared handler capture count mismatch",
                    )]);
                }
                self.emit_capture_aggregate(function, &environment_ty, &fields, captures)?
            }
            other => {
                return Err(vec![unsupported(
                    function,
                    format!("shared handler capture layout {other:?}"),
                )]);
            }
        };
        let capture =
            self.emit_allocate_shared_capture(&environment_ty, &environment_value, targets.len());
        let mut callables = Vec::with_capacity(targets.len());
        for (target, clause_type) in targets.iter().zip(clause_types.iter().copied()) {
            let callable = self.emit_allocate_callable_shell(*target as usize, &capture);
            callables.push((clause_type, callable));
        }
        self.emit_handler_from_values(handler_def, &callables)
    }

    fn emit_handler_from_values(
        &mut self,
        handler_def: u32,
        clauses: &[(TypeId, String)],
    ) -> Result<String, Vec<Diagnostic>> {
        let usize_ty = format!("i{}", self.pointer_width());
        let handler_end = self.temp();
        self.line(&format!(
            "  %{handler_end} = getelementptr %g1.handler, ptr null, {usize_ty} 1"
        ));
        let handler_size = self.temp();
        self.line(&format!(
            "  %{handler_size} = ptrtoint ptr %{handler_end} to {usize_ty}"
        ));
        let handler = self.temp();
        self.line(&format!(
            "  %{handler} = call ptr @malloc({usize_ty} %{handler_size})"
        ));
        let handler_failed = self.temp();
        self.line(&format!(
            "  %{handler_failed} = icmp eq ptr %{handler}, null"
        ));
        self.emit_runtime_fault_if(handler_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        let clauses_storage = if clauses.is_empty() {
            "null".to_owned()
        } else {
            let pointer_size = usize::from(self.pointer_width() / 8);
            let storage = self.temp();
            self.line(&format!(
                "  %{storage} = call ptr @malloc({usize_ty} {})",
                clauses.len() * pointer_size
            ));
            let failed = self.temp();
            self.line(&format!("  %{failed} = icmp eq ptr %{storage}, null"));
            self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
            format!("%{storage}")
        };
        let definition_address = self.temp();
        self.line(&format!(
            "  %{definition_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 1"
        ));
        let references_address = self.temp();
        self.line(&format!(
            "  %{references_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{references_address}"));
        self.line(&format!(
            "  store i32 {handler_def}, ptr %{definition_address}"
        ));
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 2"
        ));
        self.line(&format!(
            "  store {usize_ty} {}, ptr %{count_address}",
            clauses.len()
        ));
        let clauses_address = self.temp();
        self.line(&format!(
            "  %{clauses_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 3"
        ));
        self.line(&format!(
            "  store ptr {clauses_storage}, ptr %{clauses_address}"
        ));
        for (index, (_, callable)) in clauses.iter().enumerate() {
            let slot = self.temp();
            self.line(&format!(
                "  %{slot} = getelementptr inbounds ptr, ptr {clauses_storage}, {usize_ty} {index}"
            ));
            self.line(&format!("  store ptr {callable}, ptr %{slot}"));
        }
        Ok(format!("%{handler}"))
    }

    fn emit_function(&mut self, index: usize) -> Result<(), Vec<Diagnostic>> {
        let function = &self.phases.mir.functions[index];
        if self.function_needs_effect_frame(function) {
            return self.emit_effect_function(index);
        }
        let result = self.llvm_return_type(function.result)?;
        let mut params = function
            .params
            .iter()
            .enumerate()
            .map(|(index, ty)| Ok(format!("{} %arg{index}", self.llvm_type(*ty)?)))
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        if function.receiver_mode.is_some() {
            params.insert(
                0,
                format!("{} %receiver", self.llvm_type(function.receiver_type)?),
            );
        }
        let params = params.join(", ");
        self.line(&format!("define {} @g1_f{index}({params}) {{", result));
        self.line("entry.allocas:");
        for (register, ty) in function.register_types.iter().enumerate() {
            self.line(&format!("  %r{register} = alloca {}", self.llvm_type(*ty)?));
            for field in self.ordinary_aggregate_field_layout(function, register as u32)? {
                self.line(&format!(
                    "  %fieldinit{register}.{} = alloca i8",
                    field.owned_mask_index
                ));
                self.line(&format!(
                    "  store i8 0, ptr %fieldinit{register}.{}",
                    field.owned_mask_index
                ));
            }
        }
        if function.receiver_mode.is_some() {
            self.line(&format!(
                "  store {} %receiver, ptr %r0",
                self.llvm_type(function.receiver_type)?
            ));
            self.emit_set_ordinary_aggregate_fields(function, 0, true)?;
        }
        for (parameter, ty) in function.params.iter().enumerate() {
            self.line(&format!(
                "  store {} %arg{parameter}, ptr %r{}",
                self.llvm_type(*ty)?,
                parameter + 1
            ));
            self.emit_set_ordinary_aggregate_fields(function, parameter as u32 + 1, true)?;
        }
        self.line(&format!("  br label %bb{}", function.entry));

        for block in &function.blocks {
            self.line(&format!("bb{}:", block.id));
            for instruction in &block.statements {
                if let InstructionKind::Drop { owner } = &instruction.kind {
                    let owner_type = self.register_runtime_type(function, owner.register)?;
                    if !self
                        .ordinary_aggregate_field_layout(function, owner.register)?
                        .is_empty()
                    {
                        self.emit_ordinary_drop_aggregate_register(
                            function,
                            owner.register,
                            owner_type,
                        )?;
                        continue;
                    }
                }
                if let InstructionKind::Copy { dst, src } = &instruction.kind {
                    if !self
                        .ordinary_aggregate_field_layout(function, src.register)?
                        .is_empty()
                    {
                        let value = self.load_operand(function, src)?;
                        let ty = self.register_type(function, *dst)?;
                        self.emit_retain_ordinary_aggregate_register(
                            function,
                            src.register,
                            &value,
                        )?;
                        self.line(&format!("  store {ty} {value}, ptr %r{dst}"));
                    } else {
                        self.emit_instruction(function, &instruction.kind)?;
                    }
                } else {
                    self.emit_instruction(function, &instruction.kind)?;
                }
                match &instruction.kind {
                    InstructionKind::Copy { dst, src } | InstructionKind::Move { dst, src } => {
                        self.emit_copy_ordinary_aggregate_fields(function, src.register, *dst)?;
                        if matches!(&instruction.kind, InstructionKind::Move { .. }) {
                            self.emit_set_ordinary_aggregate_fields(function, src.register, false)?;
                        }
                    }
                    _ => {
                        if let Some(destination) = instruction.kind.destination() {
                            self.emit_set_ordinary_aggregate_fields(function, destination, true)?;
                        }
                    }
                }
                if let InstructionKind::ProjectMove { src, field, .. } = &instruction.kind {
                    let source_type = self.register_runtime_type(function, src.register)?;
                    if !self
                        .ordinary_aggregate_field_layout(function, src.register)?
                        .is_empty()
                    {
                        let runtime_field =
                            self.runtime_aggregate_owned_field_index(source_type, *field)?;
                        self.line(&format!(
                            "  store i8 0, ptr %fieldinit{}.{runtime_field}",
                            src.register
                        ));
                    }
                }
            }
            self.emit_terminator(index, function, &block.terminator)?;
        }
        self.line("}");
        self.line("");
        Ok(())
    }

    fn effect_frame_type(&self, function_index: usize) -> String {
        format!("%g1.effect_frame.f{function_index}")
    }

    fn ordinary_aggregate_field_layout(
        &self,
        function: &mir::Function,
        register: u32,
    ) -> Result<Vec<AggregateFieldLayout>, Vec<Diagnostic>> {
        let ty = self.register_runtime_type(function, register)?;
        match self.runtime_type(ty)? {
            Type::Tuple { .. } | Type::Struct { .. } | Type::BindingPack { .. } => {
                self.runtime_aggregate_field_layout(ty, 0)
            }
            _ => Ok(Vec::new()),
        }
    }

    fn emit_set_ordinary_aggregate_fields(
        &mut self,
        function: &mir::Function,
        register: u32,
        initialized: bool,
    ) -> Result<(), Vec<Diagnostic>> {
        for field in self.ordinary_aggregate_field_layout(function, register)? {
            self.line(&format!(
                "  store i8 {}, ptr %fieldinit{register}.{}",
                u8::from(initialized),
                field.owned_mask_index
            ));
        }
        Ok(())
    }

    fn emit_copy_ordinary_aggregate_fields(
        &mut self,
        function: &mir::Function,
        source: u32,
        destination: u32,
    ) -> Result<(), Vec<Diagnostic>> {
        let source_fields = self.ordinary_aggregate_field_layout(function, source)?;
        let destination_fields = self.ordinary_aggregate_field_layout(function, destination)?;
        if source_fields.len() != destination_fields.len() {
            return Err(vec![unsupported(
                function,
                "aggregate field-state transfer layout mismatch",
            )]);
        }
        let flags = source_fields
            .iter()
            .map(|field| {
                let flag = self.temp();
                self.line(&format!(
                    "  %{flag} = load i8, ptr %fieldinit{source}.{}",
                    field.owned_mask_index
                ));
                format!("%{flag}")
            })
            .collect::<Vec<_>>();
        for (field, flag) in destination_fields.iter().zip(flags) {
            self.line(&format!(
                "  store i8 {flag}, ptr %fieldinit{destination}.{}",
                field.owned_mask_index
            ));
        }
        Ok(())
    }

    fn effect_field_layout(
        &self,
        function: &mir::Function,
    ) -> Result<(Vec<Vec<AggregateFieldLayout>>, usize), Vec<Diagnostic>> {
        let mut total = 0usize;
        let mut layout = Vec::with_capacity(function.register_types.len());
        for ty in &function.register_types {
            let fields = match self.runtime_type(*ty)? {
                Type::Tuple { .. } | Type::Struct { .. } | Type::BindingPack { .. } => {
                    self.runtime_aggregate_field_layout(*ty, total)?
                }
                _ => Vec::new(),
            };
            total += fields.len();
            layout.push(fields);
        }
        Ok((layout, total))
    }

    fn emit_effect_function(&mut self, index: usize) -> Result<(), Vec<Diagnostic>> {
        let function = &self.phases.mir.functions[index];
        let frame_ty = self.effect_frame_type(index);
        let (field_layout, field_count) = self.effect_field_layout(function)?;
        let register_types = function
            .register_types
            .iter()
            .map(|ty| self.llvm_type(*ty))
            .collect::<Result<Vec<_>, _>>()?;
        let mut frame_fields = vec!["%g1.effect_frame".to_owned()];
        frame_fields.extend(register_types.iter().cloned());
        frame_fields.push(format!("[{} x i8]", register_types.len()));
        frame_fields.push(format!("[{field_count} x i8]"));
        self.line(&format!(
            "{frame_ty} = type {{ {} }}",
            frame_fields.join(", ")
        ));

        let result = self.llvm_return_type(function.result)?;
        let mut direct_params = function
            .params
            .iter()
            .enumerate()
            .map(|(parameter, ty)| Ok(format!("{} %arg{parameter}", self.llvm_type(*ty)?)))
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        if function.receiver_mode.is_some() {
            direct_params.insert(
                0,
                format!("{} %receiver", self.llvm_type(function.receiver_type)?),
            );
        }
        self.line(&format!(
            "define {result} @g1_f{index}({}) {{",
            direct_params.join(", ")
        ));
        // Numeric SSA temporaries require an explicit entry label: otherwise
        // LLVM assigns the implicit entry block `%0` first.
        self.line("entry:");
        if function.outward_protocols.is_empty() {
            let return_slot = self.temp();
            let return_init = self.temp();
            self.line(&format!(
                "  %{return_slot} = alloca {}",
                if result == "void" { "i8" } else { &result }
            ));
            self.line(&format!("  %{return_init} = alloca i8"));
            self.line(&format!("  store i8 0, ptr %{return_init}"));
            let mut arguments = vec![
                "ptr null".to_owned(),
                format!("ptr %{return_slot}"),
                format!("ptr %{return_init}"),
            ];
            if function.receiver_mode.is_some() {
                arguments.push(format!(
                    "{} %receiver",
                    self.llvm_type(function.receiver_type)?
                ));
            }
            arguments.extend(
                function
                    .params
                    .iter()
                    .enumerate()
                    .map(|(parameter, ty)| {
                        self.llvm_type(*ty)
                            .map(|ty| format!("{ty} %arg{parameter}"))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            let frame = self.temp();
            self.line(&format!(
                "  %{frame} = call ptr @g1_effect_new_f{index}({})",
                arguments.join(", ")
            ));
            let runtime = self.temp();
            self.line(&format!("  %{runtime} = alloca %g1.effect_runtime"));
            for (field, ty, value) in [
                (0, "ptr", format!("%{frame}")),
                (1, "i32", "-1".to_owned()),
                (2, "i32", "0".to_owned()),
                (3, "i32", "0".to_owned()),
                (4, "ptr", "null".to_owned()),
                (5, "ptr", "null".to_owned()),
                (6, "ptr", "null".to_owned()),
                (7, "ptr", "null".to_owned()),
                (8, "i1", "false".to_owned()),
            ] {
                let address = self.temp();
                self.line(&format!(
                    "  %{address} = getelementptr inbounds %g1.effect_runtime, ptr %{runtime}, i32 0, i32 {field}"
                ));
                self.line(&format!("  store {ty} {value}, ptr %{address}"));
            }
            let loop_label = self.temp();
            let step_label = self.temp();
            let stopped_label = self.temp();
            self.line(&format!("  br label %effect.wrapper.loop{loop_label}"));
            self.line(&format!("effect.wrapper.loop{loop_label}:"));
            let current = self.load_effect_runtime_field(&format!("%{runtime}"), 0, "ptr");
            let running = self.temp();
            self.line(&format!("  %{running} = icmp ne ptr {current}, null"));
            self.line(&format!(
                "  br i1 %{running}, label %effect.wrapper.step{step_label}, label %effect.wrapper.stopped{stopped_label}"
            ));
            self.line(&format!("effect.wrapper.step{step_label}:"));
            let step_address = self.temp();
            let step = self.temp();
            self.line(&format!(
                "  %{step_address} = getelementptr inbounds %g1.effect_frame, ptr {current}, i32 0, i32 1"
            ));
            self.line(&format!("  %{step} = load ptr, ptr %{step_address}"));
            self.line(&format!(
                "  call void %{step}(ptr {current}, ptr %{runtime})"
            ));
            self.line(&format!("  br label %effect.wrapper.loop{loop_label}"));
            self.line(&format!("effect.wrapper.stopped{stopped_label}:"));
            let status = self.load_effect_runtime_field(&format!("%{runtime}"), 1, "i32");
            let normal_label = self.temp();
            let perform_label = self.temp();
            let invalid_label = self.temp();
            self.line(&format!(
                "  switch i32 {status}, label %effect.wrapper.invalid{invalid_label} [ i32 0, label %effect.wrapper.normal{normal_label} i32 1, label %effect.wrapper.perform{perform_label} ]"
            ));
            self.line(&format!("effect.wrapper.normal{normal_label}:"));
            let completed = self.load_effect_runtime_field(&format!("%{runtime}"), 5, "ptr");
            self.emit_drop_optional_effect_frame(&completed);
            if result == "void" {
                self.line("  ret void");
            } else {
                let returned = self.temp();
                self.line(&format!(
                    "  %{returned} = load {result}, ptr %{return_slot}"
                ));
                self.line(&format!("  ret {result} %{returned}"));
            }
            self.line(&format!("effect.wrapper.perform{perform_label}:"));
            let unhandled = self.temp();
            self.emit_effect_request_router(
                function,
                &format!("%{runtime}"),
                &format!("effect.wrapper.loop{loop_label}"),
                &format!("effect.wrapper.unhandled{unhandled}"),
                EffectRoutingMode::Initial,
            )?;
            self.line(&format!("effect.wrapper.unhandled{unhandled}:"));
            let protocol = self.load_effect_runtime_field(&format!("%{runtime}"), 2, "i32");
            let operation = self.load_effect_runtime_field(&format!("%{runtime}"), 3, "i32");
            self.emit_runtime_fault(
                RUNTIME_FAULT_UNHANDLED_EFFECT,
                &protocol,
                &operation,
                "null",
                "0",
            );
            self.line(&format!("effect.wrapper.invalid{invalid_label}:"));
            self.line("  call void @llvm.trap()");
            self.line("  unreachable");
        } else {
            self.line("  call void @llvm.trap()");
            self.line("  unreachable");
        }
        self.line("}");
        self.line("");

        let mut constructor_params = vec![
            "ptr %previous".to_owned(),
            "ptr %return_slot".to_owned(),
            "ptr %return_init".to_owned(),
        ];
        if function.receiver_mode.is_some() {
            constructor_params.push(format!(
                "{} %receiver",
                self.llvm_type(function.receiver_type)?
            ));
        }
        constructor_params.extend(
            function
                .params
                .iter()
                .enumerate()
                .map(|(parameter, ty)| {
                    self.llvm_type(*ty)
                        .map(|ty| format!("{ty} %arg{parameter}"))
                })
                .collect::<Result<Vec<_>, _>>()?,
        );
        let usize_ty = format!("i{}", self.pointer_width());
        self.line(&format!(
            "define ptr @g1_effect_new_f{index}({}) {{",
            constructor_params.join(", ")
        ));
        let frame_size = self.emit_array_element_size(&frame_ty);
        let frame = self.temp();
        self.line(&format!(
            "  %{frame} = call ptr @malloc({usize_ty} {frame_size})"
        ));
        let failed = self.temp();
        self.line(&format!("  %{failed} = icmp eq ptr %{frame}, null"));
        self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        let header = self.temp();
        self.line(&format!(
            "  %{header} = getelementptr inbounds {frame_ty}, ptr %{frame}, i32 0, i32 0"
        ));
        let has_previous = self.temp();
        let inherit_label = self.temp();
        let fresh_label = self.temp();
        let preserve_ready_label = self.temp();
        self.line(&format!("  %{has_previous} = icmp ne ptr %previous, null"));
        self.line(&format!(
            "  br i1 %{has_previous}, label %effect.new.inherit{inherit_label}, label %effect.new.fresh{fresh_label}"
        ));
        self.line(&format!("effect.new.inherit{inherit_label}:"));
        let previous_preserve_address = self.temp();
        let previous_preserve = self.temp();
        self.line(&format!(
            "  %{previous_preserve_address} = getelementptr inbounds %g1.effect_frame, ptr %previous, i32 0, i32 10"
        ));
        self.line(&format!(
            "  %{previous_preserve} = load i1, ptr %{previous_preserve_address}"
        ));
        self.line(&format!(
            "  br label %effect.new.preserve.ready{preserve_ready_label}"
        ));
        self.line(&format!("effect.new.fresh{fresh_label}:"));
        self.line(&format!(
            "  br label %effect.new.preserve.ready{preserve_ready_label}"
        ));
        self.line(&format!("effect.new.preserve.ready{preserve_ready_label}:"));
        let inherited_preserve = self.temp();
        self.line(&format!(
            "  %{inherited_preserve} = phi i1 [ %{previous_preserve}, %effect.new.inherit{inherit_label} ], [ false, %effect.new.fresh{fresh_label} ]"
        ));
        for (field, ty, value) in [
            (0, "ptr", "%previous".to_owned()),
            (1, "ptr", format!("@g1_effect_step_f{index}")),
            (2, "ptr", format!("@g1_effect_drop_f{index}")),
            (3, "ptr", "%return_slot".to_owned()),
            (4, "i32", function.entry.to_string()),
            (5, "ptr", "null".to_owned()),
            (6, "ptr", "null".to_owned()),
            (7, "ptr", "%return_init".to_owned()),
            (8, "ptr", format!("@g1_effect_clone_f{index}")),
            (9, "ptr", format!("@g1_effect_fix_snapshot_f{index}")),
            (10, "i1", format!("%{inherited_preserve}")),
        ] {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store {ty} {value}, ptr %{address}"));
        }
        if function.receiver_mode.is_some() {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds {frame_ty}, ptr %{frame}, i32 0, i32 1"
            ));
            self.line(&format!(
                "  store {} %receiver, ptr %{address}",
                register_types[0]
            ));
        }
        for (parameter, ty) in function.params.iter().enumerate() {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds {frame_ty}, ptr %{frame}, i32 0, i32 {}",
                parameter + 2
            ));
            self.line(&format!(
                "  store {} %arg{parameter}, ptr %{address}",
                self.llvm_type(*ty)?
            ));
        }
        let initialized_field = function.register_types.len() + 1;
        for register in 0..function.register_types.len() {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds {frame_ty}, ptr %{frame}, i32 0, i32 {initialized_field}, i32 {register}"
            ));
            let initialized = (function.receiver_mode.is_some() && register == 0)
                || (1..=function.params.len()).contains(&register);
            self.line(&format!(
                "  store i8 {}, ptr %{address}",
                u8::from(initialized)
            ));
        }
        let field_initialized_field = function.register_types.len() + 2;
        for (register, fields) in field_layout.iter().enumerate() {
            let initialized = (function.receiver_mode.is_some() && register == 0)
                || (1..=function.params.len()).contains(&register);
            for field in fields {
                let address = self.temp();
                self.line(&format!(
                    "  %{address} = getelementptr inbounds {frame_ty}, ptr %{frame}, i32 0, i32 {field_initialized_field}, i32 {}",
                    field.owned_mask_index
                ));
                self.line(&format!(
                    "  store i8 {}, ptr %{address}",
                    u8::from(initialized)
                ));
            }
        }
        self.line(&format!("  ret ptr %{frame}"));
        self.line("}");
        self.line("");

        self.emit_effect_callable_starter(index, function)?;

        self.line(&format!(
            "define ptr @g1_effect_clone_f{index}(ptr %source, ptr %previous, ptr %context) {{"
        ));
        let clone_size = self.emit_array_element_size(&frame_ty);
        let clone = self.temp();
        self.line(&format!(
            "  %{clone} = call ptr @malloc({usize_ty} {clone_size})"
        ));
        let clone_failed = self.temp();
        self.line(&format!("  %{clone_failed} = icmp eq ptr %{clone}, null"));
        self.emit_runtime_fault_if(clone_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        self.line(&format!(
            "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{clone}, ptr %source, {usize_ty} {clone_size}, i1 false)"
        ));
        self.line(&format!(
            "  call void @g1_snapshot_record(ptr %context, ptr %source, {usize_ty} {clone_size}, ptr %{clone}, ptr @g1_effect_fix_snapshot_f{index})"
        ));
        let cloned_header = self.temp();
        self.line(&format!(
            "  %{cloned_header} = getelementptr inbounds {frame_ty}, ptr %{clone}, i32 0, i32 0"
        ));
        let cloned_previous_address = self.temp();
        self.line(&format!(
            "  %{cloned_previous_address} = getelementptr inbounds %g1.effect_frame, ptr %{cloned_header}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  store ptr %previous, ptr %{cloned_previous_address}"
        ));
        for field in [3, 7] {
            let source_header = self.temp();
            let source_previous_address = self.temp();
            let source_previous = self.temp();
            let source_pointer_address = self.temp();
            let source_pointer = self.temp();
            let has_previous = self.temp();
            let has_pointer = self.temp();
            let should_rebase = self.temp();
            let rebase_label = self.temp();
            let keep_label = self.temp();
            let join_label = self.temp();
            self.line(&format!(
                "  %{source_header} = getelementptr inbounds {frame_ty}, ptr %source, i32 0, i32 0"
            ));
            self.line(&format!(
                "  %{source_previous_address} = getelementptr inbounds %g1.effect_frame, ptr %{source_header}, i32 0, i32 0"
            ));
            self.line(&format!(
                "  %{source_previous} = load ptr, ptr %{source_previous_address}"
            ));
            self.line(&format!(
                "  %{source_pointer_address} = getelementptr inbounds %g1.effect_frame, ptr %{source_header}, i32 0, i32 {field}"
            ));
            self.line(&format!(
                "  %{source_pointer} = load ptr, ptr %{source_pointer_address}"
            ));
            self.line(&format!(
                "  %{has_previous} = icmp ne ptr %{source_previous}, null"
            ));
            self.line(&format!(
                "  %{has_pointer} = icmp ne ptr %{source_pointer}, null"
            ));
            self.line(&format!(
                "  %{should_rebase} = and i1 %{has_previous}, %{has_pointer}"
            ));
            self.line(&format!(
                "  br i1 %{should_rebase}, label %frame.clone.rebase{rebase_label}, label %frame.clone.keep{keep_label}"
            ));
            self.line(&format!("frame.clone.rebase{rebase_label}:"));
            let source_integer = self.temp();
            let previous_integer = self.temp();
            let offset = self.temp();
            let rebased = self.temp();
            self.line(&format!(
                "  %{source_integer} = ptrtoint ptr %{source_pointer} to {usize_ty}"
            ));
            self.line(&format!(
                "  %{previous_integer} = ptrtoint ptr %{source_previous} to {usize_ty}"
            ));
            self.line(&format!(
                "  %{offset} = sub {usize_ty} %{source_integer}, %{previous_integer}"
            ));
            self.line(&format!(
                "  %{rebased} = getelementptr inbounds i8, ptr %previous, {usize_ty} %{offset}"
            ));
            self.line(&format!("  br label %frame.clone.join{join_label}"));
            self.line(&format!("frame.clone.keep{keep_label}:"));
            self.line(&format!("  br label %frame.clone.join{join_label}"));
            self.line(&format!("frame.clone.join{join_label}:"));
            let final_pointer = self.temp();
            self.line(&format!(
                "  %{final_pointer} = phi ptr [ %{rebased}, %frame.clone.rebase{rebase_label} ], [ %{source_pointer}, %frame.clone.keep{keep_label} ]"
            ));
            let cloned_pointer_address = self.temp();
            self.line(&format!(
                "  %{cloned_pointer_address} = getelementptr inbounds %g1.effect_frame, ptr %{cloned_header}, i32 0, i32 {field}"
            ));
            self.line(&format!(
                "  store ptr %{final_pointer}, ptr %{cloned_pointer_address}"
            ));
        }
        for register in 0..function.register_types.len() {
            let initialized_address = self.temp();
            let initialized = self.temp();
            let full_label = self.temp();
            let done_label = self.temp();
            self.line(&format!(
                "  %{initialized_address} = getelementptr inbounds {frame_ty}, ptr %{clone}, i32 0, i32 {initialized_field}, i32 {register}"
            ));
            self.line(&format!(
                "  %{initialized} = load i8, ptr %{initialized_address}"
            ));
            let value_address = self.temp();
            let value = self.temp();
            let ty = self.llvm_type(function.register_types[register])?;
            self.line(&format!(
                "  %{value_address} = getelementptr inbounds {frame_ty}, ptr %{clone}, i32 0, i32 {}",
                register + 1
            ));
            self.line(&format!("  %{value} = load {ty}, ptr %{value_address}"));
            let full = self.temp();
            self.line(&format!("  %{full} = icmp eq i8 %{initialized}, 1"));
            let direct_fields = field_layout[register].len();
            let partial_label = self.temp();
            if direct_fields == 0 {
                self.line(&format!(
                    "  br i1 %{full}, label %frame.clone.retain{full_label}, label %frame.clone.done{done_label}"
                ));
            } else {
                self.line(&format!(
                    "  br i1 %{full}, label %frame.clone.retain{full_label}, label %frame.clone.partial{partial_label}"
                ));
            }
            self.line(&format!("frame.clone.retain{full_label}:"));
            let cloned_value = self.emit_clone_effect_snapshot_value(
                function.register_types[register],
                &format!("%{value}"),
                function,
                "%context",
            )?;
            self.line(&format!(
                "  store {ty} {cloned_value}, ptr %{value_address}"
            ));
            self.line(&format!("  br label %frame.clone.done{done_label}"));
            if direct_fields != 0 {
                self.line(&format!("frame.clone.partial{partial_label}:"));
                let partial = self.temp();
                let partial_fields_label = self.temp();
                self.line(&format!("  %{partial} = icmp eq i8 %{initialized}, 2"));
                self.line(&format!(
                    "  br i1 %{partial}, label %frame.clone.fields{partial_fields_label}, label %frame.clone.done{done_label}"
                ));
                self.line(&format!("frame.clone.fields{partial_fields_label}:"));
                self.emit_clone_masked_effect_snapshot_fields(
                    function,
                    function.register_types[register],
                    &frame_ty,
                    &format!("%{clone}"),
                    &format!("%{value_address}"),
                    field_initialized_field,
                    &field_layout[register],
                    "%context",
                )?;
                self.line(&format!("  br label %frame.clone.done{done_label}"));
            }
            self.line(&format!("frame.clone.done{done_label}:"));
        }
        let cloned_guards_address = self.temp();
        let cloned_guards = self.temp();
        self.line(&format!(
            "  %{cloned_guards_address} = getelementptr inbounds %g1.effect_frame, ptr %{cloned_header}, i32 0, i32 6"
        ));
        self.line(&format!(
            "  %{cloned_guards} = load ptr, ptr %{cloned_guards_address}"
        ));
        let snapshot_guards = self.emit_clone_effect_snapshot_guard_chain(
            &format!("%{cloned_guards}"),
            function,
            "%context",
        )?;
        self.line(&format!(
            "  store ptr {snapshot_guards}, ptr %{cloned_guards_address}"
        ));
        self.line(&format!("  ret ptr %{clone}"));
        self.line("}");
        self.line("");

        self.line(&format!(
            "define void @g1_effect_fix_snapshot_f{index}(ptr %source, ptr %clone, ptr %context) {{"
        ));
        let cloned_header = self.temp();
        let delimiter_address = self.temp();
        let delimiter = self.temp();
        let fixed_delimiter = self.temp();
        self.line(&format!(
            "  %{cloned_header} = getelementptr inbounds {frame_ty}, ptr %clone, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{delimiter_address} = getelementptr inbounds %g1.effect_frame, ptr %{cloned_header}, i32 0, i32 5"
        ));
        self.line(&format!(
            "  %{delimiter} = load ptr, ptr %{delimiter_address}"
        ));
        self.line(&format!(
            "  %{fixed_delimiter} = call ptr @g1_snapshot_remap(ptr %context, ptr %{delimiter})"
        ));
        self.line(&format!(
            "  store ptr %{fixed_delimiter}, ptr %{delimiter_address}"
        ));
        for register in 0..function.register_types.len() {
            let initialized_address = self.temp();
            let initialized = self.temp();
            let full = self.temp();
            let fix_label = self.temp();
            let done_label = self.temp();
            let partial_label = self.temp();
            let value_address = self.temp();
            let ty = self.llvm_type(function.register_types[register])?;
            self.line(&format!(
                "  %{initialized_address} = getelementptr inbounds {frame_ty}, ptr %clone, i32 0, i32 {initialized_field}, i32 {register}"
            ));
            self.line(&format!(
                "  %{initialized} = load i8, ptr %{initialized_address}"
            ));
            self.line(&format!("  %{full} = icmp eq i8 %{initialized}, 1"));
            self.line(&format!(
                "  %{value_address} = getelementptr inbounds {frame_ty}, ptr %clone, i32 0, i32 {}",
                register + 1
            ));
            let direct_fields = field_layout[register].len();
            if direct_fields == 0 {
                self.line(&format!(
                    "  br i1 %{full}, label %frame.fix.value{fix_label}, label %frame.fix.done{done_label}"
                ));
            } else {
                self.line(&format!(
                    "  br i1 %{full}, label %frame.fix.value{fix_label}, label %frame.fix.partial{partial_label}"
                ));
            }
            self.line(&format!("frame.fix.value{fix_label}:"));
            let value = self.temp();
            self.line(&format!("  %{value} = load {ty}, ptr %{value_address}"));
            let fixed = self.emit_fix_effect_snapshot_value(
                function.register_types[register],
                &format!("%{value}"),
                function,
                "%context",
            )?;
            self.line(&format!("  store {ty} {fixed}, ptr %{value_address}"));
            self.line(&format!("  br label %frame.fix.done{done_label}"));
            if direct_fields != 0 {
                self.line(&format!("frame.fix.partial{partial_label}:"));
                let partial = self.temp();
                let fields_label = self.temp();
                self.line(&format!("  %{partial} = icmp eq i8 %{initialized}, 2"));
                self.line(&format!(
                    "  br i1 %{partial}, label %frame.fix.fields{fields_label}, label %frame.fix.done{done_label}"
                ));
                self.line(&format!("frame.fix.fields{fields_label}:"));
                self.emit_fix_masked_effect_snapshot_fields(
                    function,
                    function.register_types[register],
                    &frame_ty,
                    "%clone",
                    &format!("%{value_address}"),
                    field_initialized_field,
                    &field_layout[register],
                    "%context",
                )?;
                self.line(&format!("  br label %frame.fix.done{done_label}"));
            }
            self.line(&format!("frame.fix.done{done_label}:"));
        }
        self.line("  ret void");
        self.line("}");
        self.line("");

        self.line(&format!(
            "define void @g1_effect_drop_f{index}(ptr %frame) {{"
        ));
        for register in (0..function.register_types.len()).rev() {
            let initialized_address = self.temp();
            let initialized = self.temp();
            let full_label = self.temp();
            let done_label = self.temp();
            self.line(&format!(
                "  %{initialized_address} = getelementptr inbounds {frame_ty}, ptr %frame, i32 0, i32 {initialized_field}, i32 {register}"
            ));
            self.line(&format!(
                "  %{initialized} = load i8, ptr %{initialized_address}"
            ));
            let value_address = self.temp();
            let value = self.temp();
            let ty = self.llvm_type(function.register_types[register])?;
            self.line(&format!(
                "  %{value_address} = getelementptr inbounds {frame_ty}, ptr %frame, i32 0, i32 {}",
                register + 1
            ));
            self.line(&format!("  %{value} = load {ty}, ptr %{value_address}"));
            let full = self.temp();
            self.line(&format!("  %{full} = icmp eq i8 %{initialized}, 1"));
            let direct_fields = field_layout[register].len();
            let partial_label = self.temp();
            if direct_fields == 0 {
                self.line(&format!(
                    "  br i1 %{full}, label %frame.drop{full_label}, label %frame.drop.done{done_label}"
                ));
            } else {
                self.line(&format!(
                    "  br i1 %{full}, label %frame.drop{full_label}, label %frame.drop.partial{partial_label}"
                ));
            }
            self.line(&format!("frame.drop{full_label}:"));
            self.line(&format!("  store i8 0, ptr %{initialized_address}"));
            self.emit_destroy(
                function.register_types[register],
                &format!("%{value}"),
                function,
            )?;
            self.line(&format!("  br label %frame.drop.done{done_label}"));
            if direct_fields != 0 {
                self.line(&format!("frame.drop.partial{partial_label}:"));
                let partial = self.temp();
                let partial_fields_label = self.temp();
                self.line(&format!("  %{partial} = icmp eq i8 %{initialized}, 2"));
                self.line(&format!(
                    "  br i1 %{partial}, label %frame.drop.fields{partial_fields_label}, label %frame.drop.done{done_label}"
                ));
                self.line(&format!("frame.drop.fields{partial_fields_label}:"));
                self.line(&format!("  store i8 0, ptr %{initialized_address}"));
                self.emit_masked_aggregate_fields(
                    function,
                    function.register_types[register],
                    &format!("%{value}"),
                    &frame_ty,
                    "%frame",
                    field_initialized_field,
                    &field_layout[register],
                    false,
                )?;
                self.line(&format!("  br label %frame.drop.done{done_label}"));
            }
            self.line(&format!("frame.drop.done{done_label}:"));
        }
        let header = self.temp();
        let guards_address = self.temp();
        let guards = self.temp();
        self.line(&format!(
            "  %{header} = getelementptr inbounds {frame_ty}, ptr %frame, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{guards_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 6"
        ));
        self.line(&format!("  %{guards} = load ptr, ptr %{guards_address}"));
        self.line(&format!(
            "  call void @g1_effect_guard_release(ptr %{guards})"
        ));
        self.line("  call void @free(ptr %frame)");
        self.line("  ret void");
        self.line("}");
        self.line("");

        self.line(&format!(
            "define void @g1_effect_step_f{index}(ptr %frame, ptr %runtime) {{"
        ));
        let header = self.temp();
        self.line(&format!(
            "  %{header} = getelementptr inbounds {frame_ty}, ptr %frame, i32 0, i32 0"
        ));
        let preserve_address = self.temp();
        let preserve = self.temp();
        let runtime_preserve_address = self.temp();
        self.line(&format!(
            "  %{preserve_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 10"
        ));
        self.line(&format!("  %{preserve} = load i1, ptr %{preserve_address}"));
        self.line(&format!(
            "  %{runtime_preserve_address} = getelementptr inbounds %g1.effect_runtime, ptr %runtime, i32 0, i32 8"
        ));
        self.line(&format!(
            "  store i1 %{preserve}, ptr %{runtime_preserve_address}"
        ));
        for register in 0..function.register_types.len() {
            self.line(&format!(
                "  %r{register} = getelementptr inbounds {frame_ty}, ptr %frame, i32 0, i32 {}",
                register + 1
            ));
            self.line(&format!(
                "  %init{register} = getelementptr inbounds {frame_ty}, ptr %frame, i32 0, i32 {initialized_field}, i32 {register}"
            ));
            for (owned_field, field) in field_layout[register].iter().enumerate() {
                self.line(&format!(
                    "  %fieldinit{register}.{owned_field} = getelementptr inbounds {frame_ty}, ptr %frame, i32 0, i32 {field_initialized_field}, i32 {}",
                    field.owned_mask_index
                ));
            }
        }
        let state_address = self.temp();
        let state = self.temp();
        self.line(&format!(
            "  %{state_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 4"
        ));
        self.line(&format!("  %{state} = load i32, ptr %{state_address}"));
        self.line(&format!("  switch i32 %{state}, label %effect.invalid ["));
        for block in &function.blocks {
            self.line(&format!("    i32 {}, label %bb{}", block.id, block.id));
        }
        self.line("  ]");
        self.line("effect.invalid:");
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        for block in &function.blocks {
            self.line(&format!("bb{}:", block.id));
            for instruction in &block.statements {
                self.emit_effect_instruction(function, &instruction.kind)?;
            }
            self.emit_effect_terminator(index, function, &block.terminator)?;
        }
        self.line("}");
        self.line("");
        Ok(())
    }

    fn emit_effect_callable_starter(
        &mut self,
        index: usize,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let Some(receiver_mode) = function.receiver_mode else {
            return Ok(());
        };
        let capture_type = match (receiver_mode, self.runtime_type(function.receiver_type)?) {
            (0, Type::RefShared { referent }) | (1, Type::RefUnique { referent }) => *referent,
            (2, _) => function.receiver_type,
            _ => {
                return Err(vec![unsupported(
                    function,
                    "effect callable has an invalid receiver layout",
                )]);
            }
        };
        let mut parameters = vec![
            "ptr %callable".to_owned(),
            "i1 %take".to_owned(),
            "ptr %previous".to_owned(),
            "ptr %return_slot".to_owned(),
            "ptr %return_init".to_owned(),
            "ptr %delimiter".to_owned(),
            "ptr %inherited_guards".to_owned(),
        ];
        parameters.extend(
            function
                .params
                .iter()
                .enumerate()
                .map(|(parameter, ty)| {
                    self.llvm_type(*ty)
                        .map(|ty| format!("{ty} %arg{parameter}"))
                })
                .collect::<Result<Vec<_>, _>>()?,
        );
        self.line(&format!(
            "define ptr @g1_effect_start_f{index}({}) {{",
            parameters.join(", ")
        ));
        let capture_address = self.temp();
        let capture_handle = self.temp();
        let data_address = self.temp();
        let capture_data = self.temp();
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr %callable, i32 0, i32 2"
        ));
        self.line(&format!(
            "  %{capture_handle} = load ptr, ptr %{capture_address}"
        ));
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.capture, ptr %{capture_handle}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{capture_data} = load ptr, ptr %{data_address}"
        ));

        let mut constructor_arguments = vec![
            "ptr %previous".to_owned(),
            "ptr %return_slot".to_owned(),
            "ptr %return_init".to_owned(),
        ];
        let final_guards;
        if receiver_mode == 2 {
            let not_take = self.temp();
            self.line(&format!("  %{not_take} = xor i1 %take, true"));
            self.emit_trap_if(not_take);
            let capture_ty = self.llvm_type(capture_type)?;
            let receiver = self.temp();
            self.line(&format!(
                "  %{receiver} = load {capture_ty}, ptr %{capture_data}"
            ));
            let receiver_slot = self.temp();
            let count_address = self.temp();
            let count = self.temp();
            let unique = self.temp();
            let move_label = self.temp();
            let copy_label = self.temp();
            let ready_label = self.temp();
            self.line(&format!("  %{receiver_slot} = alloca {capture_ty}"));
            self.line(&format!(
                "  %{count_address} = getelementptr inbounds %g1.callable, ptr %callable, i32 0, i32 0"
            ));
            self.line(&format!("  %{count} = load i64, ptr %{count_address}"));
            self.line(&format!("  %{unique} = icmp eq i64 %{count}, 1"));
            self.line(&format!(
                "  br i1 %{unique}, label %effect.start.receiver.move{move_label}, label %effect.start.receiver.copy{copy_label}"
            ));
            self.line(&format!("effect.start.receiver.copy{copy_label}:"));
            let copied_receiver = if self.type_contains_array(capture_type, &mut BTreeSet::new())?
                || self.type_contains_resumption(capture_type, &mut BTreeSet::new())?
            {
                let context = self.temp();
                self.line(&format!("  %{context} = alloca ptr"));
                self.line(&format!("  store ptr null, ptr %{context}"));
                let cloned = self.emit_clone_effect_snapshot_value(
                    capture_type,
                    &format!("%{receiver}"),
                    function,
                    &format!("%{context}"),
                )?;
                self.line(&format!("  call void @g1_snapshot_fix_all(ptr %{context})"));
                self.line(&format!("  call void @g1_snapshot_dispose(ptr %{context})"));
                cloned
            } else {
                self.emit_retain(capture_type, &format!("%{receiver}"), function)?;
                format!("%{receiver}")
            };
            self.line(&format!(
                "  store {capture_ty} {copied_receiver}, ptr %{receiver_slot}"
            ));
            self.emit_destroy_callable("%callable", capture_type, function)?;
            self.line(&format!(
                "  br label %effect.start.receiver.ready{ready_label}"
            ));
            self.line(&format!("effect.start.receiver.move{move_label}:"));
            self.line(&format!("  store ptr null, ptr %{data_address}"));
            self.line(&format!("  call void @free(ptr %{capture_data})"));
            self.line(&format!(
                "  store {capture_ty} %{receiver}, ptr %{receiver_slot}"
            ));
            self.emit_destroy_callable("%callable", capture_type, function)?;
            self.line(&format!(
                "  br label %effect.start.receiver.ready{ready_label}"
            ));
            self.line(&format!("effect.start.receiver.ready{ready_label}:"));
            let final_receiver = self.temp();
            self.line(&format!(
                "  %{final_receiver} = load {capture_ty}, ptr %{receiver_slot}"
            ));
            constructor_arguments.push(format!("{capture_ty} %{final_receiver}"));
            final_guards = "%inherited_guards".to_owned();
        } else {
            let retain_label = self.temp();
            let retained_label = self.temp();
            self.line(&format!(
                "  br i1 %take, label %effect.start.retained{retained_label}, label %effect.start.retain{retain_label}"
            ));
            self.line(&format!("effect.start.retain{retain_label}:"));
            let count_address = self.temp();
            let count = self.temp();
            let next = self.temp();
            self.line(&format!(
                "  %{count_address} = getelementptr inbounds %g1.callable, ptr %callable, i32 0, i32 0"
            ));
            self.line(&format!("  %{count} = load i64, ptr %{count_address}"));
            self.line(&format!("  %{next} = add i64 %{count}, 1"));
            self.line(&format!("  store i64 %{next}, ptr %{count_address}"));
            self.line(&format!(
                "  br label %effect.start.retained{retained_label}"
            ));
            self.line(&format!("effect.start.retained{retained_label}:"));
            constructor_arguments.push(format!(
                "{} %{capture_data}",
                self.llvm_type(function.receiver_type)?
            ));
            let guard_size = self.emit_array_element_size("%g1.effect_guard");
            let usize_ty = format!("i{}", self.pointer_width());
            let guard = self.temp();
            let failed = self.temp();
            self.line(&format!(
                "  %{guard} = call ptr @malloc({usize_ty} {guard_size})"
            ));
            self.line(&format!("  %{failed} = icmp eq ptr %{guard}, null"));
            self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
            for (field, ty, value) in [
                (0, "i64", "1".to_owned()),
                (1, "ptr", "%callable".to_owned()),
                (2, "ptr", format!("@g1_effect_guard_drop_f{index}")),
                (3, "ptr", "%inherited_guards".to_owned()),
            ] {
                let address = self.temp();
                self.line(&format!(
                    "  %{address} = getelementptr inbounds %g1.effect_guard, ptr %{guard}, i32 0, i32 {field}"
                ));
                self.line(&format!("  store {ty} {value}, ptr %{address}"));
            }
            final_guards = format!("%{guard}");
        }
        constructor_arguments.extend(
            function
                .params
                .iter()
                .enumerate()
                .map(|(parameter, ty)| Ok(format!("{} %arg{parameter}", self.llvm_type(*ty)?)))
                .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?,
        );
        let frame = self.temp();
        self.line(&format!(
            "  %{frame} = call ptr @g1_effect_new_f{index}({})",
            constructor_arguments.join(", ")
        ));
        for (field, value) in [(5, "%delimiter"), (6, final_guards.as_str())] {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_frame, ptr %{frame}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store ptr {value}, ptr %{address}"));
        }
        self.line(&format!("  ret ptr %{frame}"));
        self.line("}");
        self.line("");

        self.line(&format!(
            "define internal void @g1_effect_guard_drop_f{index}(ptr %callable) {{"
        ));
        self.emit_destroy_callable("%callable", capture_type, function)?;
        self.line("  ret void");
        self.line("}");
        self.line("");
        Ok(())
    }

    fn emit_effect_terminator(
        &mut self,
        function_index: usize,
        function: &mir::Function,
        terminator: &Terminator,
    ) -> Result<(), Vec<Diagnostic>> {
        match terminator {
            Terminator::Goto(edge) => self.emit_effect_edge(function, edge, BTreeSet::new())?,
            Terminator::Switch {
                discr,
                cases,
                otherwise,
            } => {
                let ty = self.register_type(function, discr.register)?;
                let value = self.load_operand(function, discr)?;
                if discr.mode == mir::UseMode::Move {
                    self.emit_effect_set_initialized(function, discr.register, false)?;
                }
                let switch_id = self.temp();
                let otherwise_label = self.temp();
                let case_labels = cases.iter().map(|_| self.temp()).collect::<Vec<_>>();
                self.line(&format!(
                    "  switch {ty} {value}, label %effect.switch{switch_id}.{otherwise_label} ["
                ));
                for ((constant, _), label) in cases.iter().zip(&case_labels) {
                    self.line(&format!(
                        "    {ty} {}, label %effect.switch{switch_id}.{label}",
                        llvm_scalar_constant(constant)?,
                    ));
                }
                self.line("  ]");
                self.line(&format!("effect.switch{switch_id}.{otherwise_label}:"));
                self.emit_effect_edge(function, otherwise, BTreeSet::new())?;
                for ((_, edge), label) in cases.iter().zip(case_labels) {
                    self.line(&format!("effect.switch{switch_id}.{label}:"));
                    self.emit_effect_edge(function, edge, BTreeSet::new())?;
                }
            }
            Terminator::Return { value } => {
                let header = self.temp();
                let return_address = self.temp();
                let return_slot = self.temp();
                self.line(&format!(
                    "  %{header} = getelementptr inbounds {}, ptr %frame, i32 0, i32 0",
                    self.effect_frame_type(function_index)
                ));
                self.line(&format!(
                    "  %{return_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 3"
                ));
                self.line(&format!(
                    "  %{return_slot} = load ptr, ptr %{return_address}"
                ));
                if let Some(value) = value {
                    let ty = self.register_type(function, value.register)?;
                    let loaded = self.load_operand(function, value)?;
                    if value.mode == mir::UseMode::Copy {
                        let runtime_ty = self.register_runtime_type(function, value.register)?;
                        self.emit_retain(runtime_ty, &loaded, function)?;
                    } else {
                        self.emit_effect_set_initialized(function, value.register, false)?;
                    }
                    self.line(&format!("  store {ty} {loaded}, ptr %{return_slot}"));
                    let return_init_address = self.temp();
                    let return_init = self.temp();
                    self.line(&format!(
                        "  %{return_init_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 7"
                    ));
                    self.line(&format!(
                        "  %{return_init} = load ptr, ptr %{return_init_address}"
                    ));
                    let has_return_init = self.temp();
                    let mark_label = self.temp();
                    let marked_label = self.temp();
                    self.line(&format!(
                        "  %{has_return_init} = icmp ne ptr %{return_init}, null"
                    ));
                    self.line(&format!(
                        "  br i1 %{has_return_init}, label %effect.return.mark{mark_label}, label %effect.return.marked{marked_label}"
                    ));
                    self.line(&format!("effect.return.mark{mark_label}:"));
                    self.line(&format!("  store i8 1, ptr %{return_init}"));
                    self.line(&format!("  br label %effect.return.marked{marked_label}"));
                    self.line(&format!("effect.return.marked{marked_label}:"));
                } else if matches!(self.runtime_type(function.result)?, Type::Unit) {
                    self.emit_effect_store_optional_unit_return(
                        &format!("%{header}"),
                        &format!("%{return_slot}"),
                    );
                }
                let previous_address = self.temp();
                let previous = self.temp();
                let root = self.temp();
                let root_label = self.temp();
                let caller_label = self.temp();
                self.line(&format!(
                    "  %{previous_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{previous} = load ptr, ptr %{previous_address}"
                ));
                self.line(&format!("  %{root} = icmp eq ptr %{previous}, null"));
                self.line(&format!(
                    "  br i1 %{root}, label %effect.return.root{root_label}, label %effect.return.caller{caller_label}"
                ));
                self.line(&format!("effect.return.caller{caller_label}:"));
                self.emit_effect_runtime_store(0, "ptr", &format!("%{previous}"));
                self.line(&format!(
                    "  call void @g1_effect_drop_f{function_index}(ptr %frame)"
                ));
                self.line("  ret void");
                self.line(&format!("effect.return.root{root_label}:"));
                self.emit_effect_runtime_store(1, "i32", "0");
                self.emit_effect_runtime_store(5, "ptr", "%frame");
                self.emit_effect_runtime_store(0, "ptr", "null");
                self.line("  ret void");
            }
            Terminator::Call {
                result,
                function: callee,
                args,
                normal,
            } => self.emit_effect_call(function, *result, *callee as usize, args, normal)?,
            Terminator::CallSelf {
                result,
                args,
                normal,
            } => self.emit_effect_call(function, *result, function_index, args, normal)?,
            Terminator::CallKnownReceiver {
                result,
                function: callee,
                receiver,
                args,
                normal,
            } => self.emit_effect_known_receiver_call(
                function,
                *result,
                *callee as usize,
                receiver,
                args,
                normal,
            )?,
            Terminator::HostCall {
                result,
                import,
                args,
                normal,
            } => {
                let returned = self.emit_host_invocation(function, *result, *import, args)?;
                for operand in args {
                    if operand.mode == mir::UseMode::Move {
                        self.emit_effect_set_initialized(function, operand.register, false)?;
                    }
                }
                if let Some(dst) = result {
                    if let Some(value) = returned {
                        self.line(&format!("  store ptr %{value}, ptr %r{dst}"));
                    } else if matches!(
                        self.runtime_type(self.register_runtime_type(function, *dst)?)?,
                        Type::Unit
                    ) {
                        self.line(&format!("  store i8 0, ptr %r{dst}"));
                    } else {
                        return Err(vec![unsupported(
                            function,
                            "host call returned no value for a non-Unit result",
                        )]);
                    }
                    self.emit_effect_set_initialized(function, *dst, true)?;
                }
                self.emit_effect_edge(function, normal, result.iter().copied().collect())?;
            }
            Terminator::CallIndirect {
                result,
                callable,
                known_function,
                receiver_mode,
                cleanup_callable,
                args,
                normal,
            } => self.emit_effect_indirect_call(
                function,
                *result,
                callable,
                *known_function,
                *receiver_mode,
                *cleanup_callable,
                args,
                normal,
            )?,
            Terminator::TailCall {
                function: callee,
                args,
            } => {
                self.emit_effect_tail_call(function, function_index, *callee as usize, None, args)?
            }
            Terminator::TailCallSelf { args } => {
                let receiver = function.receiver_mode.map(|_| mir::Operand {
                    register: 0,
                    mode: mir::UseMode::Move,
                });
                self.emit_effect_tail_call(
                    function,
                    function_index,
                    function_index,
                    receiver.as_ref(),
                    args,
                )?
            }
            Terminator::TailCallKnownReceiver {
                function: callee,
                receiver,
                args,
            } => self.emit_effect_tail_call(
                function,
                function_index,
                *callee as usize,
                Some(receiver),
                args,
            )?,
            Terminator::TailCallIndirect {
                callable,
                known_function,
                receiver_mode,
                args,
            } => self.emit_effect_tail_indirect_call(
                function,
                function_index,
                callable,
                *known_function,
                *receiver_mode,
                args,
            )?,
            Terminator::Handle {
                result,
                handler,
                body,
                normal,
            } => {
                self.emit_effect_handle(function_index, function, *result, handler, body, normal)?
            }
            Terminator::Resume {
                result,
                resumption,
                receiver_mode,
                value,
                normal,
            } => self.emit_effect_resume(
                function,
                *result,
                resumption,
                *receiver_mode,
                value,
                normal,
            )?,
            Terminator::TailResume {
                resumption,
                receiver_mode,
                value,
            } => self.emit_effect_tail_resume(
                function_index,
                function,
                resumption,
                *receiver_mode,
                value,
            )?,
            Terminator::Cancel {
                result,
                resumption,
                normal,
            } => self.emit_effect_cancel(function, *result, resumption, normal)?,
            Terminator::Perform {
                result,
                protocol,
                operation,
                payloads,
                capture,
                resume,
            } => {
                if let Some(resume) = resume {
                    let state_address = self.temp();
                    self.line(&format!(
                        "  %{state_address} = getelementptr inbounds %g1.effect_frame, ptr %frame, i32 0, i32 4"
                    ));
                    self.line(&format!(
                        "  store i32 {}, ptr %{state_address}",
                        resume.target
                    ));
                    self.emit_edge_arguments(function, resume, result.iter().copied().collect())?;
                }
                let payload_types = payloads
                    .iter()
                    .map(|payload| self.register_type(function, payload.register))
                    .collect::<Result<Vec<_>, _>>()?;
                let payload_ty = format!("{{ {} }}", payload_types.join(", "));
                let payload_size = self.emit_array_element_size(&payload_ty);
                let usize_ty = format!("i{}", self.pointer_width());
                let payload = self.temp();
                self.line(&format!(
                    "  %{payload} = call ptr @malloc({usize_ty} {payload_size})"
                ));
                let failed = self.temp();
                self.line(&format!("  %{failed} = icmp eq ptr %{payload}, null"));
                self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
                for (index, (operand, ty)) in payloads.iter().zip(&payload_types).enumerate() {
                    let value = self.load_operand(function, operand)?;
                    if operand.mode == mir::UseMode::Copy {
                        let runtime_ty = self.register_runtime_type(function, operand.register)?;
                        self.emit_retain(runtime_ty, &value, function)?;
                    } else {
                        self.emit_effect_set_initialized(function, operand.register, false)?;
                    }
                    let slot = self.temp();
                    self.line(&format!(
                        "  %{slot} = getelementptr inbounds {payload_ty}, ptr %{payload}, i32 0, i32 {index}"
                    ));
                    self.line(&format!("  store {ty} {value}, ptr %{slot}"));
                }
                let _ = capture;
                self.emit_effect_runtime_store(1, "i32", "1");
                self.emit_effect_runtime_store(2, "i32", &protocol.to_string());
                self.emit_effect_runtime_store(3, "i32", &operation.to_string());
                self.emit_effect_runtime_store(4, "ptr", &format!("%{payload}"));
                self.emit_effect_runtime_store(5, "ptr", "%frame");
                self.emit_effect_runtime_store(
                    6,
                    "ptr",
                    &result.map_or_else(|| "null".to_owned(), |result| format!("%r{result}")),
                );
                self.emit_effect_runtime_store(
                    7,
                    "ptr",
                    &result.map_or_else(|| "null".to_owned(), |result| format!("%init{result}")),
                );
                self.emit_effect_runtime_store(0, "ptr", "null");
                self.line("  ret void");
            }
            Terminator::Leave { target, .. } => {
                self.emit_effect_edge(function, target, BTreeSet::new())?
            }
            Terminator::Abort { message } => self.emit_abort(message.as_deref()),
            Terminator::Unreachable => {
                self.line("  call void @llvm.trap()");
                self.line("  unreachable");
            }
        }
        Ok(())
    }

    fn emit_effect_handle(
        &mut self,
        function_index: usize,
        function: &mir::Function,
        result: u32,
        handler_operand: &mir::Operand,
        body_operand: &mir::Operand,
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        if handler_operand.mode != mir::UseMode::Move || body_operand.mode != mir::UseMode::Move {
            return Err(vec![unsupported(
                function,
                "effect-frame handlers require owned handler and body operands",
            )]);
        }
        let handler_type = self.register_runtime_type(function, handler_operand.register)?;
        let Type::Handler {
            handler_def,
            capture_type: clause_tuple,
            ..
        } = self.runtime_type(handler_type)?.clone()
        else {
            return Err(vec![unsupported(
                function,
                "effect-frame Handle with a non-handler value",
            )]);
        };
        let definition = self
            .phases
            .artifact
            .handler_defs
            .get(handler_def as usize)
            .ok_or_else(|| vec![unsupported(function, "Handle descriptor is missing")])?;
        if self.runtime_aggregate_fields(clause_tuple)?.len() != definition.clauses.len() {
            return Err(vec![unsupported(
                function,
                "handler clause layout does not match its descriptor",
            )]);
        }
        let body_type = self.register_runtime_type(function, body_operand.register)?;
        let Type::Callable {
            signature,
            receiver_mode,
            ..
        } = self.runtime_type(body_type)?.clone()
        else {
            return Err(vec![unsupported(function, "Handle body is not callable")]);
        };
        if receiver_mode != 2
            || !signature.params.is_empty()
            || signature.result != definition.result_type
            || self.register_runtime_type(function, result)? != definition.result_type
        {
            return Err(vec![unsupported(
                function,
                "malformed effect-frame Handle body",
            )]);
        }

        let state_address = self.temp();
        self.line(&format!(
            "  %{state_address} = getelementptr inbounds %g1.effect_frame, ptr %frame, i32 0, i32 4"
        ));
        self.line(&format!(
            "  store i32 {}, ptr %{state_address}",
            normal.target
        ));
        self.emit_edge_arguments(function, normal, [result].into_iter().collect())?;

        let handler = self.load_operand(function, handler_operand)?;
        let body = self.load_operand(function, body_operand)?;
        self.emit_effect_set_initialized(function, handler_operand.register, false)?;
        self.emit_effect_set_initialized(function, body_operand.register, false)?;

        let header = self.temp();
        let guards_address = self.temp();
        let guards = self.temp();
        self.line(&format!(
            "  %{header} = getelementptr inbounds {}, ptr %frame, i32 0, i32 0",
            self.effect_frame_type(function_index)
        ));
        self.line(&format!(
            "  %{guards_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 6"
        ));
        self.line(&format!("  %{guards} = load ptr, ptr %{guards_address}"));
        let activation = self.emit_allocate_handler_activation(
            &handler,
            handler_def,
            &format!("%{guards}"),
            true,
        );
        let starter_address = self.temp();
        let starter = self.temp();
        let missing = self.temp();
        self.line(&format!(
            "  %{starter_address} = getelementptr inbounds %g1.callable, ptr {body}, i32 0, i32 3"
        ));
        self.line(&format!("  %{starter} = load ptr, ptr %{starter_address}"));
        self.line(&format!("  %{missing} = icmp eq ptr %{starter}, null"));
        self.emit_trap_if(missing);
        let child = self.temp();
        self.line(&format!(
            "  %{child} = call ptr %{starter}(ptr {body}, i1 true, ptr %frame, ptr %r{result}, ptr %init{result}, ptr {activation}, ptr {activation})"
        ));
        self.emit_effect_runtime_store(0, "ptr", &format!("%{child}"));
        self.line("  ret void");
        Ok(())
    }

    fn emit_effect_tail_call(
        &mut self,
        caller: &mir::Function,
        caller_index: usize,
        callee_index: usize,
        receiver: Option<&mir::Operand>,
        args: &[mir::Operand],
    ) -> Result<(), Vec<Diagnostic>> {
        let callee = self
            .phases
            .mir
            .functions
            .get(callee_index)
            .cloned()
            .ok_or_else(|| vec![unsupported(caller, "effect tail-call target is missing")])?;
        if !self.function_needs_effect_frame(&callee) {
            return self.emit_effect_sync_tail_call(
                caller,
                caller_index,
                callee_index,
                &callee,
                receiver,
                args,
            );
        }
        if callee.params.len() != args.len()
            || receiver.is_some() != callee.receiver_mode.is_some()
            || receiver.is_some() && callee.receiver_mode != Some(0) && callee_index != caller_index
            || callee.result != caller.result
        {
            return Err(vec![unsupported(
                caller,
                "malformed outward-effect tail call",
            )]);
        }
        let header = self.temp();
        self.line(&format!(
            "  %{header} = getelementptr inbounds {}, ptr %frame, i32 0, i32 0",
            self.effect_frame_type(caller_index)
        ));
        let mut inherited = Vec::new();
        for (field, ty) in [(0, "ptr"), (3, "ptr"), (7, "ptr"), (5, "ptr"), (6, "ptr")] {
            let address = self.temp();
            let value = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 {field}"
            ));
            self.line(&format!("  %{value} = load {ty}, ptr %{address}"));
            inherited.push(format!("%{value}"));
        }
        let mut arguments = Vec::with_capacity(args.len() + usize::from(receiver.is_some()));
        if let Some(receiver) = receiver {
            let actual = self.register_runtime_type(caller, receiver.register)?;
            if actual != callee.receiver_type {
                return Err(vec![unsupported(
                    caller,
                    "known tail receiver type mismatch",
                )]);
            }
            let ty = self.register_type(caller, receiver.register)?;
            let value = self.load_operand(caller, receiver)?;
            if receiver.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, receiver.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        for (operand, expected) in args.iter().zip(&callee.params) {
            let actual = self.register_runtime_type(caller, operand.register)?;
            if actual != *expected {
                return Err(vec![unsupported(
                    caller,
                    "outward tail-call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, operand.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let suffix = if arguments.is_empty() {
            String::new()
        } else {
            format!(", {}", arguments.join(", "))
        };
        let replacement = self.temp();
        self.line(&format!(
            "  %{replacement} = call ptr @g1_effect_new_f{callee_index}(ptr {}, ptr {}, ptr {}{suffix})",
            inherited[0], inherited[1], inherited[2]
        ));
        for (field, value) in [(5, &inherited[3]), (6, &inherited[4])] {
            let address = self.temp();
            let old_address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_frame, ptr %{replacement}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store ptr {value}, ptr %{address}"));
            self.line(&format!(
                "  %{old_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store ptr null, ptr %{old_address}"));
        }
        self.emit_effect_runtime_store(0, "ptr", &format!("%{replacement}"));
        self.line(&format!(
            "  call void @g1_effect_drop_f{caller_index}(ptr %frame)"
        ));
        self.line("  ret void");
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_effect_indirect_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callable_operand: &mir::Operand,
        known_function: Option<u32>,
        requested_mode: u32,
        cleanup_callable: bool,
        args: &[mir::Operand],
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let callable_type = self.register_runtime_type(caller, callable_operand.register)?;
        let Type::Callable {
            signature,
            receiver_mode,
            ..
        } = self.runtime_type(callable_type)?.clone()
        else {
            return Err(vec![unsupported(
                caller,
                "effect indirect call through a non-callable value",
            )]);
        };
        if signature.outward_protocols.is_empty() {
            return self.emit_effect_sync_indirect_call(
                caller,
                result,
                callable_operand,
                known_function,
                requested_mode,
                cleanup_callable,
                args,
                normal,
            );
        }
        if requested_mode > 2
            || requested_mode < receiver_mode
            || signature.params.len() != args.len()
            || result.is_none() && self.llvm_return_type(signature.result)? != "void"
        {
            return Err(vec![unsupported(
                caller,
                "malformed outward-effect indirect call",
            )]);
        }
        if let Some(target) = known_function {
            let target = self
                .phases
                .mir
                .functions
                .get(target as usize)
                .ok_or_else(|| vec![unsupported(caller, "missing known indirect-call target")])?;
            if target.receiver_mode != Some(receiver_mode)
                || target.params != signature.params
                || target.result != signature.result
                || target.outward_protocols != signature.outward_protocols
            {
                return Err(vec![unsupported(
                    caller,
                    "known outward indirect-call target does not match its callable type",
                )]);
            }
        }

        let state_address = self.temp();
        self.line(&format!(
            "  %{state_address} = getelementptr inbounds %g1.effect_frame, ptr %frame, i32 0, i32 4"
        ));
        self.line(&format!(
            "  store i32 {}, ptr %{state_address}",
            normal.target
        ));
        self.emit_edge_arguments(caller, normal, result.into_iter().collect())?;

        let callable = self.load_operand(caller, callable_operand)?;
        let take = callable_operand.mode == mir::UseMode::Move || cleanup_callable;
        if receiver_mode == 2 && !take {
            return Err(vec![unsupported(
                caller,
                "owned outward callable invoked without transferring its shell",
            )]);
        }
        if take {
            self.emit_effect_set_initialized(caller, callable_operand.register, false)?;
        }
        let starter_address = self.temp();
        let starter = self.temp();
        let missing = self.temp();
        self.line(&format!(
            "  %{starter_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 3"
        ));
        self.line(&format!("  %{starter} = load ptr, ptr %{starter_address}"));
        self.line(&format!("  %{missing} = icmp eq ptr %{starter}, null"));
        self.emit_trap_if(missing);

        let mut arguments = Vec::with_capacity(args.len());
        for (operand, expected) in args.iter().zip(&signature.params) {
            let actual = self.register_runtime_type(caller, operand.register)?;
            if actual != *expected {
                return Err(vec![unsupported(
                    caller,
                    "outward indirect-call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, operand.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let suffix = if arguments.is_empty() {
            String::new()
        } else {
            format!(", {}", arguments.join(", "))
        };
        let return_slot = result.map_or_else(|| "null".to_owned(), |result| format!("%r{result}"));
        let return_init =
            result.map_or_else(|| "null".to_owned(), |result| format!("%init{result}"));
        let child = self.temp();
        self.line(&format!(
            "  %{child} = call ptr %{starter}(ptr {callable}, i1 {}, ptr %frame, ptr {return_slot}, ptr {return_init}, ptr null, ptr null{suffix})",
            if take { "true" } else { "false" }
        ));
        self.emit_effect_runtime_store(0, "ptr", &format!("%{child}"));
        self.line("  ret void");
        Ok(())
    }

    fn emit_effect_tail_indirect_call(
        &mut self,
        caller: &mir::Function,
        caller_index: usize,
        callable_operand: &mir::Operand,
        known_function: Option<u32>,
        requested_mode: u32,
        args: &[mir::Operand],
    ) -> Result<(), Vec<Diagnostic>> {
        let callable_type = self.register_runtime_type(caller, callable_operand.register)?;
        let Type::Callable {
            signature,
            receiver_mode,
            ..
        } = self.runtime_type(callable_type)?.clone()
        else {
            return Err(vec![unsupported(
                caller,
                "effect tail call through a non-callable value",
            )]);
        };
        if signature.outward_protocols.is_empty() {
            return self.emit_effect_sync_tail_indirect_call(
                caller,
                caller_index,
                callable_operand,
                known_function,
                requested_mode,
                args,
            );
        }
        if requested_mode != 2
            || callable_operand.mode != mir::UseMode::Move
            || requested_mode < receiver_mode
            || signature.params.len() != args.len()
            || signature.result != caller.result
        {
            return Err(vec![unsupported(
                caller,
                "malformed outward-effect indirect tail call",
            )]);
        }
        if let Some(target) = known_function {
            let target = self
                .phases
                .mir
                .functions
                .get(target as usize)
                .ok_or_else(|| vec![unsupported(caller, "missing known indirect-call target")])?;
            if target.receiver_mode != Some(receiver_mode)
                || target.params != signature.params
                || target.result != signature.result
                || target.outward_protocols != signature.outward_protocols
            {
                return Err(vec![unsupported(
                    caller,
                    "known outward indirect tail-call target does not match its callable type",
                )]);
            }
        }

        let header = self.temp();
        self.line(&format!(
            "  %{header} = getelementptr inbounds {}, ptr %frame, i32 0, i32 0",
            self.effect_frame_type(caller_index)
        ));
        let mut inherited = Vec::new();
        for field in [0, 3, 7, 5, 6] {
            let address = self.temp();
            let value = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 {field}"
            ));
            self.line(&format!("  %{value} = load ptr, ptr %{address}"));
            inherited.push(format!("%{value}"));
        }

        let callable = self.load_operand(caller, callable_operand)?;
        self.emit_effect_set_initialized(caller, callable_operand.register, false)?;
        let starter_address = self.temp();
        let starter = self.temp();
        let missing = self.temp();
        self.line(&format!(
            "  %{starter_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 3"
        ));
        self.line(&format!("  %{starter} = load ptr, ptr %{starter_address}"));
        self.line(&format!("  %{missing} = icmp eq ptr %{starter}, null"));
        self.emit_trap_if(missing);
        let mut arguments = Vec::with_capacity(args.len());
        for (operand, expected) in args.iter().zip(&signature.params) {
            let actual = self.register_runtime_type(caller, operand.register)?;
            if actual != *expected {
                return Err(vec![unsupported(
                    caller,
                    "outward indirect tail-call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, operand.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let suffix = if arguments.is_empty() {
            String::new()
        } else {
            format!(", {}", arguments.join(", "))
        };
        let replacement = self.temp();
        self.line(&format!(
            "  %{replacement} = call ptr %{starter}(ptr {callable}, i1 true, ptr {}, ptr {}, ptr {}, ptr {}, ptr {}{suffix})",
            inherited[0], inherited[1], inherited[2], inherited[3], inherited[4]
        ));
        for field in [5, 6] {
            let old_address = self.temp();
            self.line(&format!(
                "  %{old_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store ptr null, ptr %{old_address}"));
        }
        self.emit_effect_runtime_store(0, "ptr", &format!("%{replacement}"));
        self.line(&format!(
            "  call void @g1_effect_drop_f{caller_index}(ptr %frame)"
        ));
        self.line("  ret void");
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_effect_sync_indirect_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callable_operand: &mir::Operand,
        known_function: Option<u32>,
        requested_mode: u32,
        cleanup_callable: bool,
        args: &[mir::Operand],
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let (result_type, returned) = self.emit_effect_sync_indirect_invoke(
            caller,
            callable_operand,
            known_function,
            requested_mode,
            cleanup_callable,
            args,
        )?;
        let result_ty = self.llvm_return_type(result_type)?;
        match (result, returned) {
            (Some(result), Some(value)) => {
                self.line(&format!("  store {result_ty} %{value}, ptr %r{result}"));
                self.emit_effect_set_initialized(caller, result, true)?;
            }
            (Some(result), None) => {
                self.line(&format!("  store i8 0, ptr %r{result}"));
                self.emit_effect_set_initialized(caller, result, true)?;
            }
            (None, Some(_)) => {
                return Err(vec![unsupported(
                    caller,
                    "discarded non-unit synchronous indirect-call result",
                )]);
            }
            (None, None) => {}
        }
        self.emit_effect_edge(caller, normal, result.into_iter().collect())
    }

    fn emit_effect_sync_tail_indirect_call(
        &mut self,
        caller: &mir::Function,
        caller_index: usize,
        callable_operand: &mir::Operand,
        known_function: Option<u32>,
        requested_mode: u32,
        args: &[mir::Operand],
    ) -> Result<(), Vec<Diagnostic>> {
        let (result_type, returned) = self.emit_effect_sync_indirect_invoke(
            caller,
            callable_operand,
            known_function,
            requested_mode,
            false,
            args,
        )?;
        if result_type != caller.result {
            return Err(vec![unsupported(
                caller,
                "synchronous indirect tail-call result type mismatch",
            )]);
        }
        if returned.is_none() && matches!(self.runtime_type(result_type)?, Type::Unit) {
            let header = self.temp();
            let return_address = self.temp();
            let return_slot = self.temp();
            self.line(&format!(
                "  %{header} = getelementptr inbounds {}, ptr %frame, i32 0, i32 0",
                self.effect_frame_type(caller_index)
            ));
            self.line(&format!(
                "  %{return_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 3"
            ));
            self.line(&format!(
                "  %{return_slot} = load ptr, ptr %{return_address}"
            ));
            self.emit_effect_store_optional_unit_return(
                &format!("%{header}"),
                &format!("%{return_slot}"),
            );
        }
        let returned = match returned {
            Some(value) => Some((self.llvm_return_type(result_type)?, format!("%{value}"))),
            None => None,
        };
        self.emit_effect_finish_frame(caller_index, returned.as_ref())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_effect_sync_indirect_invoke(
        &mut self,
        caller: &mir::Function,
        callable_operand: &mir::Operand,
        known_function: Option<u32>,
        requested_mode: u32,
        cleanup_callable: bool,
        args: &[mir::Operand],
    ) -> Result<(TypeId, Option<Temporary>), Vec<Diagnostic>> {
        let callable_type = self.register_runtime_type(caller, callable_operand.register)?;
        let Type::Callable {
            signature,
            capture_type,
            receiver_mode,
            ..
        } = self.runtime_type(callable_type)?.clone()
        else {
            return Err(vec![unsupported(
                caller,
                "synchronous indirect call through a non-callable value",
            )]);
        };
        if !signature.outward_protocols.is_empty()
            || requested_mode > 2
            || requested_mode < receiver_mode
            || signature.params.len() != args.len()
            || requested_mode == 2 && callable_operand.mode != mir::UseMode::Move
            || requested_mode != 2 && callable_operand.mode != mir::UseMode::Copy
            || requested_mode == 2 && cleanup_callable
        {
            return Err(vec![unsupported(
                caller,
                "malformed synchronous indirect call from an effect frame",
            )]);
        }
        if let Some(target) = known_function {
            let target = self
                .phases
                .mir
                .functions
                .get(target as usize)
                .ok_or_else(|| vec![unsupported(caller, "missing known indirect-call target")])?;
            if target.receiver_mode != Some(receiver_mode)
                || target.params != signature.params
                || target.result != signature.result
                || !target.outward_protocols.is_empty()
            {
                return Err(vec![unsupported(
                    caller,
                    "known synchronous indirect-call target does not match its callable type",
                )]);
            }
        }

        let callable = self.load_operand(caller, callable_operand)?;
        let function_address = self.temp();
        let target = self.temp();
        self.line(&format!(
            "  %{function_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 1"
        ));
        self.line(&format!("  %{target} = load ptr, ptr %{function_address}"));
        let capture_address = self.temp();
        let capture_handle = self.temp();
        let data_address = self.temp();
        let capture_data = self.temp();
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 2"
        ));
        self.line(&format!(
            "  %{capture_handle} = load ptr, ptr %{capture_address}"
        ));
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.capture, ptr %{capture_handle}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{capture_data} = load ptr, ptr %{data_address}"
        ));

        let mut arguments = Vec::with_capacity(args.len() + 1);
        if receiver_mode == 2 {
            let capture_ty = self.llvm_type(capture_type)?;
            let receiver = self.temp();
            self.line(&format!(
                "  %{receiver} = load {capture_ty}, ptr %{capture_data}"
            ));
            self.line(&format!("  store ptr null, ptr %{data_address}"));
            self.line(&format!("  call void @free(ptr %{capture_data})"));
            self.emit_release_capture(&format!("%{capture_handle}"), capture_type, caller)?;
            self.line(&format!("  call void @free(ptr {callable})"));
            self.emit_effect_set_initialized(caller, callable_operand.register, false)?;
            arguments.push(format!("{capture_ty} %{receiver}"));
        } else {
            arguments.push(format!("ptr %{capture_data}"));
        }
        for (operand, expected) in args.iter().zip(&signature.params) {
            let actual = self.register_runtime_type(caller, operand.register)?;
            if actual != *expected {
                return Err(vec![unsupported(
                    caller,
                    "synchronous indirect-call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, operand.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let result_ty = self.llvm_return_type(signature.result)?;
        let returned = if result_ty == "void" {
            self.line(&format!("  call void %{target}({})", arguments.join(", ")));
            None
        } else {
            let returned = self.temp();
            self.line(&format!(
                "  %{returned} = call {result_ty} %{target}({})",
                arguments.join(", ")
            ));
            Some(returned)
        };
        if receiver_mode != 2 && (requested_mode == 2 || cleanup_callable) {
            self.emit_destroy(callable_type, &callable, caller)?;
            self.emit_effect_set_initialized(caller, callable_operand.register, false)?;
        }
        Ok((signature.result, returned))
    }

    fn emit_effect_sync_tail_call(
        &mut self,
        caller: &mir::Function,
        caller_index: usize,
        callee_index: usize,
        callee: &mir::Function,
        receiver: Option<&mir::Operand>,
        args: &[mir::Operand],
    ) -> Result<(), Vec<Diagnostic>> {
        if callee.params.len() != args.len()
            || receiver.is_some() != callee.receiver_mode.is_some()
            || receiver.is_some() && callee.receiver_mode != Some(0)
        {
            return Err(vec![unsupported(
                caller,
                "malformed synchronous tail call from an effect frame",
            )]);
        }
        let mut arguments = Vec::with_capacity(args.len() + usize::from(receiver.is_some()));
        if let Some(receiver) = receiver {
            let actual = self.register_runtime_type(caller, receiver.register)?;
            if actual != callee.receiver_type {
                return Err(vec![unsupported(
                    caller,
                    "synchronous tail receiver type mismatch",
                )]);
            }
            let ty = self.register_type(caller, receiver.register)?;
            let value = self.load_operand(caller, receiver)?;
            if receiver.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, receiver.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        for (operand, expected) in args.iter().zip(&callee.params) {
            let actual = self.register_runtime_type(caller, operand.register)?;
            if actual != *expected {
                return Err(vec![unsupported(
                    caller,
                    "synchronous tail-call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, operand.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let result_ty = self.llvm_return_type(callee.result)?;
        let returned = if result_ty == "void" {
            self.line(&format!(
                "  call void @g1_f{callee_index}({})",
                arguments.join(", ")
            ));
            None
        } else {
            let returned = self.temp();
            self.line(&format!(
                "  %{returned} = call {result_ty} @g1_f{callee_index}({})",
                arguments.join(", ")
            ));
            Some((result_ty, format!("%{returned}")))
        };
        if returned.is_none() && matches!(self.runtime_type(callee.result)?, Type::Unit) {
            let header = self.temp();
            let return_address = self.temp();
            let return_slot = self.temp();
            self.line(&format!(
                "  %{header} = getelementptr inbounds {}, ptr %frame, i32 0, i32 0",
                self.effect_frame_type(caller_index)
            ));
            self.line(&format!(
                "  %{return_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 3"
            ));
            self.line(&format!(
                "  %{return_slot} = load ptr, ptr %{return_address}"
            ));
            self.emit_effect_store_optional_unit_return(
                &format!("%{header}"),
                &format!("%{return_slot}"),
            );
        }
        self.emit_effect_finish_frame(caller_index, returned.as_ref())
    }

    fn emit_effect_finish_frame(
        &mut self,
        function_index: usize,
        returned: Option<&(String, String)>,
    ) -> Result<(), Vec<Diagnostic>> {
        let header = self.temp();
        self.line(&format!(
            "  %{header} = getelementptr inbounds {}, ptr %frame, i32 0, i32 0",
            self.effect_frame_type(function_index)
        ));
        if let Some((ty, value)) = returned {
            let return_address = self.temp();
            let return_slot = self.temp();
            self.line(&format!(
                "  %{return_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 3"
            ));
            self.line(&format!(
                "  %{return_slot} = load ptr, ptr %{return_address}"
            ));
            self.line(&format!("  store {ty} {value}, ptr %{return_slot}"));
            let init_address = self.temp();
            let init = self.temp();
            let has_init = self.temp();
            let mark_label = self.temp();
            let done_label = self.temp();
            self.line(&format!(
                "  %{init_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 7"
            ));
            self.line(&format!("  %{init} = load ptr, ptr %{init_address}"));
            self.line(&format!("  %{has_init} = icmp ne ptr %{init}, null"));
            self.line(&format!(
                "  br i1 %{has_init}, label %effect.finish.mark{mark_label}, label %effect.finish.marked{done_label}"
            ));
            self.line(&format!("effect.finish.mark{mark_label}:"));
            self.line(&format!("  store i8 1, ptr %{init}"));
            self.line(&format!("  br label %effect.finish.marked{done_label}"));
            self.line(&format!("effect.finish.marked{done_label}:"));
        }
        let previous_address = self.temp();
        let previous = self.temp();
        let root = self.temp();
        let caller_label = self.temp();
        let root_label = self.temp();
        self.line(&format!(
            "  %{previous_address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{previous} = load ptr, ptr %{previous_address}"
        ));
        self.line(&format!("  %{root} = icmp eq ptr %{previous}, null"));
        self.line(&format!(
            "  br i1 %{root}, label %effect.finish.root{root_label}, label %effect.finish.caller{caller_label}"
        ));
        self.line(&format!("effect.finish.caller{caller_label}:"));
        self.emit_effect_runtime_store(0, "ptr", &format!("%{previous}"));
        self.line(&format!(
            "  call void @g1_effect_drop_f{function_index}(ptr %frame)"
        ));
        self.line("  ret void");
        self.line(&format!("effect.finish.root{root_label}:"));
        self.emit_effect_runtime_store(1, "i32", "0");
        self.emit_effect_runtime_store(5, "ptr", "%frame");
        self.emit_effect_runtime_store(0, "ptr", "null");
        self.line("  ret void");
        Ok(())
    }

    fn emit_effect_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callee_index: usize,
        args: &[mir::Operand],
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let callee = self
            .phases
            .mir
            .functions
            .get(callee_index)
            .cloned()
            .ok_or_else(|| vec![unsupported(caller, "effect call target is missing")])?;
        if !self.function_needs_effect_frame(&callee) {
            return self.emit_effect_sync_call(caller, result, callee_index, &callee, args, normal);
        }
        if callee.receiver_mode.is_some() || callee.params.len() != args.len() {
            return Err(vec![unsupported(
                caller,
                "malformed direct outward-effect call",
            )]);
        }
        if result.is_none() && self.llvm_return_type(callee.result)? != "void" {
            return Err(vec![unsupported(
                caller,
                "discarded non-unit outward-effect result",
            )]);
        }
        let state_address = self.temp();
        self.line(&format!(
            "  %{state_address} = getelementptr inbounds %g1.effect_frame, ptr %frame, i32 0, i32 4"
        ));
        self.line(&format!(
            "  store i32 {}, ptr %{state_address}",
            normal.target
        ));
        self.emit_edge_arguments(caller, normal, result.into_iter().collect())?;
        let mut arguments = Vec::with_capacity(args.len());
        for (operand, expected) in args.iter().zip(&callee.params) {
            let actual = self.register_runtime_type(caller, operand.register)?;
            if actual != *expected {
                return Err(vec![unsupported(
                    caller,
                    "outward-effect call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, operand.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let return_slot = result.map_or_else(|| "null".to_owned(), |result| format!("%r{result}"));
        let child = self.temp();
        let suffix = if arguments.is_empty() {
            String::new()
        } else {
            format!(", {}", arguments.join(", "))
        };
        self.line(&format!(
            "  %{child} = call ptr @g1_effect_new_f{callee_index}(ptr %frame, ptr {return_slot}, ptr {}{suffix})",
            result.map_or_else(|| "null".to_owned(), |result| format!("%init{result}"))
        ));
        self.emit_effect_runtime_store(0, "ptr", &format!("%{child}"));
        self.line("  ret void");
        Ok(())
    }

    fn emit_effect_known_receiver_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callee_index: usize,
        receiver: &mir::Operand,
        args: &[mir::Operand],
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let callee = self
            .phases
            .mir
            .functions
            .get(callee_index)
            .cloned()
            .ok_or_else(|| {
                vec![unsupported(
                    caller,
                    "effect known-receiver call target is missing",
                )]
            })?;
        if callee.receiver_mode != Some(0)
            || receiver.mode != mir::UseMode::Copy
            || callee.params.len() != args.len()
        {
            return Err(vec![unsupported(
                caller,
                "malformed shared known-receiver call from an effect frame",
            )]);
        }
        let receiver_type = self.register_runtime_type(caller, receiver.register)?;
        if receiver_type != callee.receiver_type {
            return Err(vec![unsupported(
                caller,
                "known-receiver call receiver type mismatch",
            )]);
        }
        if let Some(result) = result {
            if self.register_runtime_type(caller, result)? != callee.result {
                return Err(vec![unsupported(
                    caller,
                    "known-receiver call result type mismatch",
                )]);
            }
        } else if self.llvm_return_type(callee.result)? != "void" {
            return Err(vec![unsupported(
                caller,
                "discarded non-unit known-receiver call result",
            )]);
        }

        let receiver_ty = self.register_type(caller, receiver.register)?;
        let receiver_value = self.load_operand(caller, receiver)?;
        if !self.function_needs_effect_frame(&callee) {
            return self.emit_effect_sync_known_receiver_call(
                caller,
                result,
                callee_index,
                &callee,
                &receiver_ty,
                &receiver_value,
                args,
                normal,
            );
        }

        let state_address = self.temp();
        self.line(&format!(
            "  %{state_address} = getelementptr inbounds %g1.effect_frame, ptr %frame, i32 0, i32 4"
        ));
        self.line(&format!(
            "  store i32 {}, ptr %{state_address}",
            normal.target
        ));
        self.emit_edge_arguments(caller, normal, result.into_iter().collect())?;

        let mut arguments = vec![format!("{receiver_ty} {receiver_value}")];
        for (operand, expected) in args.iter().zip(&callee.params) {
            let actual = self.register_runtime_type(caller, operand.register)?;
            if actual != *expected {
                return Err(vec![unsupported(
                    caller,
                    "outward known-receiver call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, operand.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let return_slot = result.map_or_else(|| "null".to_owned(), |result| format!("%r{result}"));
        let return_init =
            result.map_or_else(|| "null".to_owned(), |result| format!("%init{result}"));
        let child = self.temp();
        self.line(&format!(
            "  %{child} = call ptr @g1_effect_new_f{callee_index}(ptr %frame, ptr {return_slot}, ptr {return_init}, {})",
            arguments.join(", ")
        ));
        self.emit_effect_runtime_store(0, "ptr", &format!("%{child}"));
        self.line("  ret void");
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_effect_sync_known_receiver_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callee_index: usize,
        callee: &mir::Function,
        receiver_ty: &str,
        receiver_value: &str,
        args: &[mir::Operand],
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let mut arguments = vec![format!("{receiver_ty} {receiver_value}")];
        for (operand, expected) in args.iter().zip(&callee.params) {
            let actual = self.register_runtime_type(caller, operand.register)?;
            if actual != *expected {
                return Err(vec![unsupported(
                    caller,
                    "synchronous known-receiver call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, operand.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let result_ty = self.llvm_return_type(callee.result)?;
        if result_ty == "void" {
            self.line(&format!(
                "  call void @g1_f{callee_index}({})",
                arguments.join(", ")
            ));
            if let Some(result) = result {
                self.line(&format!("  store i8 0, ptr %r{result}"));
                self.emit_effect_set_initialized(caller, result, true)?;
            }
        } else {
            let returned = self.temp();
            self.line(&format!(
                "  %{returned} = call {result_ty} @g1_f{callee_index}({})",
                arguments.join(", ")
            ));
            if let Some(result) = result {
                self.line(&format!("  store {result_ty} %{returned}, ptr %r{result}"));
                self.emit_effect_set_initialized(caller, result, true)?;
            }
        }
        self.emit_effect_edge(caller, normal, result.into_iter().collect())
    }

    fn emit_effect_sync_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callee_index: usize,
        callee: &mir::Function,
        args: &[mir::Operand],
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        if callee.receiver_mode.is_some() || callee.params.len() != args.len() {
            return Err(vec![unsupported(
                caller,
                "malformed synchronous call from an effect frame",
            )]);
        }
        let result_ty = self.llvm_return_type(callee.result)?;
        if result.is_none() && result_ty != "void" {
            return Err(vec![unsupported(
                caller,
                "discarded non-unit synchronous call result",
            )]);
        }
        let mut arguments = Vec::with_capacity(args.len());
        for (operand, expected) in args.iter().zip(&callee.params) {
            let actual = self.register_runtime_type(caller, operand.register)?;
            if actual != *expected {
                return Err(vec![unsupported(
                    caller,
                    "synchronous call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(actual, &value, caller)?;
            } else {
                self.emit_effect_set_initialized(caller, operand.register, false)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        if result_ty == "void" {
            self.line(&format!(
                "  call void @g1_f{callee_index}({})",
                arguments.join(", ")
            ));
            if let Some(result) = result {
                self.line(&format!("  store i8 0, ptr %r{result}"));
                self.emit_effect_set_initialized(caller, result, true)?;
            }
        } else {
            let returned = self.temp();
            self.line(&format!(
                "  %{returned} = call {result_ty} @g1_f{callee_index}({})",
                arguments.join(", ")
            ));
            if let Some(result) = result {
                self.line(&format!("  store {result_ty} %{returned}, ptr %r{result}"));
                self.emit_effect_set_initialized(caller, result, true)?;
            }
        }
        self.emit_effect_edge(caller, normal, result.into_iter().collect())
    }

    fn emit_effect_instruction(
        &mut self,
        function: &mir::Function,
        instruction: &InstructionKind,
    ) -> Result<(), Vec<Diagnostic>> {
        if let InstructionKind::Drop { owner } = instruction {
            let owner_type = self.register_runtime_type(function, owner.register)?;
            if matches!(
                self.runtime_type(owner_type)?,
                Type::Tuple { .. } | Type::Struct { .. } | Type::BindingPack { .. }
            ) {
                return self.emit_effect_drop_aggregate_register(
                    function,
                    owner.register,
                    owner_type,
                );
            }
        }
        self.emit_instruction(function, instruction)?;
        let mut consumed = BTreeSet::new();
        instruction.for_each_register_use(|register, use_kind| {
            if use_kind == mir::RegisterUseKind::Consume {
                consumed.insert(register);
            }
        });
        for register in consumed {
            self.emit_effect_set_initialized(function, register, false)?;
        }
        if let Some(destination) = instruction.destination() {
            self.emit_effect_set_initialized(function, destination, true)?;
        }
        if let InstructionKind::ProjectMove { src, field, .. } = instruction {
            let source_type = self.register_runtime_type(function, src.register)?;
            if matches!(
                self.runtime_type(source_type)?,
                Type::Tuple { .. } | Type::Struct { .. } | Type::BindingPack { .. }
            ) {
                let runtime_field =
                    self.runtime_aggregate_owned_field_index(source_type, *field)?;
                self.line(&format!("  store i8 2, ptr %init{}", src.register));
                self.line(&format!(
                    "  store i8 0, ptr %fieldinit{}.{runtime_field}",
                    src.register
                ));
            }
        }
        Ok(())
    }

    fn emit_effect_drop_aggregate_register(
        &mut self,
        function: &mir::Function,
        register: u32,
        aggregate_type: TypeId,
    ) -> Result<(), Vec<Diagnostic>> {
        let full_label = self.temp();
        let partial_label = self.temp();
        let done_label = self.temp();
        let value = self.load_register(function, register)?;
        let state = self.temp();
        let full = self.temp();
        self.line(&format!("  %{state} = load i8, ptr %init{register}"));
        self.line(&format!("  %{full} = icmp eq i8 %{state}, 1"));
        self.line(&format!(
            "  br i1 %{full}, label %effect.drop.full{full_label}, label %effect.drop.partial{partial_label}"
        ));
        self.line(&format!("effect.drop.full{full_label}:"));
        self.emit_destroy(aggregate_type, &value, function)?;
        self.line(&format!("  br label %effect.drop.done{done_label}"));
        self.line(&format!("effect.drop.partial{partial_label}:"));
        let partial = self.temp();
        let fields_label = self.temp();
        self.line(&format!("  %{partial} = icmp eq i8 %{state}, 2"));
        self.line(&format!(
            "  br i1 %{partial}, label %effect.drop.fields{fields_label}, label %effect.drop.done{done_label}"
        ));
        self.line(&format!("effect.drop.fields{fields_label}:"));
        let fields = self.runtime_aggregate_field_layout(aggregate_type, 0)?;
        let aggregate_ty = self.llvm_type(aggregate_type)?;
        for field in fields.iter().rev() {
            let flag = self.temp();
            let present = self.temp();
            let drop_label = self.temp();
            let field_done = self.temp();
            self.line(&format!(
                "  %{flag} = load i8, ptr %fieldinit{register}.{}",
                field.owned_mask_index
            ));
            self.line(&format!("  %{present} = icmp ne i8 %{flag}, 0"));
            self.line(&format!(
                "  br i1 %{present}, label %effect.drop.field{drop_label}, label %effect.drop.field.done{field_done}"
            ));
            self.line(&format!("effect.drop.field{drop_label}:"));
            let extracted = self.temp();
            self.line(&format!(
                "  %{extracted} = extractvalue {aggregate_ty} {value}, {}",
                field.physical_index
            ));
            self.emit_destroy(field.runtime_type, &format!("%{extracted}"), function)?;
            self.line(&format!("  br label %effect.drop.field.done{field_done}"));
            self.line(&format!("effect.drop.field.done{field_done}:"));
        }
        self.line(&format!("  br label %effect.drop.done{done_label}"));
        self.line(&format!("effect.drop.done{done_label}:"));
        self.emit_effect_set_initialized(function, register, false)
    }

    fn emit_ordinary_drop_aggregate_register(
        &mut self,
        function: &mir::Function,
        register: u32,
        aggregate_type: TypeId,
    ) -> Result<(), Vec<Diagnostic>> {
        let fields = self.ordinary_aggregate_field_layout(function, register)?;
        let aggregate_ty = self.llvm_type(aggregate_type)?;
        let value = self.load_register(function, register)?;
        let mut all_present = "true".to_owned();
        for field in &fields {
            let flag = self.temp();
            let present = self.temp();
            self.line(&format!(
                "  %{flag} = load i8, ptr %fieldinit{register}.{}",
                field.owned_mask_index
            ));
            self.line(&format!("  %{present} = icmp ne i8 %{flag}, 0"));
            if all_present == "true" {
                all_present = format!("%{present}");
            } else {
                let combined = self.temp();
                self.line(&format!("  %{combined} = and i1 {all_present}, %{present}"));
                all_present = format!("%{combined}");
            }
        }
        let full_label = self.temp();
        let partial_label = self.temp();
        let done_label = self.temp();
        self.line(&format!(
            "  br i1 {all_present}, label %drop.aggregate.full{full_label}, label %drop.aggregate.partial{partial_label}"
        ));
        self.line(&format!("drop.aggregate.full{full_label}:"));
        self.emit_destroy(aggregate_type, &value, function)?;
        self.line(&format!("  br label %drop.aggregate.done{done_label}"));
        self.line(&format!("drop.aggregate.partial{partial_label}:"));
        for field in fields.iter().rev() {
            let flag = self.temp();
            let present = self.temp();
            let drop_label = self.temp();
            let field_done = self.temp();
            self.line(&format!(
                "  %{flag} = load i8, ptr %fieldinit{register}.{}",
                field.owned_mask_index
            ));
            self.line(&format!("  %{present} = icmp ne i8 %{flag}, 0"));
            self.line(&format!(
                "  br i1 %{present}, label %drop.aggregate.field{drop_label}, label %drop.aggregate.field.done{field_done}"
            ));
            self.line(&format!("drop.aggregate.field{drop_label}:"));
            let extracted = self.temp();
            self.line(&format!(
                "  %{extracted} = extractvalue {aggregate_ty} {value}, {}",
                field.physical_index
            ));
            self.emit_destroy(field.runtime_type, &format!("%{extracted}"), function)?;
            self.line(&format!(
                "  br label %drop.aggregate.field.done{field_done}"
            ));
            self.line(&format!("drop.aggregate.field.done{field_done}:"));
        }
        self.line(&format!("  br label %drop.aggregate.done{done_label}"));
        self.line(&format!("drop.aggregate.done{done_label}:"));
        self.emit_set_ordinary_aggregate_fields(function, register, false)
    }

    fn emit_retain_ordinary_aggregate_register(
        &mut self,
        function: &mir::Function,
        register: u32,
        value: &str,
    ) -> Result<(), Vec<Diagnostic>> {
        let aggregate_type = self.register_runtime_type(function, register)?;
        let aggregate_ty = self.llvm_type(aggregate_type)?;
        for field in self.ordinary_aggregate_field_layout(function, register)? {
            let flag = self.temp();
            let present = self.temp();
            let retain_label = self.temp();
            let done_label = self.temp();
            self.line(&format!(
                "  %{flag} = load i8, ptr %fieldinit{register}.{}",
                field.owned_mask_index
            ));
            self.line(&format!("  %{present} = icmp ne i8 %{flag}, 0"));
            self.line(&format!(
                "  br i1 %{present}, label %retain.aggregate.field{retain_label}, label %retain.aggregate.field.done{done_label}"
            ));
            self.line(&format!("retain.aggregate.field{retain_label}:"));
            let extracted = self.temp();
            self.line(&format!(
                "  %{extracted} = extractvalue {aggregate_ty} {value}, {}",
                field.physical_index
            ));
            self.emit_retain(field.runtime_type, &format!("%{extracted}"), function)?;
            self.line(&format!(
                "  br label %retain.aggregate.field.done{done_label}"
            ));
            self.line(&format!("retain.aggregate.field.done{done_label}:"));
        }
        Ok(())
    }

    fn emit_effect_set_initialized(
        &mut self,
        function: &mir::Function,
        register: u32,
        initialized: bool,
    ) -> Result<(), Vec<Diagnostic>> {
        self.line(&format!(
            "  store i8 {}, ptr %init{register}",
            u8::from(initialized)
        ));
        let count = match self.runtime_type(self.register_runtime_type(function, register)?)? {
            Type::Tuple { .. } | Type::Struct { .. } | Type::BindingPack { .. } => self
                .runtime_aggregate_field_layout(self.register_runtime_type(function, register)?, 0)?
                .len(),
            _ => 0,
        };
        for field in 0..count {
            self.line(&format!(
                "  store i8 {}, ptr %fieldinit{register}.{field}",
                u8::from(initialized)
            ));
        }
        Ok(())
    }

    fn emit_effect_edge(
        &mut self,
        function: &mir::Function,
        edge: &mir::Edge,
        preassigned: BTreeSet<u32>,
    ) -> Result<(), Vec<Diagnostic>> {
        self.emit_edge_arguments(function, edge, preassigned)?;
        self.line(&format!("  br label %bb{}", edge.target));
        Ok(())
    }

    fn emit_effect_runtime_store(&mut self, field: u32, ty: &str, value: &str) {
        let address = self.temp();
        self.line(&format!(
            "  %{address} = getelementptr inbounds %g1.effect_runtime, ptr %runtime, i32 0, i32 {field}"
        ));
        self.line(&format!("  store {ty} {value}, ptr %{address}"));
    }

    fn emit_effect_store_optional_unit_return(&mut self, header: &str, return_slot: &str) {
        let has_slot = self.temp();
        let store_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  %{has_slot} = icmp ne ptr {return_slot}, null"));
        self.line(&format!(
            "  br i1 %{has_slot}, label %effect.unit.store{store_label}, label %effect.unit.done{done_label}"
        ));
        self.line(&format!("effect.unit.store{store_label}:"));
        self.line(&format!("  store i8 0, ptr {return_slot}"));
        let init_address = self.temp();
        let init = self.temp();
        let has_init = self.temp();
        let mark_label = self.temp();
        self.line(&format!(
            "  %{init_address} = getelementptr inbounds %g1.effect_frame, ptr {header}, i32 0, i32 7"
        ));
        self.line(&format!("  %{init} = load ptr, ptr %{init_address}"));
        self.line(&format!("  %{has_init} = icmp ne ptr %{init}, null"));
        self.line(&format!(
            "  br i1 %{has_init}, label %effect.unit.mark{mark_label}, label %effect.unit.done{done_label}"
        ));
        self.line(&format!("effect.unit.mark{mark_label}:"));
        self.line(&format!("  store i8 1, ptr %{init}"));
        self.line(&format!("  br label %effect.unit.done{done_label}"));
        self.line(&format!("effect.unit.done{done_label}:"));
    }

    fn emit_edge_reference_relocations(
        &mut self,
        function: &mir::Function,
        edge: &mir::Edge,
        parameters: &[&mir::BlockParam],
    ) -> Result<Vec<(u32, u32, String)>, Vec<Diagnostic>> {
        if !edge.args.iter().try_fold(false, |found, operand| {
            Ok::<_, Vec<Diagnostic>>(
                found
                    || matches!(
                        self.runtime_type(self.register_runtime_type(function, operand.register)?)?,
                        Type::RefShared { .. } | Type::RefUnique { .. }
                    ),
            )
        })? {
            return Ok(Vec::new());
        }
        // PlaceFlow identifies the register where each loan is issued, but
        // optimized block parameters forward references under fresh register
        // identities without adding new LoanFacts. Consequently it cannot map
        // a parameter reference back to a simultaneously moved owner here.
        // Derive that final alias relation from the actual frame addresses;
        // validated loan discipline guarantees those references are either
        // into live function storage or valid external storage.
        edge.args
            .iter()
            .zip(parameters)
            .filter(|(operand, parameter)| {
                operand.mode == mir::UseMode::Move && operand.register != parameter.register
            })
            .map(|(operand, parameter)| {
                let ty = self.register_type(function, operand.register)?;
                let size = self.emit_array_element_size(&ty);
                Ok((operand.register, parameter.register, size))
            })
            .collect()
    }

    fn emit_relocated_edge_reference(
        &mut self,
        function: &mir::Function,
        source: u32,
        value: &str,
        relocations: &[(u32, u32, String)],
    ) -> Result<String, Vec<Diagnostic>> {
        if relocations.is_empty()
            || !matches!(
                self.runtime_type(self.register_runtime_type(function, source)?)?,
                Type::RefShared { .. } | Type::RefUnique { .. }
            )
        {
            return Ok(value.to_owned());
        }
        // Registers are addressable storage, so forwarding an owner and an
        // interior reference to distinct block-parameter registers cannot copy
        // the reference verbatim. Preserve its byte offset when it points into
        // an owner moved by this edge. Heap, caller, and other external
        // references match no source register and remain unchanged.
        let usize_ty = format!("i{}", self.pointer_width());
        let reference_integer = self.temp();
        self.line(&format!(
            "  %{reference_integer} = ptrtoint ptr {value} to {usize_ty}"
        ));
        let mut relocated = value.to_owned();
        for (owner_source, owner_target, owner_size) in relocations {
            let source_integer = self.temp();
            let source_end = self.temp();
            let after_start = self.temp();
            let before_end = self.temp();
            let inside = self.temp();
            let offset = self.temp();
            let rebased = self.temp();
            let selected = self.temp();
            self.line(&format!(
                "  %{source_integer} = ptrtoint ptr %r{owner_source} to {usize_ty}"
            ));
            self.line(&format!(
                "  %{source_end} = add {usize_ty} %{source_integer}, {owner_size}"
            ));
            self.line(&format!(
                "  %{after_start} = icmp uge {usize_ty} %{reference_integer}, %{source_integer}"
            ));
            self.line(&format!(
                "  %{before_end} = icmp ult {usize_ty} %{reference_integer}, %{source_end}"
            ));
            self.line(&format!(
                "  %{inside} = and i1 %{after_start}, %{before_end}"
            ));
            self.line(&format!(
                "  %{offset} = sub {usize_ty} %{reference_integer}, %{source_integer}"
            ));
            self.line(&format!(
                "  %{rebased} = getelementptr i8, ptr %r{owner_target}, {usize_ty} %{offset}"
            ));
            self.line(&format!(
                "  %{selected} = select i1 %{inside}, ptr %{rebased}, ptr {relocated}"
            ));
            relocated = format!("%{selected}");
        }
        Ok(relocated)
    }

    fn emit_edge_arguments(
        &mut self,
        function: &mir::Function,
        edge: &mir::Edge,
        preassigned: BTreeSet<u32>,
    ) -> Result<(), Vec<Diagnostic>> {
        let target = function
            .blocks
            .iter()
            .find(|block| block.id == edge.target)
            .ok_or_else(|| vec![unsupported(function, "edge to a missing block")])?;
        let parameters = target
            .params
            .iter()
            .filter(|parameter| !preassigned.contains(&parameter.register))
            .collect::<Vec<_>>();
        if parameters.len() != edge.args.len() {
            return Err(vec![unsupported(function, "malformed block argument edge")]);
        }
        let relocations = self.emit_edge_reference_relocations(function, edge, &parameters)?;
        let mut values = edge
            .args
            .iter()
            .map(|operand| {
                let ty = self.register_type(function, operand.register)?;
                let value = self.load_operand(function, operand)?;
                let fields = self.ordinary_aggregate_field_layout(function, operand.register)?;
                if operand.mode == mir::UseMode::Copy {
                    if fields.is_empty() {
                        let runtime_ty = self.register_runtime_type(function, operand.register)?;
                        self.emit_retain(runtime_ty, &value, function)?;
                    } else {
                        self.emit_retain_ordinary_aggregate_register(
                            function,
                            operand.register,
                            &value,
                        )?;
                    }
                }
                let state = if fields.is_empty() {
                    None
                } else {
                    let state = self.temp();
                    self.line(&format!(
                        "  %{state} = load i8, ptr %init{}",
                        operand.register
                    ));
                    Some(format!("%{state}"))
                };
                let field_flags = fields
                    .iter()
                    .map(|field| {
                        let flag = self.temp();
                        self.line(&format!(
                            "  %{flag} = load i8, ptr %fieldinit{}.{}",
                            operand.register, field.owned_mask_index
                        ));
                        format!("%{flag}")
                    })
                    .collect::<Vec<_>>();
                Ok((
                    ty,
                    value,
                    operand.register,
                    operand.mode,
                    state,
                    field_flags,
                ))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        for (_, value, source, _, _, _) in &mut values {
            *value = self.emit_relocated_edge_reference(function, *source, value, &relocations)?;
        }
        for (parameter, (ty, value, source, mode, state, field_flags)) in
            parameters.into_iter().zip(values)
        {
            self.line(&format!(
                "  store {ty} {value}, ptr %r{}",
                parameter.register
            ));
            let target_fields =
                self.ordinary_aggregate_field_layout(function, parameter.register)?;
            if target_fields.len() != field_flags.len() {
                return Err(vec![unsupported(
                    function,
                    "effect edge aggregate field-state layout mismatch",
                )]);
            }
            if field_flags.is_empty() {
                if mode == mir::UseMode::Move {
                    self.emit_effect_set_initialized(function, source, false)?;
                }
                self.emit_effect_set_initialized(function, parameter.register, true)?;
                continue;
            }
            if mode == mir::UseMode::Move {
                self.emit_effect_set_initialized(function, source, false)?;
            }
            for (field, flag) in target_fields.iter().zip(field_flags) {
                self.line(&format!(
                    "  store i8 {flag}, ptr %fieldinit{}.{}",
                    parameter.register, field.owned_mask_index
                ));
            }
            self.line(&format!(
                "  store i8 {}, ptr %init{}",
                state.expect("aggregate edge arguments have an initialization state"),
                parameter.register
            ));
        }
        Ok(())
    }

    fn emit_instruction(
        &mut self,
        function: &mir::Function,
        instruction: &InstructionKind,
    ) -> Result<(), Vec<Diagnostic>> {
        match instruction {
            InstructionKind::Const { dst, value } => {
                let ty = self.register_type(function, *dst)?;
                let value = self.llvm_constant(value)?;
                self.line(&format!("  store {ty} {value}, ptr %r{dst}"));
            }
            InstructionKind::Copy { dst, src } => {
                let value = self.load_operand(function, src)?;
                let ty = self.register_type(function, *dst)?;
                let runtime_ty = self.register_runtime_type(function, *dst)?;
                self.emit_retain(runtime_ty, &value, function)?;
                self.line(&format!("  store {ty} {value}, ptr %r{dst}"));
            }
            InstructionKind::Move { dst, src } => {
                let value = self.load_operand(function, src)?;
                let ty = self.register_type(function, *dst)?;
                self.line(&format!("  store {ty} {value}, ptr %r{dst}"));
            }
            InstructionKind::Borrow { dst, src, .. } => {
                self.line(&format!("  store ptr %r{src}, ptr %r{dst}"));
            }
            InstructionKind::ProjectBorrow {
                dst, src, field, ..
            } => {
                let source = self.register_runtime_type(function, *src)?;
                let (aggregate, base) = match self.runtime_type(source)? {
                    Type::RefShared { referent } | Type::RefUnique { referent } => {
                        (*referent, self.load_register(function, *src)?)
                    }
                    _ => (source, format!("%r{src}")),
                };
                let aggregate_ty = self.llvm_type(aggregate)?;
                let llvm_field = if matches!(self.runtime_type(aggregate)?, Type::Enum { .. }) {
                    self.enum_slot_words(aggregate, *field)?;
                    field + 1
                } else {
                    self.runtime_aggregate_physical_field_index(aggregate, *field)? as u32
                };
                let address = self.temp();
                self.line(&format!(
                    "  %{address} = getelementptr inbounds {aggregate_ty}, ptr {base}, i32 0, i32 {llvm_field}"
                ));
                self.line(&format!("  store ptr %{address}, ptr %r{dst}"));
            }
            InstructionKind::Reborrow { dst, src, .. } => {
                let reference = self.load_register(function, *src)?;
                self.line(&format!("  store ptr {reference}, ptr %r{dst}"));
            }
            InstructionKind::DerefCopy { dst, src }
            | InstructionKind::DerefReborrow { dst, src, .. }
            | InstructionKind::DerefMove { dst, src } => {
                let reference = self.load_register(function, *src)?;
                let ty = self.register_type(function, *dst)?;
                let value = self.temp();
                self.line(&format!("  %{value} = load {ty}, ptr {reference}"));
                if matches!(instruction, InstructionKind::DerefCopy { .. }) {
                    let runtime_ty = self.register_runtime_type(function, *dst)?;
                    self.emit_retain(runtime_ty, &format!("%{value}"), function)?;
                }
                self.line(&format!("  store {ty} %{value}, ptr %r{dst}"));
            }
            InstructionKind::DerefStore { dst, src } => {
                let reference = self.load_register(function, *dst)?;
                let ty = self.register_type(function, src.register)?;
                let value = self.load_operand(function, src)?;
                if src.mode == mir::UseMode::Copy {
                    let runtime_ty = self.register_runtime_type(function, src.register)?;
                    self.emit_retain(runtime_ty, &value, function)?;
                }
                self.line(&format!("  store {ty} {value}, ptr {reference}"));
            }
            InstructionKind::Construct {
                dst,
                ty,
                variant: None,
                fields,
            } => {
                let aggregate_ty = self.llvm_type(*ty)?;
                let runtime_fields = self.runtime_aggregate_fields(*ty)?;
                if runtime_fields.len() != fields.len() {
                    return Err(vec![backend_error(format!(
                        "aggregate t{ty} expects {} runtime fields, received {}",
                        runtime_fields.len(),
                        fields.len()
                    ))]);
                }
                let mut aggregate = "zeroinitializer".to_owned();
                for (index, field) in fields.iter().enumerate() {
                    let actual = self.register_runtime_type(function, field.register)?;
                    if actual != runtime_fields[index] {
                        return Err(vec![unsupported(function, "aggregate field type mismatch")]);
                    }
                    let field_ty = self.register_type(function, field.register)?;
                    let value = self.load_operand(function, field)?;
                    if field.mode == mir::UseMode::Copy {
                        let runtime_ty = self.register_runtime_type(function, field.register)?;
                        self.emit_retain(runtime_ty, &value, function)?;
                    }
                    let inserted = self.temp();
                    self.line(&format!(
                        "  %{inserted} = insertvalue {aggregate_ty} {aggregate}, {field_ty} {value}, {index}"
                    ));
                    aggregate = format!("%{inserted}");
                }
                self.line(&format!("  store {aggregate_ty} {aggregate}, ptr %r{dst}"));
            }
            InstructionKind::Construct {
                dst,
                ty,
                variant: Some(variant),
                fields,
            } => {
                let aggregate_ty = self.llvm_type(*ty)?;
                let variants = match self.runtime_type(*ty)? {
                    Type::Enum { variants, .. } => variants,
                    other => {
                        return Err(vec![backend_error(format!(
                            "tagged construction requires an enum, found {other:?}"
                        ))]);
                    }
                };
                let declaration = variants.get(*variant as usize).ok_or_else(|| {
                    vec![backend_error(format!(
                        "enum t{ty} has no variant {variant}"
                    ))]
                })?;
                if declaration.fields.len() != fields.len() {
                    return Err(vec![backend_error(format!(
                        "enum t{ty} variant {variant} expects {} fields, received {}",
                        declaration.fields.len(),
                        fields.len()
                    ))]);
                }
                let tagged = self.temp();
                self.line(&format!(
                    "  %{tagged} = insertvalue {aggregate_ty} poison, i32 {variant}, 0"
                ));
                let mut aggregate = format!("%{tagged}");
                for (index, field) in fields.iter().enumerate() {
                    let words = self.enum_slot_words(*ty, index as u32)?;
                    let slot_ty = format!("[{words} x i128]");
                    let slot = self.temp();
                    self.line(&format!("  %{slot} = alloca {slot_ty}"));
                    self.line(&format!(
                        "  store {slot_ty} zeroinitializer, ptr %{slot}, align 1"
                    ));
                    let field_ty = self.register_type(function, field.register)?;
                    let value = self.load_operand(function, field)?;
                    if field.mode == mir::UseMode::Copy {
                        let runtime_ty = self.register_runtime_type(function, field.register)?;
                        self.emit_retain(runtime_ty, &value, function)?;
                    }
                    self.line(&format!("  store {field_ty} {value}, ptr %{slot}, align 1"));
                    let packed = self.temp();
                    self.line(&format!(
                        "  %{packed} = load {slot_ty}, ptr %{slot}, align 1"
                    ));
                    let inserted = self.temp();
                    self.line(&format!(
                        "  %{inserted} = insertvalue {aggregate_ty} {aggregate}, {slot_ty} %{packed}, {}",
                        index + 1
                    ));
                    aggregate = format!("%{inserted}");
                }
                self.line(&format!("  store {aggregate_ty} {aggregate}, ptr %r{dst}"));
            }
            InstructionKind::ProjectCopy { dst, src, field }
            | InstructionKind::ProjectMove { dst, src, field } => {
                let source_id = self.register_runtime_type(function, src.register)?;
                let (aggregate_id, through_reference) = match self.runtime_type(source_id)? {
                    Type::RefShared { referent } | Type::RefUnique { referent } => {
                        (*referent, true)
                    }
                    _ => (source_id, false),
                };
                let aggregate_ty = self.llvm_type(aggregate_id)?;
                let aggregate = self.load_operand(function, src)?;
                let field_ty = self.register_type(function, *dst)?;
                let value = if matches!(self.runtime_type(aggregate_id)?, Type::Enum { .. }) {
                    let words = self.enum_slot_words(aggregate_id, *field)?;
                    let slot_ty = format!("[{words} x i128]");
                    let packed = if through_reference {
                        let address = self.temp();
                        self.line(&format!(
                            "  %{address} = getelementptr inbounds {aggregate_ty}, ptr {aggregate}, i32 0, i32 {}",
                            field + 1
                        ));
                        let packed = self.temp();
                        self.line(&format!("  %{packed} = load {slot_ty}, ptr %{address}"));
                        packed
                    } else {
                        let packed = self.temp();
                        self.line(&format!(
                            "  %{packed} = extractvalue {aggregate_ty} {aggregate}, {}",
                            field + 1
                        ));
                        packed
                    };
                    let slot = self.temp();
                    self.line(&format!("  %{slot} = alloca {slot_ty}"));
                    self.line(&format!(
                        "  store {slot_ty} %{packed}, ptr %{slot}, align 1"
                    ));
                    let value = self.temp();
                    self.line(&format!(
                        "  %{value} = load {field_ty}, ptr %{slot}, align 1"
                    ));
                    value
                } else {
                    let physical_field =
                        self.runtime_aggregate_physical_field_index(aggregate_id, *field)?;
                    if through_reference {
                        let address = self.temp();
                        self.line(&format!(
                            "  %{address} = getelementptr inbounds {aggregate_ty}, ptr {aggregate}, i32 0, i32 {physical_field}"
                        ));
                        let value = self.temp();
                        self.line(&format!("  %{value} = load {field_ty}, ptr %{address}"));
                        value
                    } else {
                        let value = self.temp();
                        self.line(&format!(
                            "  %{value} = extractvalue {aggregate_ty} {aggregate}, {physical_field}"
                        ));
                        value
                    }
                };
                if matches!(instruction, InstructionKind::ProjectCopy { .. }) {
                    let runtime_ty = self.register_runtime_type(function, *dst)?;
                    self.emit_retain(runtime_ty, &format!("%{value}"), function)?;
                }
                self.line(&format!("  store {field_ty} %{value}, ptr %r{dst}"));
            }
            InstructionKind::EnumTag { dst, src } => {
                let source_id = self.register_runtime_type(function, *src)?;
                let (aggregate_id, through_reference) = match self.runtime_type(source_id)? {
                    Type::RefShared { referent } | Type::RefUnique { referent } => {
                        (*referent, true)
                    }
                    _ => (source_id, false),
                };
                if !matches!(self.runtime_type(aggregate_id)?, Type::Enum { .. }) {
                    return Err(vec![unsupported(function, "tag read from a non-enum")]);
                }
                let aggregate_ty = self.llvm_type(aggregate_id)?;
                let aggregate = self.load_register(function, *src)?;
                let tag = if through_reference {
                    let address = self.temp();
                    self.line(&format!(
                        "  %{address} = getelementptr inbounds {aggregate_ty}, ptr {aggregate}, i32 0, i32 0"
                    ));
                    let tag = self.temp();
                    self.line(&format!("  %{tag} = load i32, ptr %{address}"));
                    tag
                } else {
                    let tag = self.temp();
                    self.line(&format!(
                        "  %{tag} = extractvalue {aggregate_ty} {aggregate}, 0"
                    ));
                    tag
                };
                let dst_ty = self.register_type(function, *dst)?;
                self.line(&format!("  store {dst_ty} %{tag}, ptr %r{dst}"));
            }
            InstructionKind::Primitive {
                dst,
                primitive,
                args,
            } => self.emit_primitive(function, *dst, *primitive, args)?,
            InstructionKind::MakeCallable {
                dst,
                callable_type,
                function: target,
                captures,
            } => {
                let callable =
                    self.emit_make_callable(function, *callable_type, *target as usize, captures)?;
                self.line(&format!("  store ptr {callable}, ptr %r{dst}"));
            }
            InstructionKind::MakeHandler {
                dst,
                handler_def,
                clauses,
            } => {
                let handler_type = self.register_runtime_type(function, *dst)?;
                let handler =
                    self.emit_make_handler(function, handler_type, *handler_def, clauses)?;
                self.line(&format!("  store ptr {handler}, ptr %r{dst}"));
            }
            InstructionKind::MakeHandlerShared {
                dst,
                handler_def,
                functions,
                captures,
            } => {
                let handler_type = self.register_runtime_type(function, *dst)?;
                let handler = self.emit_make_handler_shared(
                    function,
                    handler_type,
                    *handler_def,
                    functions,
                    captures,
                )?;
                self.line(&format!("  store ptr {handler}, ptr %r{dst}"));
            }
            InstructionKind::MakeBindingPack {
                dst,
                binding_type,
                payloads,
            } => {
                let Type::BindingPack { payload_type, .. } =
                    self.runtime_type(*binding_type)?.clone()
                else {
                    return Err(vec![unsupported(
                        function,
                        "MakeBindingPack with a non-binding runtime type",
                    )]);
                };
                let aggregate_ty = self.llvm_type(payload_type)?;
                let fields = self.runtime_aggregate_fields(payload_type)?;
                if fields.len() != payloads.len() {
                    return Err(vec![unsupported(
                        function,
                        "binding payload count mismatch",
                    )]);
                }
                let mut value = "zeroinitializer".to_owned();
                for (index, (field, payload)) in fields.iter().zip(payloads).enumerate() {
                    let actual = self.register_runtime_type(function, payload.register)?;
                    if actual != *field {
                        return Err(vec![unsupported(function, "binding payload type mismatch")]);
                    }
                    let field_ty = self.llvm_type(*field)?;
                    let field_value = self.load_operand(function, payload)?;
                    if payload.mode == mir::UseMode::Copy {
                        self.emit_retain(*field, &field_value, function)?;
                    }
                    let inserted = self.temp();
                    self.line(&format!(
                        "  %{inserted} = insertvalue {aggregate_ty} {value}, {field_ty} {field_value}, {index}"
                    ));
                    value = format!("%{inserted}");
                }
                self.line(&format!("  store {aggregate_ty} {value}, ptr %r{dst}"));
            }
            InstructionKind::Drop { owner } => {
                let ty = self.register_runtime_type(function, owner.register)?;
                let value = self.load_operand(function, owner)?;
                self.emit_destroy(ty, &value, function)?;
            }
            InstructionKind::EndBorrow { .. }
            | InstructionKind::Deconstruct { .. }
            | InstructionKind::LabelPush { .. }
            | InstructionKind::LabelPop { .. } => {}
        }
        Ok(())
    }

    fn emit_primitive(
        &mut self,
        function: &mir::Function,
        dst: u32,
        primitive: Primitive,
        args: &[mir::Operand],
    ) -> Result<(), Vec<Diagnostic>> {
        let dst_ty = self.register_type(function, dst)?;
        let loaded = args
            .iter()
            .map(|operand| {
                Ok((
                    self.register_type(function, operand.register)?,
                    self.load_operand(function, operand)?,
                ))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        for (operand, (_, value)) in args.iter().zip(&loaded) {
            if operand.mode == mir::UseMode::Copy {
                let ty = self.register_runtime_type(function, operand.register)?;
                self.emit_retain(ty, value, function)?;
            }
        }
        let result = match primitive {
            Primitive::IntCheckedAdd | Primitive::IntCheckedSub | Primitive::IntCheckedMul => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed checked arithmetic")]);
                };
                let width = integer_width(ty)
                    .ok_or_else(|| vec![unsupported(function, "non-integer checked arithmetic")])?;
                let signed = self.register_is_signed(function, args[0].register)?;
                let operation = match (primitive, signed) {
                    (Primitive::IntCheckedAdd, true) => "sadd",
                    (Primitive::IntCheckedAdd, false) => "uadd",
                    (Primitive::IntCheckedSub, true) => "ssub",
                    (Primitive::IntCheckedSub, false) => "usub",
                    (Primitive::IntCheckedMul, true) => "smul",
                    (Primitive::IntCheckedMul, false) => "umul",
                    _ => unreachable!(),
                };
                self.overflow_widths.insert((width, operation));
                let pair = self.temp();
                let value = self.temp();
                let overflow = self.temp();
                let trap = self.temp();
                let continuation = self.temp();
                self.line(&format!(
                    "  %{pair} = call {{ {ty}, i1 }} @llvm.{operation}.with.overflow.i{width}({ty} {left}, {ty} {right})"
                ));
                self.line(&format!(
                    "  %{value} = extractvalue {{ {ty}, i1 }} %{pair}, 0"
                ));
                self.line(&format!(
                    "  %{overflow} = extractvalue {{ {ty}, i1 }} %{pair}, 1"
                ));
                self.line(&format!(
                    "  br i1 %{overflow}, label %trap{trap}, label %cont{continuation}"
                ));
                self.line(&format!("trap{trap}:"));
                self.emit_runtime_fault(RUNTIME_FAULT_ARITHMETIC_OVERFLOW, "0", "0", "null", "0");
                self.line(&format!("cont{continuation}:"));
                format!("%{value}")
            }
            Primitive::IntCheckedDiv | Primitive::IntCheckedRem => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(
                        function,
                        "malformed checked division or remainder",
                    )]);
                };
                let width = integer_width(ty).ok_or_else(|| {
                    vec![unsupported(
                        function,
                        "non-integer checked division or remainder",
                    )]
                })?;
                let zero = self.temp();
                self.line(&format!("  %{zero} = icmp eq {ty} {right}, 0"));
                self.emit_runtime_fault_if(zero, RUNTIME_FAULT_DIVISION_BY_ZERO);
                if self.register_is_signed(function, args[0].register)? {
                    let minimum = signed_minimum(width);
                    let minimum_operand = self.temp();
                    let negative_one = self.temp();
                    let overflow = self.temp();
                    self.line(&format!(
                        "  %{minimum_operand} = icmp eq {ty} {left}, {minimum}"
                    ));
                    self.line(&format!("  %{negative_one} = icmp eq {ty} {right}, -1"));
                    self.line(&format!(
                        "  %{overflow} = and i1 %{minimum_operand}, %{negative_one}"
                    ));
                    self.emit_runtime_fault_if(overflow, RUNTIME_FAULT_ARITHMETIC_OVERFLOW);
                }
                let temporary = self.temp();
                let operation = match (
                    primitive,
                    self.register_is_signed(function, args[0].register)?,
                ) {
                    (Primitive::IntCheckedDiv, true) => "sdiv",
                    (Primitive::IntCheckedDiv, false) => "udiv",
                    (Primitive::IntCheckedRem, true) => "srem",
                    (Primitive::IntCheckedRem, false) => "urem",
                    _ => unreachable!(),
                };
                self.line(&format!(
                    "  %{temporary} = {operation} {ty} {left}, {right}"
                ));
                format!("%{temporary}")
            }
            Primitive::IntWrappingAdd
            | Primitive::IntWrappingSub
            | Primitive::IntWrappingMul
            | Primitive::IntBitAnd
            | Primitive::IntBitOr
            | Primitive::IntBitXor
            | Primitive::IntShl
            | Primitive::IntShr => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed integer primitive")]);
                };
                let operation = match primitive {
                    Primitive::IntWrappingAdd => "add",
                    Primitive::IntWrappingSub => "sub",
                    Primitive::IntWrappingMul => "mul",
                    Primitive::IntBitAnd => "and",
                    Primitive::IntBitOr => "or",
                    Primitive::IntBitXor => "xor",
                    Primitive::IntShl => "shl",
                    Primitive::IntShr if self.register_is_signed(function, args[0].register)? => {
                        "ashr"
                    }
                    Primitive::IntShr => "lshr",
                    _ => unreachable!(),
                };
                let shift = matches!(primitive, Primitive::IntShl | Primitive::IntShr);
                if shift {
                    let width = integer_width(ty)
                        .ok_or_else(|| vec![unsupported(function, "non-integer shift operand")])?;
                    let count_ty = &loaded[1].0;
                    let invalid = self.temp();
                    self.line(&format!(
                        "  %{invalid} = icmp uge {count_ty} {right}, {width}"
                    ));
                    self.emit_runtime_fault_if(invalid, RUNTIME_FAULT_INVALID_SHIFT_COUNT);
                }
                let right = if shift && loaded[1].0 != ty {
                    let widened = self.temp();
                    self.line(&format!(
                        "  %{widened} = zext {} {right} to {ty}",
                        loaded[1].0
                    ));
                    format!("%{widened}")
                } else {
                    right.to_owned()
                };
                let temporary = self.temp();
                self.line(&format!(
                    "  %{temporary} = {operation} {ty} {left}, {right}"
                ));
                format!("%{temporary}")
            }
            Primitive::IntBitNot | Primitive::IntCheckedNeg | Primitive::IntWrappingNeg => {
                let Some((ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed unary integer primitive",
                    )]);
                };
                let signed = self.register_is_signed(function, args[0].register)?;
                if primitive == Primitive::IntCheckedNeg {
                    let invalid = self.temp();
                    if signed {
                        let width = integer_width(ty).ok_or_else(|| {
                            vec![unsupported(function, "non-integer checked negation")]
                        })?;
                        self.line(&format!(
                            "  %{invalid} = icmp eq {ty} {value}, {}",
                            signed_minimum(width)
                        ));
                    } else {
                        self.line(&format!("  %{invalid} = icmp ne {ty} {value}, 0"));
                    }
                    self.emit_runtime_fault_if(invalid, RUNTIME_FAULT_ARITHMETIC_OVERFLOW);
                }
                let temporary = self.temp();
                let operation = if primitive == Primitive::IntBitNot {
                    "xor"
                } else {
                    "sub"
                };
                let identity = if primitive == Primitive::IntBitNot {
                    "-1"
                } else {
                    "0"
                };
                self.line(&format!(
                    "  %{temporary} = {operation} {ty} {identity}, {value}"
                ));
                format!("%{temporary}")
            }
            Primitive::IntEq
            | Primitive::IntNe
            | Primitive::IntLt
            | Primitive::IntLe
            | Primitive::IntGt
            | Primitive::IntGe => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed integer comparison")]);
                };
                let signed = self.register_is_signed(function, args[0].register)?;
                let predicate = match (primitive, signed) {
                    (Primitive::IntEq, _) => "eq",
                    (Primitive::IntNe, _) => "ne",
                    (Primitive::IntLt, true) => "slt",
                    (Primitive::IntLt, false) => "ult",
                    (Primitive::IntLe, true) => "sle",
                    (Primitive::IntLe, false) => "ule",
                    (Primitive::IntGt, true) => "sgt",
                    (Primitive::IntGt, false) => "ugt",
                    (Primitive::IntGe, true) => "sge",
                    (Primitive::IntGe, false) => "uge",
                    _ => unreachable!(),
                };
                let flag = self.temp();
                let extended = self.temp();
                self.line(&format!(
                    "  %{flag} = icmp {predicate} {ty} {left}, {right}"
                ));
                self.line(&format!("  %{extended} = zext i1 %{flag} to {dst_ty}"));
                format!("%{extended}")
            }
            Primitive::IntConvertChecked | Primitive::IntConvertWrapping => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed integer conversion")]);
                };
                let source_id = self.register_runtime_type(function, args[0].register)?;
                let target_id = self.register_runtime_type(function, dst)?;
                let (source_signed, source_width) = self
                    .integer_type_info(source_id)
                    .ok_or_else(|| vec![unsupported(function, "non-integer conversion source")])?;
                let (target_signed, target_width) = self
                    .integer_type_info(target_id)
                    .ok_or_else(|| vec![unsupported(function, "non-integer conversion target")])?;
                if primitive == Primitive::IntConvertChecked {
                    let mut invalid = None;
                    let mut add_guard = |this: &mut Self, guard: Temporary| {
                        invalid = Some(if let Some(previous) = invalid {
                            let combined = this.temp();
                            this.line(&format!("  %{combined} = or i1 %{previous}, %{guard}"));
                            combined
                        } else {
                            guard
                        });
                    };
                    match (source_signed, target_signed) {
                        (true, true) if target_width < source_width => {
                            let below = self.temp();
                            let above = self.temp();
                            self.line(&format!(
                                "  %{below} = icmp slt {source_ty} {value}, {}",
                                signed_minimum(target_width)
                            ));
                            self.line(&format!(
                                "  %{above} = icmp sgt {source_ty} {value}, {}",
                                signed_maximum(target_width)
                            ));
                            add_guard(self, below);
                            add_guard(self, above);
                        }
                        (false, false) if target_width < source_width => {
                            let above = self.temp();
                            self.line(&format!(
                                "  %{above} = icmp ugt {source_ty} {value}, {}",
                                unsigned_maximum(target_width)
                            ));
                            add_guard(self, above);
                        }
                        (true, false) => {
                            let negative = self.temp();
                            self.line(&format!("  %{negative} = icmp slt {source_ty} {value}, 0"));
                            add_guard(self, negative);
                            if target_width < source_width {
                                let above = self.temp();
                                self.line(&format!(
                                    "  %{above} = icmp ugt {source_ty} {value}, {}",
                                    unsigned_maximum(target_width)
                                ));
                                add_guard(self, above);
                            }
                        }
                        (false, true) if target_width <= source_width => {
                            let above = self.temp();
                            self.line(&format!(
                                "  %{above} = icmp ugt {source_ty} {value}, {}",
                                signed_maximum(target_width)
                            ));
                            add_guard(self, above);
                        }
                        _ => {}
                    }
                    if let Some(invalid) = invalid {
                        self.emit_runtime_fault_if(invalid, RUNTIME_FAULT_ARITHMETIC_OVERFLOW);
                    }
                }
                if source_width == target_width {
                    value.clone()
                } else {
                    let temporary = self.temp();
                    let operation = if target_width < source_width {
                        "trunc"
                    } else if source_signed {
                        "sext"
                    } else {
                        "zext"
                    };
                    self.line(&format!(
                        "  %{temporary} = {operation} {source_ty} {value} to {dst_ty}"
                    ));
                    format!("%{temporary}")
                }
            }
            Primitive::FloatAdd
            | Primitive::FloatSub
            | Primitive::FloatMul
            | Primitive::FloatDiv
            | Primitive::FloatRem => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed float arithmetic")]);
                };
                let operation = match primitive {
                    Primitive::FloatAdd => "fadd",
                    Primitive::FloatSub => "fsub",
                    Primitive::FloatMul => "fmul",
                    Primitive::FloatDiv => "fdiv",
                    Primitive::FloatRem => "frem",
                    _ => unreachable!(),
                };
                let temporary = self.temp();
                self.line(&format!(
                    "  %{temporary} = {operation} {ty} {left}, {right}"
                ));
                format!("%{temporary}")
            }
            Primitive::FloatNeg => {
                let Some((ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed float negation")]);
                };
                let temporary = self.temp();
                self.line(&format!("  %{temporary} = fneg {ty} {value}"));
                format!("%{temporary}")
            }
            Primitive::FloatEq
            | Primitive::FloatNe
            | Primitive::FloatLt
            | Primitive::FloatLe
            | Primitive::FloatGt
            | Primitive::FloatGe => {
                let Some((ty, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed float comparison")]);
                };
                let predicate = match primitive {
                    Primitive::FloatEq => "oeq",
                    Primitive::FloatNe => "une",
                    Primitive::FloatLt => "olt",
                    Primitive::FloatLe => "ole",
                    Primitive::FloatGt => "ogt",
                    Primitive::FloatGe => "oge",
                    _ => unreachable!(),
                };
                let flag = self.temp();
                let extended = self.temp();
                self.line(&format!(
                    "  %{flag} = fcmp {predicate} {ty} {left}, {right}"
                ));
                self.line(&format!("  %{extended} = zext i1 %{flag} to {dst_ty}"));
                format!("%{extended}")
            }
            Primitive::FloatToBits | Primitive::FloatFromBits => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed float bit conversion",
                    )]);
                };
                let temporary = self.temp();
                self.line(&format!(
                    "  %{temporary} = bitcast {source_ty} {value} to {dst_ty}"
                ));
                format!("%{temporary}")
            }
            Primitive::FloatConvert => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed float conversion")]);
                };
                if source_ty == &dst_ty {
                    value.clone()
                } else {
                    let temporary = self.temp();
                    let operation = if source_ty == "float" {
                        "fpext"
                    } else {
                        "fptrunc"
                    };
                    self.line(&format!(
                        "  %{temporary} = {operation} {source_ty} {value} to {dst_ty}"
                    ));
                    format!("%{temporary}")
                }
            }
            Primitive::IntToFloat => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed integer-to-float conversion",
                    )]);
                };
                let source_id = self.register_runtime_type(function, args[0].register)?;
                let (signed, _) = self.integer_type_info(source_id).ok_or_else(|| {
                    vec![unsupported(function, "non-integer integer-to-float source")]
                })?;
                let temporary = self.temp();
                let operation = if signed { "sitofp" } else { "uitofp" };
                self.line(&format!(
                    "  %{temporary} = {operation} {source_ty} {value} to {dst_ty}"
                ));
                format!("%{temporary}")
            }
            Primitive::FloatToIntChecked => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed checked float-to-integer conversion",
                    )]);
                };
                let target_id = self.register_runtime_type(function, dst)?;
                let (signed, width) = self.integer_type_info(target_id).ok_or_else(|| {
                    vec![unsupported(
                        function,
                        "non-integer checked float conversion target",
                    )]
                })?;
                let lower = if signed {
                    llvm_float_power(source_ty, i32::from(width) - 1, true)?
                } else {
                    if source_ty == "float" {
                        "0.000000e+00".to_owned()
                    } else {
                        "0.000000e+00".to_owned()
                    }
                };
                let upper =
                    llvm_float_power(source_ty, i32::from(width - u16::from(signed)), false)?;
                let unordered = self.temp();
                let below = self.temp();
                let above = self.temp();
                let invalid_range = self.temp();
                let invalid = self.temp();
                self.line(&format!(
                    "  %{unordered} = fcmp uno {source_ty} {value}, {value}"
                ));
                self.line(&format!(
                    "  %{below} = fcmp olt {source_ty} {value}, {lower}"
                ));
                self.line(&format!(
                    "  %{above} = fcmp oge {source_ty} {value}, {upper}"
                ));
                self.line(&format!("  %{invalid_range} = or i1 %{below}, %{above}"));
                self.line(&format!(
                    "  %{invalid} = or i1 %{unordered}, %{invalid_range}"
                ));
                self.emit_runtime_fault_if(invalid, RUNTIME_FAULT_ARITHMETIC_OVERFLOW);
                let temporary = self.temp();
                let operation = if signed { "fptosi" } else { "fptoui" };
                self.line(&format!(
                    "  %{temporary} = {operation} {source_ty} {value} to {dst_ty}"
                ));
                format!("%{temporary}")
            }
            Primitive::BytesFromArrayMove => {
                let Some((_, array)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed Array-to-Bytes conversion",
                    )]);
                };
                let array_ty = self.register_runtime_type(function, args[0].register)?;
                let element = self.array_element(array_ty)?;
                if !matches!(self.runtime_type(element)?, Type::U8) {
                    return Err(vec![unsupported(
                        function,
                        "Array-to-Bytes conversion with non-u8 elements",
                    )]);
                }
                let usize_ty = format!("i{}", self.pointer_width());
                let length_address = self.temp();
                let length = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.emit_array_dense_check(array, &format!("%{length}"), &usize_ty);
                let bytes = self.temp();
                let bytes_data = self.temp();
                let array_data_address = self.temp();
                let array_data = self.temp();
                self.line(&format!(
                    "  %{bytes} = call ptr @g1_bytes_allocate({usize_ty} %{length})"
                ));
                self.line(&format!(
                    "  %{bytes_data} = call ptr @g1_bytes_data(ptr %{bytes})"
                ));
                self.line(&format!(
                    "  %{array_data_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 3"
                ));
                self.line(&format!(
                    "  %{array_data} = load ptr, ptr %{array_data_address}"
                ));
                self.line(&format!(
                    "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{bytes_data}, ptr %{array_data}, {usize_ty} %{length}, i1 false)"
                ));
                self.line(&format!("  call void @g1_array_free(ptr {array})"));
                format!("%{bytes}")
            }
            Primitive::BytesToArray => {
                let Some((_, bytes)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed Bytes-to-Array conversion",
                    )]);
                };
                let array_ty = self.register_runtime_type(function, dst)?;
                let element = self.array_element(array_ty)?;
                if !matches!(self.runtime_type(element)?, Type::U8) {
                    return Err(vec![unsupported(
                        function,
                        "Bytes-to-Array conversion with non-u8 elements",
                    )]);
                }
                let usize_ty = format!("i{}", self.pointer_width());
                let length_address = self.temp();
                let length = self.temp();
                let array = self.temp();
                let array_length_address = self.temp();
                let bytes_data = self.temp();
                let array_data_address = self.temp();
                let array_data = self.temp();
                let initialized_address = self.temp();
                let initialized = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.bytes, ptr {bytes}, i32 0, i32 1"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{array} = call ptr @g1_array_allocate({usize_ty} %{length}, {usize_ty} 1)"
                ));
                self.line(&format!(
                    "  %{array_length_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  store {usize_ty} %{length}, ptr %{array_length_address}"
                ));
                self.line(&format!(
                    "  %{bytes_data} = call ptr @g1_bytes_data(ptr {bytes})"
                ));
                self.line(&format!(
                    "  %{array_data_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 3"
                ));
                self.line(&format!(
                    "  %{array_data} = load ptr, ptr %{array_data_address}"
                ));
                self.line(&format!(
                    "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{array_data}, ptr %{bytes_data}, {usize_ty} %{length}, i1 false)"
                ));
                self.line(&format!(
                    "  %{initialized_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 4"
                ));
                self.line(&format!(
                    "  %{initialized} = load ptr, ptr %{initialized_address}"
                ));
                self.line(&format!(
                    "  call void @llvm.memset.p0.{usize_ty}(ptr %{initialized}, i8 1, {usize_ty} %{length}, i1 false)"
                ));
                self.line(&format!("  call void @g1_bytes_release(ptr {bytes})"));
                format!("%{array}")
            }
            Primitive::ArrayEmpty => {
                let array_ty = self.register_runtime_type(function, dst)?;
                let element = self.array_element(array_ty)?;
                self.ensure_plain_array_element(element, function)?;
                let element_ty = self.llvm_type(element)?;
                let element_size = self.emit_array_element_size(&element_ty);
                let usize_ty = format!("i{}", self.pointer_width());
                let array = self.temp();
                self.line(&format!(
                    "  %{array} = call ptr @g1_array_allocate({usize_ty} 0, {usize_ty} {element_size})"
                ));
                format!("%{array}")
            }
            Primitive::ArrayNew => {
                let Some((length_ty, length)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array allocation")]);
                };
                let Some((fill_ty, fill)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array allocation")]);
                };
                let array_ty = self.register_runtime_type(function, dst)?;
                let element = self.array_element(array_ty)?;
                self.ensure_plain_array_element(element, function)?;
                let expected = self.llvm_type(element)?;
                if &expected != fill_ty {
                    return Err(vec![unsupported(
                        function,
                        "Array fill value has the wrong LLVM type",
                    )]);
                }
                let element_size = self.emit_array_element_size(fill_ty);
                let array = self.temp();
                self.line(&format!(
                    "  %{array} = call ptr @g1_array_allocate({length_ty} {length}, {length_ty} {element_size})"
                ));
                let length_address = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  store {length_ty} {length}, ptr %{length_address}"
                ));
                let empty = self.temp();
                let loop_id = self.temp();
                let index_address = self.temp();
                self.line(&format!("  %{empty} = icmp eq {length_ty} {length}, 0"));
                self.line(&format!("  %{index_address} = alloca {length_ty}"));
                self.line(&format!("  store {length_ty} 0, ptr %{index_address}"));
                self.line(&format!(
                    "  br i1 %{empty}, label %array.fill.done{loop_id}, label %array.fill{loop_id}"
                ));
                self.line(&format!("array.fill{loop_id}:"));
                let index = self.temp();
                self.line(&format!(
                    "  %{index} = load {length_ty}, ptr %{index_address}"
                ));
                let data_address = self.temp();
                let data = self.temp();
                let slot = self.temp();
                let initialized_address = self.temp();
                let initialized = self.temp();
                let initialized_slot = self.temp();
                self.line(&format!(
                    "  %{data_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 3"
                ));
                self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
                self.line(&format!(
                    "  %{slot} = getelementptr inbounds {fill_ty}, ptr %{data}, {length_ty} %{index}"
                ));
                self.emit_retain(element, fill, function)?;
                self.line(&format!("  store {fill_ty} {fill}, ptr %{slot}"));
                self.line(&format!(
                    "  %{initialized_address} = getelementptr inbounds %g1.array, ptr %{array}, i32 0, i32 4"
                ));
                self.line(&format!(
                    "  %{initialized} = load ptr, ptr %{initialized_address}"
                ));
                self.line(&format!(
                    "  %{initialized_slot} = getelementptr inbounds i8, ptr %{initialized}, {length_ty} %{index}"
                ));
                self.line(&format!("  store i8 1, ptr %{initialized_slot}"));
                let next = self.temp();
                let more = self.temp();
                self.line(&format!("  %{next} = add {length_ty} %{index}, 1"));
                self.line(&format!(
                    "  store {length_ty} %{next}, ptr %{index_address}"
                ));
                self.line(&format!(
                    "  %{more} = icmp ult {length_ty} %{next}, {length}"
                ));
                self.line(&format!(
                    "  br i1 %{more}, label %array.fill{loop_id}, label %array.fill.done{loop_id}"
                ));
                self.line(&format!("array.fill.done{loop_id}:"));
                self.emit_destroy(element, fill, function)?;
                format!("%{array}")
            }
            Primitive::ArrayLen | Primitive::ArrayCapacity => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed Array metadata access",
                    )]);
                };
                self.referenced_array_element(function, args[0].register)?;
                let array = self.emit_array_from_reference(reference);
                let address = self.temp();
                let value = self.temp();
                let field = if primitive == Primitive::ArrayLen {
                    0
                } else {
                    1
                };
                self.line(&format!(
                    "  %{address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 {field}"
                ));
                self.line(&format!("  %{value} = load {dst_ty}, ptr %{address}"));
                format!("%{value}")
            }
            Primitive::ArrayGetCopy | Primitive::ArrayGetMove => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array access")]);
                };
                let Some((index_ty, index)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array access")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                if element_ty != dst_ty {
                    return Err(vec![unsupported(function, "Array element type mismatch")]);
                }
                let array = self.emit_array_from_reference(reference);
                let (slot, initialized) =
                    self.emit_checked_array_slot(&array, index_ty, index, &element_ty, true);
                let value = self.temp();
                self.line(&format!("  %{value} = load {element_ty}, ptr {slot}"));
                if primitive == Primitive::ArrayGetCopy {
                    self.emit_retain(element, &format!("%{value}"), function)?;
                } else {
                    self.line(&format!("  store i8 0, ptr {initialized}"));
                }
                format!("%{value}")
            }
            Primitive::ArrayGetBorrowShared | Primitive::ArrayGetBorrowUnique => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array borrow")]);
                };
                let Some((index_ty, index)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array borrow")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                let array = self.emit_array_from_reference(reference);
                let (slot, _) =
                    self.emit_checked_array_slot(&array, index_ty, index, &element_ty, true);
                slot
            }
            Primitive::ArraySetMove => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array store")]);
                };
                let Some((index_ty, index)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array store")]);
                };
                let Some((value_ty, value)) = loaded.get(2) else {
                    return Err(vec![unsupported(function, "malformed Array store")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                if &element_ty != value_ty {
                    return Err(vec![unsupported(
                        function,
                        "Array stored value type mismatch",
                    )]);
                }
                let array = self.emit_array_from_reference(reference);
                let (slot, initialized) =
                    self.emit_checked_array_slot(&array, index_ty, index, &element_ty, false);
                self.line(&format!("  store {element_ty} {value}, ptr {slot}"));
                self.line(&format!("  store i8 1, ptr {initialized}"));
                "0".to_owned()
            }
            Primitive::ArrayPushMove => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array push")]);
                };
                let Some((value_ty, value)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array push")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                if &element_ty != value_ty {
                    return Err(vec![unsupported(
                        function,
                        "Array pushed value type mismatch",
                    )]);
                }
                let usize_ty = format!("i{}", self.pointer_width());
                self.overflow_widths.insert((self.pointer_width(), "uadd"));
                let array = self.emit_array_from_reference(reference);
                let length_address = self.temp();
                let length = self.temp();
                let pair = self.temp();
                let required = self.temp();
                let overflow = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{pair} = call {{ {usize_ty}, i1 }} @llvm.uadd.with.overflow.{usize_ty}({usize_ty} %{length}, {usize_ty} 1)"
                ));
                self.line(&format!(
                    "  %{required} = extractvalue {{ {usize_ty}, i1 }} %{pair}, 0"
                ));
                self.line(&format!(
                    "  %{overflow} = extractvalue {{ {usize_ty}, i1 }} %{pair}, 1"
                ));
                self.emit_runtime_fault_if(overflow, RUNTIME_FAULT_ALLOCATION_OVERFLOW);
                self.line(&format!(
                    "  call void @g1_array_grow(ptr {array}, {usize_ty} %{required})"
                ));
                let data_address = self.temp();
                let data = self.temp();
                let slot = self.temp();
                let initialized_address = self.temp();
                let initialized = self.temp();
                let initialized_slot = self.temp();
                self.line(&format!(
                    "  %{data_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 3"
                ));
                self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
                self.line(&format!(
                    "  %{slot} = getelementptr inbounds {element_ty}, ptr %{data}, {usize_ty} %{length}"
                ));
                self.line(&format!("  store {element_ty} {value}, ptr %{slot}"));
                self.line(&format!(
                    "  %{initialized_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
                ));
                self.line(&format!(
                    "  %{initialized} = load ptr, ptr %{initialized_address}"
                ));
                self.line(&format!(
                    "  %{initialized_slot} = getelementptr inbounds i8, ptr %{initialized}, {usize_ty} %{length}"
                ));
                self.line(&format!("  store i8 1, ptr %{initialized_slot}"));
                self.line(&format!(
                    "  store {usize_ty} %{required}, ptr %{length_address}"
                ));
                "0".to_owned()
            }
            Primitive::ArrayPopMove => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array pop")]);
                };
                let element = self.referenced_array_element(function, args[0].register)?;
                let element_ty = self.llvm_type(element)?;
                if element_ty != dst_ty {
                    return Err(vec![unsupported(
                        function,
                        "Array popped value type mismatch",
                    )]);
                }
                let usize_ty = format!("i{}", self.pointer_width());
                let array = self.emit_array_from_reference(reference);
                let length_address = self.temp();
                let length = self.temp();
                let empty = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.line(&format!("  %{empty} = icmp eq {usize_ty} %{length}, 0"));
                self.emit_runtime_fault_if(empty, RUNTIME_FAULT_INDEX_OUT_OF_BOUNDS);
                let index = self.temp();
                self.line(&format!("  %{index} = sub {usize_ty} %{length}, 1"));
                let (slot, initialized) = self.emit_checked_array_slot(
                    &array,
                    &usize_ty,
                    &format!("%{index}"),
                    &element_ty,
                    true,
                );
                let value = self.temp();
                self.line(&format!("  %{value} = load {element_ty}, ptr {slot}"));
                self.line(&format!("  store i8 0, ptr {initialized}"));
                self.line(&format!(
                    "  store {usize_ty} %{index}, ptr %{length_address}"
                ));
                format!("%{value}")
            }
            Primitive::ArrayReserve => {
                let Some((_, reference)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed Array reserve")]);
                };
                let Some((additional_ty, additional)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed Array reserve")]);
                };
                self.referenced_array_element(function, args[0].register)?;
                self.overflow_widths.insert((self.pointer_width(), "uadd"));
                let array = self.emit_array_from_reference(reference);
                let length_address = self.temp();
                let length = self.temp();
                let pair = self.temp();
                let required = self.temp();
                let overflow = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {additional_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{pair} = call {{ {additional_ty}, i1 }} @llvm.uadd.with.overflow.{additional_ty}({additional_ty} %{length}, {additional_ty} {additional})"
                ));
                self.line(&format!(
                    "  %{required} = extractvalue {{ {additional_ty}, i1 }} %{pair}, 0"
                ));
                self.line(&format!(
                    "  %{overflow} = extractvalue {{ {additional_ty}, i1 }} %{pair}, 1"
                ));
                self.emit_runtime_fault_if(overflow, RUNTIME_FAULT_ALLOCATION_OVERFLOW);
                self.line(&format!(
                    "  call void @g1_array_grow(ptr {array}, {additional_ty} %{required})"
                ));
                "0".to_owned()
            }
            Primitive::ArrayFinishDrained => {
                let Some((_, array)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed drained Array finish",
                    )]);
                };
                let array_ty = self.register_runtime_type(function, args[0].register)?;
                let element = self.array_element(array_ty)?;
                self.ensure_plain_array_element(element, function)?;
                let usize_ty = format!("i{}", self.pointer_width());
                let length_address = self.temp();
                let length = self.temp();
                let empty = self.temp();
                let loop_id = self.temp();
                let index_address = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
                ));
                self.line(&format!(
                    "  %{length} = load {usize_ty}, ptr %{length_address}"
                ));
                self.line(&format!("  %{empty} = icmp eq {usize_ty} %{length}, 0"));
                self.line(&format!("  %{index_address} = alloca {usize_ty}"));
                self.line(&format!("  store {usize_ty} 0, ptr %{index_address}"));
                self.line(&format!(
                    "  br i1 %{empty}, label %array.drain.done{loop_id}, label %array.drain.check{loop_id}"
                ));
                self.line(&format!("array.drain.check{loop_id}:"));
                let index = self.temp();
                let initialized_address = self.temp();
                let initialized = self.temp();
                let slot = self.temp();
                let state = self.temp();
                let occupied = self.temp();
                self.line(&format!(
                    "  %{index} = load {usize_ty}, ptr %{index_address}"
                ));
                self.line(&format!(
                    "  %{initialized_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
                ));
                self.line(&format!(
                    "  %{initialized} = load ptr, ptr %{initialized_address}"
                ));
                self.line(&format!(
                    "  %{slot} = getelementptr inbounds i8, ptr %{initialized}, {usize_ty} %{index}"
                ));
                self.line(&format!("  %{state} = load i8, ptr %{slot}"));
                self.line(&format!("  %{occupied} = icmp ne i8 %{state}, 0"));
                let trap_label = self.temp();
                let continue_label = self.temp();
                self.line(&format!(
                    "  br i1 %{occupied}, label %array.drain.trap{trap_label}, label %array.drain.continue{continue_label}"
                ));
                self.line(&format!("array.drain.trap{trap_label}:"));
                self.emit_runtime_fault(RUNTIME_FAULT_ARRAY_NOT_DRAINED, "0", "0", "null", "0");
                self.line(&format!("array.drain.continue{continue_label}:"));
                let next = self.temp();
                let more = self.temp();
                self.line(&format!("  %{next} = add {usize_ty} %{index}, 1"));
                self.line(&format!("  store {usize_ty} %{next}, ptr %{index_address}"));
                self.line(&format!(
                    "  %{more} = icmp ult {usize_ty} %{next}, %{length}"
                ));
                self.line(&format!(
                    "  br i1 %{more}, label %array.drain.check{loop_id}, label %array.drain.done{loop_id}"
                ));
                self.line(&format!("array.drain.done{loop_id}:"));
                self.line(&format!("  call void @g1_array_free(ptr {array})"));
                "0".to_owned()
            }
            Primitive::TextByteLen | Primitive::BytesLen => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed byte length operation",
                    )]);
                };
                let length_address = self.temp();
                let length = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.bytes, ptr {object}, i32 0, i32 1"
                ));
                self.line(&format!(
                    "  %{length} = load {dst_ty}, ptr %{length_address}"
                ));
                self.release_byte_operands(function, args, &loaded)?;
                format!("%{length}")
            }
            Primitive::TextEq => {
                let Some((_, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed text equality")]);
                };
                let result = self.temp();
                self.line(&format!(
                    "  %{result} = call i32 @g1_bytes_equal(ptr {left}, ptr {right})"
                ));
                self.release_byte_operands(function, args, &loaded)?;
                format!("%{result}")
            }
            Primitive::TextConcat | Primitive::BytesConcat => {
                let Some((_, left, right)) = binary_operands(&loaded) else {
                    return Err(vec![unsupported(function, "malformed byte concatenation")]);
                };
                let result = self.emit_byte_concat(left, right);
                self.release_byte_operands(function, args, &loaded)?;
                result
            }
            Primitive::TextFromUtf8Checked => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed checked UTF-8 conversion",
                    )]);
                };
                let valid = self.temp();
                self.line(&format!(
                    "  %{valid} = call i1 @g1_utf8_validate(ptr {object})"
                ));
                let invalid = self.temp();
                self.line(&format!("  %{invalid} = xor i1 %{valid}, true"));
                self.emit_runtime_fault_if(invalid, RUNTIME_FAULT_INVALID_UTF8);
                object.clone()
            }
            Primitive::BytesUtf8ValidUpTo => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed UTF-8 prefix query")]);
                };
                let valid_up_to = self.temp();
                self.line(&format!(
                    "  %{valid_up_to} = call {dst_ty} @g1_utf8_valid_up_to(ptr {object})"
                ));
                self.release_byte_operands(function, args, &loaded)?;
                format!("%{valid_up_to}")
            }
            Primitive::TextAsBytes => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed Text-to-Bytes conversion",
                    )]);
                };
                object.clone()
            }
            Primitive::BytesGet => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed byte indexing")]);
                };
                let Some((index_ty, index)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed byte indexing")]);
                };
                let length_address = self.temp();
                let length = self.temp();
                let invalid = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.bytes, ptr {object}, i32 0, i32 1"
                ));
                self.line(&format!(
                    "  %{length} = load {index_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{invalid} = icmp uge {index_ty} {index}, %{length}"
                ));
                self.emit_runtime_fault_if(invalid, RUNTIME_FAULT_INDEX_OUT_OF_BOUNDS);
                let data = self.temp();
                let address = self.temp();
                let byte = self.temp();
                self.line(&format!(
                    "  %{data} = call ptr @g1_bytes_data(ptr {object})"
                ));
                self.line(&format!(
                    "  %{address} = getelementptr inbounds i8, ptr %{data}, {index_ty} {index}"
                ));
                self.line(&format!("  %{byte} = load i8, ptr %{address}"));
                self.release_byte_operands(function, args, &loaded)?;
                format!("%{byte}")
            }
            Primitive::BytesSlice => {
                let Some((_, object)) = loaded.first() else {
                    return Err(vec![unsupported(function, "malformed byte slice")]);
                };
                let Some((index_ty, start)) = loaded.get(1) else {
                    return Err(vec![unsupported(function, "malformed byte slice")]);
                };
                let Some((end_ty, end)) = loaded.get(2) else {
                    return Err(vec![unsupported(function, "malformed byte slice")]);
                };
                if index_ty != end_ty {
                    return Err(vec![unsupported(
                        function,
                        "byte slice index width mismatch",
                    )]);
                }
                let length_address = self.temp();
                let source_length = self.temp();
                let reverse = self.temp();
                let beyond = self.temp();
                let invalid = self.temp();
                self.line(&format!(
                    "  %{length_address} = getelementptr inbounds %g1.bytes, ptr {object}, i32 0, i32 1"
                ));
                self.line(&format!(
                    "  %{source_length} = load {index_ty}, ptr %{length_address}"
                ));
                self.line(&format!(
                    "  %{reverse} = icmp ugt {index_ty} {start}, {end}"
                ));
                self.line(&format!(
                    "  %{beyond} = icmp ugt {index_ty} {end}, %{source_length}"
                ));
                self.line(&format!("  %{invalid} = or i1 %{reverse}, %{beyond}"));
                self.emit_runtime_fault_if(invalid, RUNTIME_FAULT_INDEX_OUT_OF_BOUNDS);
                let length = self.temp();
                let result = self.temp();
                let source_data = self.temp();
                let source_start = self.temp();
                let result_data = self.temp();
                self.line(&format!("  %{length} = sub {index_ty} {end}, {start}"));
                self.line(&format!(
                    "  %{result} = call ptr @g1_bytes_allocate({index_ty} %{length})"
                ));
                self.line(&format!(
                    "  %{source_data} = call ptr @g1_bytes_data(ptr {object})"
                ));
                self.line(&format!(
                    "  %{source_start} = getelementptr inbounds i8, ptr %{source_data}, {index_ty} {start}"
                ));
                self.line(&format!(
                    "  %{result_data} = call ptr @g1_bytes_data(ptr %{result})"
                ));
                self.line(&format!(
                    "  call void @llvm.memcpy.p0.p0.{index_ty}(ptr %{result_data}, ptr %{source_start}, {index_ty} %{length}, i1 false)"
                ));
                self.release_byte_operands(function, args, &loaded)?;
                format!("%{result}")
            }
            Primitive::CharToU32 => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed character conversion",
                    )]);
                };
                if source_ty != &dst_ty {
                    return Err(vec![unsupported(
                        function,
                        "character conversion with mismatched widths",
                    )]);
                }
                value.clone()
            }
            Primitive::CharFromU32Checked => {
                let Some((source_ty, value)) = loaded.first() else {
                    return Err(vec![unsupported(
                        function,
                        "malformed character conversion",
                    )]);
                };
                if source_ty != &dst_ty {
                    return Err(vec![unsupported(
                        function,
                        "character conversion with mismatched widths",
                    )]);
                }
                let above_unicode = self.temp();
                let surrogate_start = self.temp();
                let surrogate_end = self.temp();
                let surrogate = self.temp();
                let invalid = self.temp();
                self.line(&format!(
                    "  %{above_unicode} = icmp ugt {source_ty} {value}, 1114111"
                ));
                self.line(&format!(
                    "  %{surrogate_start} = icmp uge {source_ty} {value}, 55296"
                ));
                self.line(&format!(
                    "  %{surrogate_end} = icmp ule {source_ty} {value}, 57343"
                ));
                self.line(&format!(
                    "  %{surrogate} = and i1 %{surrogate_start}, %{surrogate_end}"
                ));
                self.line(&format!(
                    "  %{invalid} = or i1 %{above_unicode}, %{surrogate}"
                ));
                self.emit_runtime_fault_if(invalid, RUNTIME_FAULT_INVALID_CHARACTER);
                value.clone()
            }
        };
        self.line(&format!("  store {dst_ty} {result}, ptr %r{dst}"));
        Ok(())
    }

    fn emit_terminator(
        &mut self,
        function_index: usize,
        function: &mir::Function,
        terminator: &Terminator,
    ) -> Result<(), Vec<Diagnostic>> {
        match terminator {
            Terminator::Goto(edge) => self.emit_edge(function, edge)?,
            Terminator::Return { value } => {
                if let Some(value) = value {
                    let ty = self.register_type(function, value.register)?;
                    let loaded = self.load_operand(function, value)?;
                    if value.mode == mir::UseMode::Copy {
                        let runtime_ty = self.register_runtime_type(function, value.register)?;
                        self.emit_retain(runtime_ty, &loaded, function)?;
                    }
                    self.line(&format!("  ret {ty} {loaded}"));
                } else {
                    self.line("  ret void");
                }
            }
            Terminator::Call {
                result,
                function: callee,
                args,
                normal,
            } => self.emit_call(function, *result, *callee as usize, args, normal, false)?,
            Terminator::CallSelf {
                result,
                args,
                normal,
            } => self.emit_call(function, *result, function_index, args, normal, false)?,
            Terminator::CallKnownReceiver {
                result,
                function: callee,
                receiver,
                args,
                normal,
            } => self.emit_call_with_receiver(
                function,
                *result,
                *callee as usize,
                receiver,
                args,
                normal,
                false,
            )?,
            Terminator::HostCall {
                result,
                import,
                args,
                normal,
            } => self.emit_host_call(function, *result, *import, args, normal)?,
            Terminator::CallIndirect {
                result,
                callable,
                known_function,
                receiver_mode,
                cleanup_callable,
                args,
                normal,
            } => self.emit_indirect_call(
                function,
                *result,
                callable,
                *known_function,
                *receiver_mode,
                *cleanup_callable,
                args,
                Some(normal),
            )?,
            Terminator::Handle {
                result,
                handler,
                body,
                normal,
            } => self.emit_terminal_handle(function, *result, handler, body, normal)?,
            Terminator::Resume {
                result,
                resumption,
                receiver_mode,
                value,
                normal,
            } => self.emit_one_shot_resume(
                function,
                *result,
                resumption,
                *receiver_mode,
                value,
                normal,
            )?,
            Terminator::TailResume {
                resumption,
                receiver_mode,
                value,
            } => self.emit_one_shot_tail_resume(function, resumption, *receiver_mode, value)?,
            Terminator::Cancel {
                result,
                resumption,
                normal,
            } => self.emit_one_shot_cancel(function, *result, resumption, normal)?,
            Terminator::TailCall {
                function: callee,
                args,
            } => self.emit_tail_call(function, *callee as usize, args)?,
            Terminator::TailCallSelf { args } => {
                self.emit_tail_call(function, function_index, args)?
            }
            Terminator::TailCallKnownReceiver {
                function: callee,
                receiver,
                args,
            } => self.emit_call_with_receiver(
                function,
                None,
                *callee as usize,
                receiver,
                args,
                &mir::Edge {
                    target: u32::MAX,
                    args: Vec::new(),
                },
                true,
            )?,
            Terminator::TailCallIndirect {
                callable,
                known_function,
                receiver_mode,
                args,
            } => self.emit_indirect_call(
                function,
                None,
                callable,
                *known_function,
                *receiver_mode,
                false,
                args,
                None,
            )?,
            Terminator::Switch {
                discr,
                cases,
                otherwise,
            } => {
                let ty = self.register_type(function, discr.register)?;
                let value = self.load_operand(function, discr)?;
                let switch_id = self.temp();
                let otherwise_label = self.temp();
                let case_labels = cases.iter().map(|_| self.temp()).collect::<Vec<_>>();
                self.line(&format!(
                    "  switch {ty} {value}, label %switch.edge{switch_id}.{otherwise_label} ["
                ));
                for ((constant, _), label) in cases.iter().zip(&case_labels) {
                    self.line(&format!(
                        "    {ty} {}, label %switch.edge{switch_id}.{label}",
                        llvm_scalar_constant(constant)?,
                    ));
                }
                self.line("  ]");
                self.line(&format!("switch.edge{switch_id}.{otherwise_label}:"));
                self.emit_edge(function, otherwise)?;
                for ((_, edge), label) in cases.iter().zip(case_labels) {
                    self.line(&format!("switch.edge{switch_id}.{label}:"));
                    self.emit_edge(function, edge)?;
                }
            }
            Terminator::Leave { target, .. } => self.emit_edge(function, target)?,
            Terminator::Abort { message } => self.emit_abort(message.as_deref()),
            Terminator::Unreachable => {
                self.line("  call void @llvm.trap()");
                self.line("  unreachable");
            }
            other => {
                return Err(vec![unsupported(
                    function,
                    format!("MIR terminator {other:?}"),
                )]);
            }
        }
        Ok(())
    }

    fn native_resumption_types(
        &self,
        function: &mir::Function,
        resumption: &mir::Operand,
    ) -> Result<(TypeId, TypeId, TypeId, u32, Option<u32>, bool), Vec<Diagnostic>> {
        let resumption_type = self.register_runtime_type(function, resumption.register)?;
        let Type::Resumption {
            input_type,
            output_type,
            lower_uses,
            upper_uses,
            copy,
            ..
        } = self.runtime_type(resumption_type)?
        else {
            return Err(vec![unsupported(
                function,
                "resumption terminator with a non-resumption operand",
            )]);
        };
        Ok((
            resumption_type,
            *input_type,
            *output_type,
            *lower_uses,
            *upper_uses,
            *copy,
        ))
    }

    fn emit_clone_resumption_chain(
        &mut self,
        top: &str,
        resume_slot: &str,
        resume_init: &str,
    ) -> (String, String, String, String) {
        let cloned_top = self.temp();
        let cloned_bottom = self.temp();
        self.line(&format!(
            "  %{cloned_top} = call ptr @g1_effect_clone_chain(ptr {top})"
        ));
        self.line(&format!(
            "  %{cloned_bottom} = call ptr @g1_effect_chain_bottom(ptr %{cloned_top})"
        ));
        let usize_ty = format!("i{}", self.pointer_width());
        let mut rebased = Vec::with_capacity(2);
        for pointer in [resume_slot, resume_init] {
            let present = self.temp();
            let rebase_label = self.temp();
            let null_label = self.temp();
            let done_label = self.temp();
            self.line(&format!("  %{present} = icmp ne ptr {pointer}, null"));
            self.line(&format!(
                "  br i1 %{present}, label %resumption.prepare.rebase{rebase_label}, label %resumption.prepare.null{null_label}"
            ));
            self.line(&format!("resumption.prepare.rebase{rebase_label}:"));
            let pointer_integer = self.temp();
            let top_integer = self.temp();
            let offset = self.temp();
            let cloned_pointer = self.temp();
            self.line(&format!(
                "  %{pointer_integer} = ptrtoint ptr {pointer} to {usize_ty}"
            ));
            self.line(&format!(
                "  %{top_integer} = ptrtoint ptr {top} to {usize_ty}"
            ));
            self.line(&format!(
                "  %{offset} = sub {usize_ty} %{pointer_integer}, %{top_integer}"
            ));
            self.line(&format!(
                "  %{cloned_pointer} = getelementptr inbounds i8, ptr %{cloned_top}, {usize_ty} %{offset}"
            ));
            self.line(&format!(
                "  br label %resumption.prepare.rebased{done_label}"
            ));
            self.line(&format!("resumption.prepare.null{null_label}:"));
            self.line(&format!(
                "  br label %resumption.prepare.rebased{done_label}"
            ));
            self.line(&format!("resumption.prepare.rebased{done_label}:"));
            let final_pointer = self.temp();
            self.line(&format!(
                "  %{final_pointer} = phi ptr [ %{cloned_pointer}, %resumption.prepare.rebase{rebase_label} ], [ null, %resumption.prepare.null{null_label} ]"
            ));
            rebased.push(format!("%{final_pointer}"));
        }
        (
            format!("%{cloned_top}"),
            format!("%{cloned_bottom}"),
            rebased[0].clone(),
            rebased[1].clone(),
        )
    }

    fn emit_prepare_resumption_ownership(
        &mut self,
        function: &mir::Function,
        resumption: &str,
        resumption_type: TypeId,
        borrowed: bool,
    ) -> Result<(String, String, String, String, String), Vec<Diagnostic>> {
        let fields = (0..7)
            .map(|field| {
                let address = self.temp();
                let value = self.temp();
                let ty = match field {
                    5 => "i64",
                    6 => "i1",
                    _ => "ptr",
                };
                self.line(&format!(
                    "  %{address} = getelementptr inbounds %g1.resumption, ptr {resumption}, i32 0, i32 {field}"
                ));
                self.line(&format!("  %{value} = load {ty}, ptr %{address}"));
                format!("%{value}")
            })
            .collect::<Vec<_>>();
        let [top, bottom, resume_slot, resume_init, handler, references, inherited_preserve] =
            fields.as_slice()
        else {
            unreachable!()
        };
        if borrowed {
            let cloned = self.emit_clone_resumption_chain(top, resume_slot, resume_init);
            return Ok((cloned.0, cloned.1, cloned.2, cloned.3, "true".to_owned()));
        }

        let result_slots = (0..4)
            .map(|_| {
                let slot = self.temp();
                self.line(&format!("  %{slot} = alloca ptr"));
                format!("%{slot}")
            })
            .collect::<Vec<_>>();
        let last = self.temp();
        let shared_owner = self.temp();
        let steal_label = self.temp();
        let shared_label = self.temp();
        let ready_label = self.temp();
        self.line(&format!("  %{last} = icmp eq i64 {references}, 1"));
        self.line(&format!("  %{shared_owner} = xor i1 %{last}, true"));
        self.line(&format!(
            "  br i1 %{last}, label %resumption.prepare.steal{steal_label}, label %resumption.prepare.shared{shared_label}"
        ));
        self.line(&format!("resumption.prepare.steal{steal_label}:"));
        for (slot, value) in result_slots
            .iter()
            .zip([top, bottom, resume_slot, resume_init])
        {
            self.line(&format!("  store ptr {value}, ptr {slot}"));
        }
        let clause_tuple = self.resumption_handler_capture_type(function, resumption_type)?;
        self.emit_destroy_handler(handler, clause_tuple, function)?;
        self.line(&format!("  call void @free(ptr {resumption})"));
        self.line(&format!(
            "  br label %resumption.prepare.ready{ready_label}"
        ));

        self.line(&format!("resumption.prepare.shared{shared_label}:"));
        let valid = self.temp();
        self.line(&format!("  %{valid} = icmp ugt i64 {references}, 1"));
        let clone_label = self.temp();
        let invalid_label = self.temp();
        self.line(&format!(
            "  br i1 %{valid}, label %resumption.prepare.clone{clone_label}, label %resumption.prepare.invalid{invalid_label}"
        ));
        self.line(&format!("resumption.prepare.invalid{invalid_label}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        self.line(&format!("resumption.prepare.clone{clone_label}:"));
        let cloned = self.emit_clone_resumption_chain(top, resume_slot, resume_init);
        for (slot, value) in result_slots.iter().zip([
            cloned.0.as_str(),
            cloned.1.as_str(),
            cloned.2.as_str(),
            cloned.3.as_str(),
        ]) {
            self.line(&format!("  store ptr {value}, ptr {slot}"));
        }
        let references_address = self.temp();
        let next = self.temp();
        self.line(&format!(
            "  %{references_address} = getelementptr inbounds %g1.resumption, ptr {resumption}, i32 0, i32 5"
        ));
        self.line(&format!("  %{next} = sub i64 {references}, 1"));
        self.line(&format!("  store i64 %{next}, ptr %{references_address}"));
        self.line(&format!(
            "  br label %resumption.prepare.ready{ready_label}"
        ));
        self.line(&format!("resumption.prepare.ready{ready_label}:"));
        let preserve = self.temp();
        self.line(&format!(
            "  %{preserve} = or i1 {inherited_preserve}, %{shared_owner}"
        ));
        let loaded = result_slots
            .iter()
            .map(|slot| {
                let value = self.temp();
                self.line(&format!("  %{value} = load ptr, ptr {slot}"));
                format!("%{value}")
            })
            .collect::<Vec<_>>();
        Ok((
            loaded[0].clone(),
            loaded[1].clone(),
            loaded[2].clone(),
            loaded[3].clone(),
            format!("%{preserve}"),
        ))
    }

    fn emit_effect_resume(
        &mut self,
        function: &mir::Function,
        result: u32,
        resumption: &mir::Operand,
        receiver_mode: u32,
        value: &mir::Operand,
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let (resumption_type, input_type, output_type, _, upper_uses, copy) =
            self.native_resumption_types(function, resumption)?;
        let reusable = copy || upper_uses.is_none_or(|upper| upper > 1);
        if receiver_mode > 2
            || receiver_mode < 2 && !reusable
            || receiver_mode == 2 && resumption.mode != mir::UseMode::Move
            || value.mode != mir::UseMode::Move
            || self.register_runtime_type(function, value.register)? != input_type
            || self.register_runtime_type(function, result)? != output_type
        {
            return Err(vec![unsupported(
                function,
                "malformed effect-frame Resume terminator",
            )]);
        }

        let resumption_value = self.load_operand(function, resumption)?;
        let input = self.load_operand(function, value)?;
        if receiver_mode == 2 {
            self.emit_effect_set_initialized(function, resumption.register, false)?;
        }
        self.emit_effect_set_initialized(function, value.register, false)?;
        self.emit_effect_set_initialized(function, result, false)?;
        self.emit_edge_arguments(function, normal, [result].into_iter().collect())?;
        let state_address = self.temp();
        self.line(&format!(
            "  %{state_address} = getelementptr inbounds %g1.effect_frame, ptr %frame, i32 0, i32 4"
        ));
        self.line(&format!(
            "  store i32 {}, ptr %{state_address}",
            normal.target
        ));

        let (top, bottom) = self.emit_prepare_effect_resumption(
            function,
            &resumption_value,
            resumption_type,
            input_type,
            &input,
            receiver_mode < 2,
        )?;
        self.emit_splice_effect_resumption(
            &bottom,
            "%frame",
            &format!("%r{result}"),
            &format!("%init{result}"),
        );
        self.emit_effect_runtime_store(0, "ptr", &top);
        self.line("  ret void");
        Ok(())
    }

    fn emit_effect_tail_resume(
        &mut self,
        function_index: usize,
        function: &mir::Function,
        resumption: &mir::Operand,
        receiver_mode: u32,
        value: &mir::Operand,
    ) -> Result<(), Vec<Diagnostic>> {
        let (resumption_type, input_type, output_type, _, upper_uses, _) =
            self.native_resumption_types(function, resumption)?;
        if receiver_mode != 2
            || upper_uses != Some(1)
            || resumption.mode != mir::UseMode::Move
            || value.mode != mir::UseMode::Move
            || self.register_runtime_type(function, value.register)? != input_type
            || function.result != output_type
        {
            return Err(vec![unsupported(
                function,
                "malformed effect-frame TailResume terminator",
            )]);
        }

        let resumption_value = self.load_operand(function, resumption)?;
        let input = self.load_operand(function, value)?;
        self.emit_effect_set_initialized(function, resumption.register, false)?;
        self.emit_effect_set_initialized(function, value.register, false)?;

        let header = self.temp();
        self.line(&format!(
            "  %{header} = getelementptr inbounds {}, ptr %frame, i32 0, i32 0",
            self.effect_frame_type(function_index)
        ));
        let mut continuation = Vec::with_capacity(3);
        for field in [0, 3, 7] {
            let address = self.temp();
            let loaded = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_frame, ptr %{header}, i32 0, i32 {field}"
            ));
            self.line(&format!("  %{loaded} = load ptr, ptr %{address}"));
            continuation.push(format!("%{loaded}"));
        }
        let [previous, return_slot, return_init] = continuation.as_slice() else {
            unreachable!()
        };

        let (top, bottom) = self.emit_prepare_effect_resumption(
            function,
            &resumption_value,
            resumption_type,
            input_type,
            &input,
            false,
        )?;
        self.emit_splice_effect_resumption(&bottom, previous, return_slot, return_init);
        self.emit_effect_runtime_store(0, "ptr", &top);
        self.line(&format!(
            "  call void @g1_effect_drop_f{function_index}(ptr %frame)"
        ));
        self.line("  ret void");
        Ok(())
    }

    fn emit_effect_cancel(
        &mut self,
        function: &mir::Function,
        result: u32,
        resumption: &mir::Operand,
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let (resumption_type, ..) = self.native_resumption_types(function, resumption)?;
        if resumption.mode != mir::UseMode::Move
            || !matches!(
                self.runtime_type(self.register_runtime_type(function, result)?)?,
                Type::Unit
            )
        {
            return Err(vec![unsupported(
                function,
                "malformed effect-frame Cancel terminator",
            )]);
        }
        let resumption_value = self.load_operand(function, resumption)?;
        self.emit_effect_set_initialized(function, resumption.register, false)?;
        self.emit_release_resumption(&resumption_value, resumption_type, function)?;
        self.line(&format!("  store i8 0, ptr %r{result}"));
        self.emit_effect_set_initialized(function, result, true)?;
        self.emit_effect_edge(function, normal, [result].into_iter().collect())
    }

    fn emit_prepare_effect_resumption(
        &mut self,
        function: &mir::Function,
        resumption: &str,
        resumption_type: TypeId,
        input_type: TypeId,
        input: &str,
        clone_snapshot: bool,
    ) -> Result<(String, String), Vec<Diagnostic>> {
        let (top, bottom, resume_slot, resume_init, preserve_clauses) = self
            .emit_prepare_resumption_ownership(
                function,
                resumption,
                resumption_type,
                clone_snapshot,
            )?;
        self.emit_set_effect_chain_preserve(&top, &preserve_clauses);

        let input_ty = self.llvm_type(input_type)?;
        self.line(&format!("  store {input_ty} {input}, ptr {resume_slot}"));
        let has_init = self.temp();
        let mark_label = self.temp();
        let marked_label = self.temp();
        self.line(&format!("  %{has_init} = icmp ne ptr {resume_init}, null"));
        self.line(&format!(
            "  br i1 %{has_init}, label %effect.resume.mark{mark_label}, label %effect.resume.marked{marked_label}"
        ));
        self.line(&format!("effect.resume.mark{mark_label}:"));
        self.line(&format!("  store i8 1, ptr {resume_init}"));
        self.line(&format!("  br label %effect.resume.marked{marked_label}"));
        self.line(&format!("effect.resume.marked{marked_label}:"));

        Ok((top, bottom))
    }

    fn emit_set_effect_chain_preserve(&mut self, top: &str, preserve: &str) {
        let current_slot = self.temp();
        let loop_label = self.temp();
        let set_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  %{current_slot} = alloca ptr"));
        self.line(&format!("  store ptr {top}, ptr %{current_slot}"));
        self.line(&format!("  br label %resumption.preserve.loop{loop_label}"));
        self.line(&format!("resumption.preserve.loop{loop_label}:"));
        let current = self.temp();
        let present = self.temp();
        self.line(&format!("  %{current} = load ptr, ptr %{current_slot}"));
        self.line(&format!("  %{present} = icmp ne ptr %{current}, null"));
        self.line(&format!(
            "  br i1 %{present}, label %resumption.preserve.set{set_label}, label %resumption.preserve.done{done_label}"
        ));
        self.line(&format!("resumption.preserve.set{set_label}:"));
        let preserve_address = self.temp();
        let previous_address = self.temp();
        let previous = self.temp();
        self.line(&format!(
            "  %{preserve_address} = getelementptr inbounds %g1.effect_frame, ptr %{current}, i32 0, i32 10"
        ));
        self.line(&format!("  store i1 {preserve}, ptr %{preserve_address}"));
        self.line(&format!(
            "  %{previous_address} = getelementptr inbounds %g1.effect_frame, ptr %{current}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{previous} = load ptr, ptr %{previous_address}"
        ));
        self.line(&format!("  store ptr %{previous}, ptr %{current_slot}"));
        self.line(&format!("  br label %resumption.preserve.loop{loop_label}"));
        self.line(&format!("resumption.preserve.done{done_label}:"));
    }

    fn emit_splice_effect_resumption(
        &mut self,
        bottom: &str,
        previous: &str,
        return_slot: &str,
        return_init: &str,
    ) {
        for (field, value) in [(0, previous), (3, return_slot), (7, return_init)] {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_frame, ptr {bottom}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store ptr {value}, ptr %{address}"));
        }
    }

    fn emit_one_shot_resume(
        &mut self,
        function: &mir::Function,
        result: u32,
        resumption: &mir::Operand,
        receiver_mode: u32,
        value: &mir::Operand,
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let (resumption_type, input_type, output_type, _, upper_uses, copy) =
            self.native_resumption_types(function, resumption)?;
        let reusable = copy || upper_uses.is_none_or(|upper| upper > 1);
        if receiver_mode > 2
            || receiver_mode < 2 && !reusable
            || receiver_mode == 2 && resumption.mode != mir::UseMode::Move
            || value.mode != mir::UseMode::Move
            || self.register_runtime_type(function, value.register)? != input_type
            || self.register_runtime_type(function, result)? != output_type
        {
            return Err(vec![unsupported(
                function,
                "malformed one-shot Resume terminator",
            )]);
        }
        let resumption_value = self.load_operand(function, resumption)?;
        let input = self.load_operand(function, value)?;
        self.emit_run_one_shot_resumption(
            function,
            &resumption_value,
            resumption_type,
            input_type,
            &input,
            &format!("%r{result}"),
            receiver_mode < 2,
        )?;
        self.emit_edge_with_preassigned(function, normal, [result].into_iter().collect())
    }

    fn emit_one_shot_tail_resume(
        &mut self,
        function: &mir::Function,
        resumption: &mir::Operand,
        receiver_mode: u32,
        value: &mir::Operand,
    ) -> Result<(), Vec<Diagnostic>> {
        let (resumption_type, input_type, output_type, _, upper_uses, _) =
            self.native_resumption_types(function, resumption)?;
        if receiver_mode != 2
            || upper_uses != Some(1)
            || resumption.mode != mir::UseMode::Move
            || value.mode != mir::UseMode::Move
            || self.register_runtime_type(function, value.register)? != input_type
            || function.result != output_type
        {
            return Err(vec![unsupported(
                function,
                "malformed one-shot TailResume terminator",
            )]);
        }
        let output_ty = self.llvm_type(output_type)?;
        let output = self.temp();
        self.line(&format!("  %{output} = alloca {output_ty}"));
        let resumption_value = self.load_operand(function, resumption)?;
        let input = self.load_operand(function, value)?;
        self.emit_run_one_shot_resumption(
            function,
            &resumption_value,
            resumption_type,
            input_type,
            &input,
            &format!("%{output}"),
            false,
        )?;
        if matches!(self.runtime_type(output_type)?, Type::Unit) {
            self.line("  ret void");
        } else {
            let returned = self.temp();
            self.line(&format!("  %{returned} = load {output_ty}, ptr %{output}"));
            self.line(&format!("  ret {output_ty} %{returned}"));
        }
        Ok(())
    }

    fn emit_one_shot_cancel(
        &mut self,
        function: &mir::Function,
        result: u32,
        resumption: &mir::Operand,
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let (resumption_type, ..) = self.native_resumption_types(function, resumption)?;
        if resumption.mode != mir::UseMode::Move
            || !matches!(
                self.runtime_type(self.register_runtime_type(function, result)?)?,
                Type::Unit
            )
        {
            return Err(vec![unsupported(
                function,
                "malformed one-shot Cancel terminator",
            )]);
        }
        let resumption_value = self.load_operand(function, resumption)?;
        self.emit_release_resumption(&resumption_value, resumption_type, function)?;
        self.line(&format!("  store i8 0, ptr %r{result}"));
        self.emit_edge_with_preassigned(function, normal, [result].into_iter().collect())
    }

    fn emit_run_one_shot_resumption(
        &mut self,
        function: &mir::Function,
        resumption: &str,
        resumption_type: TypeId,
        input_type: TypeId,
        input: &str,
        return_slot: &str,
        clone_snapshot: bool,
    ) -> Result<(), Vec<Diagnostic>> {
        let matching_handlers = self
            .phases
            .artifact
            .handler_defs
            .iter()
            .enumerate()
            .filter(|(_, definition)| {
                definition
                    .clauses
                    .iter()
                    .any(|clause| clause.resumption_type == Some(resumption_type))
            })
            .map(|(index, definition)| (index as u32, definition.clone()))
            .collect::<Vec<_>>();
        let [(handler_def, definition)] = matching_handlers.as_slice() else {
            return Err(vec![unsupported(
                function,
                "one-shot resumption does not identify exactly one handler",
            )]);
        };
        let clause_tuple = self
            .phases
            .artifact
            .types
            .iter()
            .find_map(|ty| match ty.representation() {
                Type::Handler {
                    handler_def: described,
                    capture_type,
                    ..
                } if described == handler_def => Some(*capture_type),
                _ => None,
            })
            .ok_or_else(|| vec![unsupported(function, "resumption handler type is missing")])?;
        let clause_types = self.runtime_aggregate_fields(clause_tuple)?;
        if clause_types.len() != definition.clauses.len() {
            return Err(vec![unsupported(
                function,
                "resumption handler clause layout mismatch",
            )]);
        }
        let (top, bottom, resume_slot, resume_init, preserve_clauses) = self
            .emit_prepare_resumption_ownership(
                function,
                resumption,
                resumption_type,
                clone_snapshot,
            )?;
        let input_ty = self.llvm_type(input_type)?;
        self.line(&format!("  store {input_ty} {input}, ptr {resume_slot}"));
        let has_init = self.temp();
        let mark_label = self.temp();
        let marked_label = self.temp();
        self.line(&format!("  %{has_init} = icmp ne ptr {resume_init}, null"));
        self.line(&format!(
            "  br i1 %{has_init}, label %resume.mark{mark_label}, label %resume.marked{marked_label}"
        ));
        self.line(&format!("resume.mark{mark_label}:"));
        self.line(&format!("  store i8 1, ptr {resume_init}"));
        self.line(&format!("  br label %resume.marked{marked_label}"));
        self.line(&format!("resume.marked{marked_label}:"));

        let return_address = self.temp();
        let return_init_address = self.temp();
        self.line(&format!(
            "  %{return_address} = getelementptr inbounds %g1.effect_frame, ptr {bottom}, i32 0, i32 3"
        ));
        self.line(&format!("  store ptr {return_slot}, ptr %{return_address}"));
        self.line(&format!(
            "  %{return_init_address} = getelementptr inbounds %g1.effect_frame, ptr {bottom}, i32 0, i32 7"
        ));
        self.line(&format!("  store ptr null, ptr %{return_init_address}"));

        let runtime = self.temp();
        self.line(&format!("  %{runtime} = alloca %g1.effect_runtime"));
        for (field, ty, value) in [
            (0, "ptr", top.clone()),
            (1, "i32", "-1".to_owned()),
            (2, "i32", "0".to_owned()),
            (3, "i32", "0".to_owned()),
            (4, "ptr", "null".to_owned()),
            (5, "ptr", "null".to_owned()),
            (6, "ptr", "null".to_owned()),
            (7, "ptr", "null".to_owned()),
            (8, "i1", "false".to_owned()),
        ] {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_runtime, ptr %{runtime}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store {ty} {value}, ptr %{address}"));
        }
        let loop_label = self.temp();
        let step_label = self.temp();
        let stopped_label = self.temp();
        self.line(&format!("  br label %resume.loop{loop_label}"));
        self.line(&format!("resume.loop{loop_label}:"));
        let current = self.load_effect_runtime_field(&format!("%{runtime}"), 0, "ptr");
        let running = self.temp();
        self.line(&format!("  %{running} = icmp ne ptr {current}, null"));
        self.line(&format!(
            "  br i1 %{running}, label %resume.step{step_label}, label %resume.stopped{stopped_label}"
        ));
        self.line(&format!("resume.step{step_label}:"));
        let step_address = self.temp();
        let step = self.temp();
        self.line(&format!(
            "  %{step_address} = getelementptr inbounds %g1.effect_frame, ptr {current}, i32 0, i32 1"
        ));
        self.line(&format!("  %{step} = load ptr, ptr %{step_address}"));
        self.line(&format!(
            "  call void %{step}(ptr {current}, ptr %{runtime})"
        ));
        self.line(&format!("  br label %resume.loop{loop_label}"));
        self.line(&format!("resume.stopped{stopped_label}:"));
        let status = self.load_effect_runtime_field(&format!("%{runtime}"), 1, "i32");
        let normal_label = self.temp();
        let perform_label = self.temp();
        let invalid = self.temp();
        self.line(&format!(
            "  switch i32 {status}, label %resume.invalid{invalid} [ i32 0, label %resume.normal{normal_label} i32 1, label %resume.perform{perform_label} ]"
        ));
        self.line(&format!("resume.invalid{invalid}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        let done_label = self.temp();
        self.line(&format!("resume.normal{normal_label}:"));
        let completed = self.load_effect_runtime_field(&format!("%{runtime}"), 5, "ptr");
        self.emit_drop_optional_effect_frame(&completed);
        self.line(&format!("  br label %resume.done{done_label}"));

        self.line(&format!("resume.perform{perform_label}:"));
        let unhandled = self.temp();
        self.emit_effect_request_router(
            function,
            &format!("%{runtime}"),
            &format!("resume.loop{loop_label}"),
            &format!("resume.unhandled{unhandled}"),
            if clone_snapshot {
                EffectRoutingMode::ReplayBorrowed
            } else {
                EffectRoutingMode::ReplayConditional(preserve_clauses)
            },
        )?;
        self.line(&format!("resume.unhandled{unhandled}:"));
        let protocol = self.load_effect_runtime_field(&format!("%{runtime}"), 2, "i32");
        let operation = self.load_effect_runtime_field(&format!("%{runtime}"), 3, "i32");
        self.emit_runtime_fault(
            RUNTIME_FAULT_UNHANDLED_EFFECT,
            &protocol,
            &operation,
            "null",
            "0",
        );
        self.line(&format!("resume.done{done_label}:"));
        Ok(())
    }

    fn emit_terminal_handle(
        &mut self,
        function: &mir::Function,
        result: u32,
        handler_operand: &mir::Operand,
        body_operand: &mir::Operand,
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        if handler_operand.mode != mir::UseMode::Move || body_operand.mode != mir::UseMode::Move {
            return Err(vec![unsupported(
                function,
                "native handlers require owned handler and body operands",
            )]);
        }
        let handler_type = self.register_runtime_type(function, handler_operand.register)?;
        let Type::Handler {
            handler_def,
            capture_type: clause_tuple,
            ..
        } = self.runtime_type(handler_type)?.clone()
        else {
            return Err(vec![unsupported(
                function,
                "Handle with a non-handler value",
            )]);
        };
        let definition = self
            .phases
            .artifact
            .handler_defs
            .get(handler_def as usize)
            .cloned()
            .ok_or_else(|| vec![unsupported(function, "Handle descriptor is missing")])?;
        for resumption_type in definition
            .clauses
            .iter()
            .filter_map(|clause| clause.resumption_type)
        {
            let Type::Resumption { .. } = self.runtime_type(resumption_type)? else {
                return Err(vec![unsupported(
                    function,
                    "handler clause has a non-resumption continuation type",
                )]);
            };
        }
        let clause_types = self.runtime_aggregate_fields(clause_tuple)?;
        if clause_types.len() != definition.clauses.len() {
            return Err(vec![unsupported(
                function,
                "handler clause layout does not match its descriptor",
            )]);
        }
        let body_type = self.register_runtime_type(function, body_operand.register)?;
        let Type::Callable {
            signature,
            capture_type: _,
            receiver_mode,
            ..
        } = self.runtime_type(body_type)?.clone()
        else {
            return Err(vec![unsupported(function, "Handle body is not callable")]);
        };
        if receiver_mode != 2 || !signature.params.is_empty() {
            return Err(vec![unsupported(
                function,
                "native Handle body must be an owned nullary callable",
            )]);
        }
        if signature.result != definition.result_type
            || self.register_runtime_type(function, result)? != definition.result_type
        {
            return Err(vec![unsupported(
                function,
                "native Handle result type mismatch",
            )]);
        }

        let handler = self.load_operand(function, handler_operand)?;
        let body = self.load_operand(function, body_operand)?;
        let activation =
            self.emit_allocate_handler_activation(&handler, handler_def, "null", false);
        let starter_address = self.temp();
        let starter = self.temp();
        let missing = self.temp();
        self.line(&format!(
            "  %{starter_address} = getelementptr inbounds %g1.callable, ptr {body}, i32 0, i32 3"
        ));
        self.line(&format!("  %{starter} = load ptr, ptr %{starter_address}"));
        self.line(&format!("  %{missing} = icmp eq ptr %{starter}, null"));
        self.emit_trap_if(missing);
        let frame = self.temp();
        self.line(&format!(
            "  %{frame} = call ptr %{starter}(ptr {body}, i1 true, ptr null, ptr %r{result}, ptr null, ptr {activation}, ptr {activation})"
        ));
        let miss = self.temp();

        let runtime = self.temp();
        self.line(&format!("  %{runtime} = alloca %g1.effect_runtime"));
        for (field, ty, value) in [
            (0, "ptr", format!("%{frame}")),
            (1, "i32", "-1".to_owned()),
            (2, "i32", "0".to_owned()),
            (3, "i32", "0".to_owned()),
            (4, "ptr", "null".to_owned()),
            (5, "ptr", "null".to_owned()),
            (6, "ptr", "null".to_owned()),
            (7, "ptr", "null".to_owned()),
            (8, "i1", "false".to_owned()),
        ] {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.effect_runtime, ptr %{runtime}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store {ty} {value}, ptr %{address}"));
        }
        let loop_label = self.temp();
        let step_label = self.temp();
        let stopped_label = self.temp();
        self.line(&format!("  br label %handle.loop{loop_label}"));
        self.line(&format!("handle.loop{loop_label}:"));
        let top_address = self.temp();
        let top = self.temp();
        let running = self.temp();
        self.line(&format!(
            "  %{top_address} = getelementptr inbounds %g1.effect_runtime, ptr %{runtime}, i32 0, i32 0"
        ));
        self.line(&format!("  %{top} = load ptr, ptr %{top_address}"));
        self.line(&format!("  %{running} = icmp ne ptr %{top}, null"));
        self.line(&format!(
            "  br i1 %{running}, label %handle.step{step_label}, label %handle.stopped{stopped_label}"
        ));
        self.line(&format!("handle.step{step_label}:"));
        let step_address = self.temp();
        let step = self.temp();
        self.line(&format!(
            "  %{step_address} = getelementptr inbounds %g1.effect_frame, ptr %{top}, i32 0, i32 1"
        ));
        self.line(&format!("  %{step} = load ptr, ptr %{step_address}"));
        self.line(&format!("  call void %{step}(ptr %{top}, ptr %{runtime})"));
        self.line(&format!("  br label %handle.loop{loop_label}"));
        self.line(&format!("handle.stopped{stopped_label}:"));
        let status_address = self.temp();
        let status = self.temp();
        let normal_label = self.temp();
        let perform_label = self.temp();
        self.line(&format!(
            "  %{status_address} = getelementptr inbounds %g1.effect_runtime, ptr %{runtime}, i32 0, i32 1"
        ));
        self.line(&format!("  %{status} = load i32, ptr %{status_address}"));
        self.line(&format!(
            "  switch i32 %{status}, label %handle.invalid{miss} [ i32 0, label %handle.normal{normal_label} i32 1, label %handle.perform{perform_label} ]"
        ));

        self.line(&format!("handle.normal{normal_label}:"));
        let completed = self.load_effect_runtime_field(&format!("%{runtime}"), 5, "ptr");
        self.emit_drop_optional_effect_frame(&completed);
        self.emit_edge_with_preassigned(function, normal, [result].into_iter().collect())?;

        self.line(&format!("handle.perform{perform_label}:"));
        let unhandled = self.temp();
        self.emit_effect_request_router(
            function,
            &format!("%{runtime}"),
            &format!("handle.loop{loop_label}"),
            &format!("handle.unhandled{unhandled}"),
            EffectRoutingMode::Initial,
        )?;

        self.line(&format!("handle.unhandled{unhandled}:"));
        let protocol = self.load_effect_runtime_field(&format!("%{runtime}"), 2, "i32");
        let operation = self.load_effect_runtime_field(&format!("%{runtime}"), 3, "i32");
        self.emit_runtime_fault(
            RUNTIME_FAULT_UNHANDLED_EFFECT,
            &protocol,
            &operation,
            "null",
            "0",
        );
        self.line(&format!("handle.invalid{miss}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        Ok(())
    }

    fn emit_effect_request_router(
        &mut self,
        function: &mir::Function,
        runtime: &str,
        loop_target: &str,
        invalid_target: &str,
        mode: EffectRoutingMode,
    ) -> Result<(), Vec<Diagnostic>> {
        let protocol = self.load_effect_runtime_field(runtime, 2, "i32");
        let operation = self.load_effect_runtime_field(runtime, 3, "i32");
        let payload = self.load_effect_runtime_field(runtime, 4, "ptr");
        let suspended = self.load_effect_runtime_field(runtime, 5, "ptr");
        let resume_slot = self.load_effect_runtime_field(runtime, 6, "ptr");
        let resume_init = self.load_effect_runtime_field(runtime, 7, "ptr");
        let runtime_preserve = self.load_effect_runtime_field(runtime, 8, "i1");
        let terminal_preserve = match &mode {
            EffectRoutingMode::Initial => Some(runtime_preserve),
            EffectRoutingMode::ReplayConditional(condition) => {
                let preserve = self.temp();
                self.line(&format!(
                    "  %{preserve} = or i1 {condition}, {runtime_preserve}"
                ));
                Some(format!("%{preserve}"))
            }
            EffectRoutingMode::ReplayBorrowed => None,
        };
        let definitions = self
            .phases
            .artifact
            .handler_defs
            .iter()
            .enumerate()
            .map(|(handler_def, definition)| {
                let capture_type = self.handler_capture_type(handler_def as u32)?;
                let clause_types = self.runtime_aggregate_fields(capture_type)?;
                if clause_types.len() != definition.clauses.len() {
                    return Err(vec![unsupported(
                        function,
                        "handler clause layout does not match its descriptor",
                    )]);
                }
                Ok((
                    handler_def as u32,
                    definition.clone(),
                    capture_type,
                    clause_types,
                ))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        let clause_labels = definitions
            .iter()
            .map(|(_, definition, _, _)| {
                definition
                    .clauses
                    .iter()
                    .map(|_| self.temp())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let cursor = self.temp();
        let scan_label = self.temp();
        let inspect_label = self.temp();
        let activation_label = self.temp();
        let advance_label = self.temp();
        self.line(&format!("  %{cursor} = alloca ptr"));
        self.line(&format!("  store ptr {suspended}, ptr %{cursor}"));
        self.line(&format!("  br label %handle.route.scan{scan_label}"));
        self.line(&format!("handle.route.scan{scan_label}:"));
        let current = self.temp();
        let present = self.temp();
        self.line(&format!("  %{current} = load ptr, ptr %{cursor}"));
        self.line(&format!("  %{present} = icmp ne ptr %{current}, null"));
        self.line(&format!(
            "  br i1 %{present}, label %handle.route.inspect{inspect_label}, label %{invalid_target}"
        ));
        self.line(&format!("handle.route.inspect{inspect_label}:"));
        let delimiter_address = self.temp();
        let delimiter = self.temp();
        let has_delimiter = self.temp();
        self.line(&format!(
            "  %{delimiter_address} = getelementptr inbounds %g1.effect_frame, ptr %{current}, i32 0, i32 5"
        ));
        self.line(&format!(
            "  %{delimiter} = load ptr, ptr %{delimiter_address}"
        ));
        self.line(&format!(
            "  %{has_delimiter} = icmp ne ptr %{delimiter}, null"
        ));
        self.line(&format!(
            "  br i1 %{has_delimiter}, label %handle.route.activation{activation_label}, label %handle.route.advance{advance_label}"
        ));
        self.line(&format!("handle.route.activation{activation_label}:"));
        let handler_address = self.temp();
        let handler = self.temp();
        let definition_address = self.temp();
        let handler_def = self.temp();
        self.line(&format!(
            "  %{handler_address} = getelementptr inbounds %g1.effect_guard, ptr %{delimiter}, i32 0, i32 1"
        ));
        self.line(&format!("  %{handler} = load ptr, ptr %{handler_address}"));
        self.line(&format!(
            "  %{definition_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{handler_def} = load i32, ptr %{definition_address}"
        ));

        let checks = definitions
            .iter()
            .flat_map(|(_, definition, _, _)| definition.clauses.iter())
            .count();
        if checks == 0 {
            self.line(&format!("  br label %handle.route.advance{advance_label}"));
        } else {
            let check_labels = (0..checks).map(|_| self.temp()).collect::<Vec<_>>();
            let mut position = 0usize;
            for (definition_index, (described_def, definition, _, _)) in
                definitions.iter().enumerate()
            {
                for (clause_index, clause) in definition.clauses.iter().enumerate() {
                    if position != 0 {
                        self.line(&format!("handle.route.check{}:", check_labels[position]));
                    }
                    let def_matches = self.temp();
                    let protocol_matches = self.temp();
                    let operation_matches = self.temp();
                    let operation_match = self.temp();
                    let matches = self.temp();
                    self.line(&format!(
                        "  %{def_matches} = icmp eq i32 %{handler_def}, {described_def}"
                    ));
                    self.line(&format!(
                        "  %{protocol_matches} = icmp eq i32 {protocol}, {}",
                        clause.protocol
                    ));
                    self.line(&format!(
                        "  %{operation_matches} = icmp eq i32 {operation}, {}",
                        clause.operation
                    ));
                    self.line(&format!(
                        "  %{operation_match} = and i1 %{protocol_matches}, %{operation_matches}"
                    ));
                    self.line(&format!(
                        "  %{matches} = and i1 %{def_matches}, %{operation_match}"
                    ));
                    let otherwise = if position + 1 == checks {
                        format!("handle.route.advance{advance_label}")
                    } else {
                        format!("handle.route.check{}", check_labels[position + 1])
                    };
                    self.line(&format!(
                        "  br i1 %{matches}, label %handle.route.clause{}, label %{otherwise}",
                        clause_labels[definition_index][clause_index]
                    ));
                    position += 1;
                }
            }
        }
        self.line(&format!("handle.route.advance{advance_label}:"));
        let previous_address = self.temp();
        let previous = self.temp();
        self.line(&format!(
            "  %{previous_address} = getelementptr inbounds %g1.effect_frame, ptr %{current}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{previous} = load ptr, ptr %{previous_address}"
        ));
        self.line(&format!("  store ptr %{previous}, ptr %{cursor}"));
        self.line(&format!("  br label %handle.route.scan{scan_label}"));

        for (definition_index, (described_def, definition, _, clause_types)) in
            definitions.iter().enumerate()
        {
            for (clause_index, (clause, clause_type)) in
                definition.clauses.iter().zip(clause_types).enumerate()
            {
                self.line(&format!(
                    "handle.route.clause{}:",
                    clause_labels[definition_index][clause_index]
                ));
                let previous_address = self.temp();
                let parent = self.temp();
                let return_address = self.temp();
                let return_slot = self.temp();
                let return_init_address = self.temp();
                let return_init = self.temp();
                for (field, address, value) in [
                    (0, previous_address, parent),
                    (3, return_address, return_slot),
                    (7, return_init_address, return_init),
                ] {
                    self.line(&format!(
                        "  %{address} = getelementptr inbounds %g1.effect_frame, ptr %{current}, i32 0, i32 {field}"
                    ));
                    self.line(&format!("  %{value} = load ptr, ptr %{address}"));
                }
                let clauses_address = self.temp();
                let clauses = self.temp();
                let slot = self.temp();
                let callable = self.temp();
                let usize_ty = format!("i{}", self.pointer_width());
                self.line(&format!(
                    "  %{clauses_address} = getelementptr inbounds %g1.handler, ptr %{handler}, i32 0, i32 3"
                ));
                self.line(&format!("  %{clauses} = load ptr, ptr %{clauses_address}"));
                self.line(&format!(
                    "  %{slot} = getelementptr inbounds ptr, ptr %{clauses}, {usize_ty} {clause_index}"
                ));
                self.line(&format!("  %{callable} = load ptr, ptr %{slot}"));
                let operation_descriptor = self
                    .phases
                    .artifact
                    .protocols
                    .get(clause.protocol as usize)
                    .and_then(|protocol| protocol.operations.get(clause.operation as usize))
                    .cloned()
                    .ok_or_else(|| vec![unsupported(function, "handler operation is missing")])?;
                let argument_types = operation_descriptor.payload_signature.params;
                let payload_ty = format!(
                    "{{ {} }}",
                    argument_types
                        .iter()
                        .map(|ty| self.llvm_type(*ty))
                        .collect::<Result<Vec<_>, _>>()?
                        .join(", ")
                );
                let mut arguments = Vec::with_capacity(
                    argument_types.len() + usize::from(clause.resumption_type.is_some()),
                );
                for (field, ty) in argument_types.iter().enumerate() {
                    let llvm_ty = self.llvm_type(*ty)?;
                    let address = self.temp();
                    let value = self.temp();
                    self.line(&format!(
                        "  %{address} = getelementptr inbounds {payload_ty}, ptr {payload}, i32 0, i32 {field}"
                    ));
                    self.line(&format!("  %{value} = load {llvm_ty}, ptr %{address}"));
                    arguments.push((*ty, format!("%{value}")));
                }
                let Type::Callable { .. } = self.runtime_type(*clause_type)? else {
                    return Err(vec![unsupported(
                        function,
                        "handler clause has a non-callable runtime type",
                    )]);
                };
                let routed_effect_framed: String;
                if let Some(resumption_type) = clause.resumption_type {
                    self.line(&format!("  store ptr null, ptr %{previous_address}"));
                    let resumption_size = self.emit_array_element_size("%g1.resumption");
                    let resumption = self.temp();
                    self.line(&format!(
                        "  %{resumption} = call ptr @malloc({usize_ty} {resumption_size})"
                    ));
                    let failed = self.temp();
                    self.line(&format!("  %{failed} = icmp eq ptr %{resumption}, null"));
                    self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
                    for (field, value) in [
                        (0, suspended.clone()),
                        (1, format!("%{current}")),
                        (2, resume_slot.clone()),
                        (3, resume_init.clone()),
                        (4, format!("%{handler}")),
                    ] {
                        let address = self.temp();
                        self.line(&format!(
                            "  %{address} = getelementptr inbounds %g1.resumption, ptr %{resumption}, i32 0, i32 {field}"
                        ));
                        self.line(&format!("  store ptr {value}, ptr %{address}"));
                    }
                    let references_address = self.temp();
                    self.line(&format!(
                        "  %{references_address} = getelementptr inbounds %g1.resumption, ptr %{resumption}, i32 0, i32 5"
                    ));
                    self.line(&format!("  store i64 1, ptr %{references_address}"));
                    let current_preserve = self.load_effect_runtime_field(runtime, 8, "i1");
                    let preserve_address = self.temp();
                    self.line(&format!(
                        "  %{preserve_address} = getelementptr inbounds %g1.resumption, ptr %{resumption}, i32 0, i32 6"
                    ));
                    self.line(&format!(
                        "  store i1 {current_preserve}, ptr %{preserve_address}"
                    ));
                    self.emit_retain_handler(&format!("%{handler}"));
                    arguments.push((resumption_type, format!("%{resumption}")));
                    self.emit_effect_runtime_store_for(runtime, 5, "ptr", "null");
                    let effect_framed_slot = self.temp();
                    let starter_address = self.temp();
                    let starter = self.temp();
                    let direct_label = self.temp();
                    let framed_label = self.temp();
                    let routed_label = self.temp();
                    self.line(&format!("  %{effect_framed_slot} = alloca i1"));
                    self.line(&format!(
                        "  %{starter_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 3"
                    ));
                    self.line(&format!("  %{starter} = load ptr, ptr %{starter_address}"));
                    let has_starter = self.temp();
                    self.line(&format!("  %{has_starter} = icmp ne ptr %{starter}, null"));
                    self.line(&format!(
                        "  br i1 %{has_starter}, label %handle.route.resumption.framed{framed_label}, label %handle.route.resumption.direct{direct_label}"
                    ));
                    self.line(&format!("handle.route.resumption.direct{direct_label}:"));
                    let returned = self.emit_call_owned_callable_value(
                        function,
                        *clause_type,
                        &format!("%{callable}"),
                        &arguments,
                        false,
                    )?;
                    self.emit_store_routed_handler_result(
                        function,
                        definition.result_type,
                        returned.as_deref(),
                        &format!("%{return_slot}"),
                        &format!("%{return_init}"),
                    )?;
                    self.line(&format!("  store i1 false, ptr %{effect_framed_slot}"));
                    self.line(&format!(
                        "  br label %handle.route.resumption.routed{routed_label}"
                    ));
                    self.line(&format!("handle.route.resumption.framed{framed_label}:"));
                    {
                        let guards_slot = self.temp();
                        let has_parent = self.temp();
                        let load_guards_label = self.temp();
                        let guards_ready_label = self.temp();
                        self.line(&format!("  %{guards_slot} = alloca ptr"));
                        self.line(&format!("  store ptr null, ptr %{guards_slot}"));
                        self.line(&format!("  %{has_parent} = icmp ne ptr %{parent}, null"));
                        self.line(&format!(
                            "  br i1 %{has_parent}, label %handle.route.resumption.guards{load_guards_label}, label %handle.route.resumption.guards.ready{guards_ready_label}"
                        ));
                        self.line(&format!(
                            "handle.route.resumption.guards{load_guards_label}:"
                        ));
                        let parent_guards_address = self.temp();
                        let parent_guards = self.temp();
                        self.line(&format!(
                            "  %{parent_guards_address} = getelementptr inbounds %g1.effect_frame, ptr %{parent}, i32 0, i32 6"
                        ));
                        self.line(&format!(
                            "  %{parent_guards} = load ptr, ptr %{parent_guards_address}"
                        ));
                        self.line(&format!(
                            "  call void @g1_effect_guard_retain(ptr %{parent_guards})"
                        ));
                        self.line(&format!("  store ptr %{parent_guards}, ptr %{guards_slot}"));
                        self.line(&format!(
                            "  br label %handle.route.resumption.guards.ready{guards_ready_label}"
                        ));
                        self.line(&format!(
                            "handle.route.resumption.guards.ready{guards_ready_label}:"
                        ));
                        let outer_guards = self.temp();
                        self.line(&format!("  %{outer_guards} = load ptr, ptr %{guards_slot}"));
                        let suffix = format!(
                            ", {}",
                            arguments
                                .iter()
                                .map(|(ty, value)| {
                                    self.llvm_type(*ty).map(|ty| format!("{ty} {value}"))
                                })
                                .collect::<Result<Vec<_>, _>>()?
                                .join(", ")
                        );
                        let clause_frame = self.temp();
                        self.line(&format!(
                            "  %{clause_frame} = call ptr %{starter}(ptr %{callable}, i1 false, ptr %{parent}, ptr %{return_slot}, ptr %{return_init}, ptr null, ptr %{outer_guards}{suffix})"
                        ));
                        self.emit_copy_runtime_preserve_to_frame(
                            runtime,
                            &format!("%{clause_frame}"),
                        );
                        self.emit_effect_runtime_store_for(
                            runtime,
                            0,
                            "ptr",
                            &format!("%{clause_frame}"),
                        );
                        self.line(&format!("  store i1 true, ptr %{effect_framed_slot}"));
                        self.line(&format!(
                            "  br label %handle.route.resumption.routed{routed_label}"
                        ));
                    }
                    self.line(&format!("handle.route.resumption.routed{routed_label}:"));
                    let effect_framed = self.temp();
                    self.line(&format!(
                        "  %{effect_framed} = load i1, ptr %{effect_framed_slot}"
                    ));
                    routed_effect_framed = format!("%{effect_framed}");
                } else {
                    if let Some(condition) = match &mode {
                        EffectRoutingMode::ReplayConditional(_) | EffectRoutingMode::Initial => {
                            terminal_preserve.as_ref()
                        }
                        EffectRoutingMode::ReplayBorrowed => None,
                    } {
                        let preserve_label = self.temp();
                        let consume_label = self.temp();
                        let ready_label = self.temp();
                        self.line(&format!(
                            "  br i1 {condition}, label %handle.route.preserve{preserve_label}, label %handle.route.consume{consume_label}"
                        ));
                        self.line(&format!("handle.route.preserve{preserve_label}:"));
                        self.emit_retain(*clause_type, &format!("%{callable}"), function)?;
                        self.line(&format!(
                            "  br label %handle.route.callable.ready{ready_label}"
                        ));
                        self.line(&format!("handle.route.consume{consume_label}:"));
                        self.line(&format!("  store ptr null, ptr %{slot}"));
                        self.line(&format!(
                            "  br label %handle.route.callable.ready{ready_label}"
                        ));
                        self.line(&format!("handle.route.callable.ready{ready_label}:"));
                    } else if mode.preserves_clauses() {
                        self.emit_retain(*clause_type, &format!("%{callable}"), function)?;
                    } else {
                        self.line(&format!("  store ptr null, ptr %{slot}"));
                    }
                    let effect_framed_slot = self.temp();
                    let starter_address = self.temp();
                    let starter = self.temp();
                    let direct_label = self.temp();
                    let framed_label = self.temp();
                    let routed_label = self.temp();
                    self.line(&format!("  %{effect_framed_slot} = alloca i1"));
                    self.line(&format!(
                        "  %{starter_address} = getelementptr inbounds %g1.callable, ptr %{callable}, i32 0, i32 3"
                    ));
                    self.line(&format!("  %{starter} = load ptr, ptr %{starter_address}"));
                    let has_starter = self.temp();
                    self.line(&format!("  %{has_starter} = icmp ne ptr %{starter}, null"));
                    self.line(&format!(
                        "  br i1 %{has_starter}, label %handle.route.framed{framed_label}, label %handle.route.direct{direct_label}"
                    ));
                    self.line(&format!("handle.route.direct{direct_label}:"));
                    self.line(&format!("  store ptr null, ptr %{previous_address}"));
                    let returned = self.emit_call_owned_callable_value(
                        function,
                        *clause_type,
                        &format!("%{callable}"),
                        &arguments,
                        true,
                    )?;
                    self.emit_drop_effect_frame_chain(&suspended);
                    self.emit_effect_runtime_store_for(runtime, 5, "ptr", "null");
                    self.emit_store_routed_handler_result(
                        function,
                        definition.result_type,
                        returned.as_deref(),
                        &format!("%{return_slot}"),
                        &format!("%{return_init}"),
                    )?;
                    self.line(&format!("  store i1 false, ptr %{effect_framed_slot}"));
                    self.line(&format!("  br label %handle.route.routed{routed_label}"));
                    self.line(&format!("handle.route.framed{framed_label}:"));
                    {
                        let guards_slot = self.temp();
                        let has_parent = self.temp();
                        let load_guards_label = self.temp();
                        let guards_ready_label = self.temp();
                        self.line(&format!("  %{guards_slot} = alloca ptr"));
                        self.line(&format!("  store ptr null, ptr %{guards_slot}"));
                        self.line(&format!("  %{has_parent} = icmp ne ptr %{parent}, null"));
                        self.line(&format!(
                            "  br i1 %{has_parent}, label %handle.route.guards{load_guards_label}, label %handle.route.guards.ready{guards_ready_label}"
                        ));
                        self.line(&format!("handle.route.guards{load_guards_label}:"));
                        let parent_guards_address = self.temp();
                        let parent_guards = self.temp();
                        self.line(&format!(
                            "  %{parent_guards_address} = getelementptr inbounds %g1.effect_frame, ptr %{parent}, i32 0, i32 6"
                        ));
                        self.line(&format!(
                            "  %{parent_guards} = load ptr, ptr %{parent_guards_address}"
                        ));
                        self.line(&format!(
                            "  call void @g1_effect_guard_retain(ptr %{parent_guards})"
                        ));
                        self.line(&format!("  store ptr %{parent_guards}, ptr %{guards_slot}"));
                        self.line(&format!(
                            "  br label %handle.route.guards.ready{guards_ready_label}"
                        ));
                        self.line(&format!("handle.route.guards.ready{guards_ready_label}:"));
                        let outer_guards = self.temp();
                        self.line(&format!("  %{outer_guards} = load ptr, ptr %{guards_slot}"));
                        self.line(&format!("  store ptr null, ptr %{previous_address}"));
                        let clause_guards = self.emit_allocate_effect_frame_chain_guard(
                            &suspended,
                            &format!("%{outer_guards}"),
                        );
                        self.emit_effect_runtime_store_for(runtime, 5, "ptr", "null");
                        let suffix = if arguments.is_empty() {
                            String::new()
                        } else {
                            format!(
                                ", {}",
                                arguments
                                    .iter()
                                    .map(|(ty, value)| {
                                        self.llvm_type(*ty).map(|ty| format!("{ty} {value}"))
                                    })
                                    .collect::<Result<Vec<_>, _>>()?
                                    .join(", ")
                            )
                        };
                        let clause_frame = self.temp();
                        self.line(&format!(
                            "  %{clause_frame} = call ptr %{starter}(ptr %{callable}, i1 true, ptr %{parent}, ptr %{return_slot}, ptr %{return_init}, ptr null, ptr {clause_guards}{suffix})"
                        ));
                        self.emit_copy_runtime_preserve_to_frame(
                            runtime,
                            &format!("%{clause_frame}"),
                        );
                        self.emit_effect_runtime_store_for(
                            runtime,
                            0,
                            "ptr",
                            &format!("%{clause_frame}"),
                        );
                        self.line(&format!("  store i1 true, ptr %{effect_framed_slot}"));
                        self.line(&format!("  br label %handle.route.routed{routed_label}"));
                    }
                    self.line(&format!("handle.route.routed{routed_label}:"));
                    let effect_framed = self.temp();
                    self.line(&format!(
                        "  %{effect_framed} = load i1, ptr %{effect_framed_slot}"
                    ));
                    routed_effect_framed = format!("%{effect_framed}");
                }
                self.line(&format!("  call void @free(ptr {payload})"));
                let direct_result_label = self.temp();
                let framed_result_label = self.temp();
                self.line(&format!(
                    "  br i1 {routed_effect_framed}, label %handle.route.result.framed{framed_result_label}, label %handle.route.result.direct{direct_result_label}"
                ));
                self.line(&format!("handle.route.result.direct{direct_result_label}:"));
                self.emit_effect_runtime_store_for(runtime, 0, "ptr", &format!("%{parent}"));
                let has_parent = self.temp();
                let continue_label = self.temp();
                let finish_label = self.temp();
                self.line(&format!("  %{has_parent} = icmp ne ptr %{parent}, null"));
                self.line(&format!(
                    "  br i1 %{has_parent}, label %handle.route.continue{continue_label}, label %handle.route.finish{finish_label}"
                ));
                self.line(&format!("handle.route.continue{continue_label}:"));
                self.line(&format!("  br label %{loop_target}"));
                self.line(&format!("handle.route.finish{finish_label}:"));
                self.emit_effect_runtime_store_for(runtime, 1, "i32", "0");
                self.line(&format!("  br label %{loop_target}"));
                self.line(&format!("handle.route.result.framed{framed_result_label}:"));
                self.line(&format!("  br label %{loop_target}"));
                let _ = described_def;
            }
        }
        Ok(())
    }

    fn emit_store_routed_handler_result(
        &mut self,
        function: &mir::Function,
        result_type: TypeId,
        returned: Option<&str>,
        return_slot: &str,
        return_init: &str,
    ) -> Result<(), Vec<Diagnostic>> {
        let result_ty = self.llvm_return_type(result_type)?;
        if let Some(returned) = returned {
            self.line(&format!(
                "  store {result_ty} {returned}, ptr {return_slot}"
            ));
        } else if result_ty == "void" {
            self.line(&format!("  store i8 0, ptr {return_slot}"));
        } else {
            return Err(vec![unsupported(
                function,
                "handler clause did not return its declared result",
            )]);
        }
        let has_init = self.temp();
        let mark_label = self.temp();
        let marked_label = self.temp();
        self.line(&format!("  %{has_init} = icmp ne ptr {return_init}, null"));
        self.line(&format!(
            "  br i1 %{has_init}, label %handle.route.mark{mark_label}, label %handle.route.marked{marked_label}"
        ));
        self.line(&format!("handle.route.mark{mark_label}:"));
        self.line(&format!("  store i8 1, ptr {return_init}"));
        self.line(&format!("  br label %handle.route.marked{marked_label}"));
        self.line(&format!("handle.route.marked{marked_label}:"));
        Ok(())
    }

    fn emit_effect_runtime_store_for(&mut self, runtime: &str, field: u32, ty: &str, value: &str) {
        let address = self.temp();
        self.line(&format!(
            "  %{address} = getelementptr inbounds %g1.effect_runtime, ptr {runtime}, i32 0, i32 {field}"
        ));
        self.line(&format!("  store {ty} {value}, ptr %{address}"));
    }

    fn emit_copy_runtime_preserve_to_frame(&mut self, runtime: &str, frame: &str) {
        let preserve = self.load_effect_runtime_field(runtime, 8, "i1");
        let address = self.temp();
        self.line(&format!(
            "  %{address} = getelementptr inbounds %g1.effect_frame, ptr {frame}, i32 0, i32 10"
        ));
        self.line(&format!("  store i1 {preserve}, ptr %{address}"));
    }

    fn emit_drop_effect_frame(&mut self, frame: &str) {
        let drop_address = self.temp();
        let drop = self.temp();
        self.line(&format!(
            "  %{drop_address} = getelementptr inbounds %g1.effect_frame, ptr {frame}, i32 0, i32 2"
        ));
        self.line(&format!("  %{drop} = load ptr, ptr %{drop_address}"));
        self.line(&format!("  call void %{drop}(ptr {frame})"));
    }

    fn emit_drop_optional_effect_frame(&mut self, frame: &str) {
        let present = self.temp();
        let drop_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  %{present} = icmp ne ptr {frame}, null"));
        self.line(&format!(
            "  br i1 %{present}, label %frame.optional.drop{drop_label}, label %frame.optional.done{done_label}"
        ));
        self.line(&format!("frame.optional.drop{drop_label}:"));
        self.emit_drop_effect_frame(frame);
        self.line(&format!("  br label %frame.optional.done{done_label}"));
        self.line(&format!("frame.optional.done{done_label}:"));
    }

    fn emit_drop_effect_frame_chain(&mut self, top: &str) {
        let current_slot = self.temp();
        let loop_label = self.temp();
        let drop_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  %{current_slot} = alloca ptr"));
        self.line(&format!("  store ptr {top}, ptr %{current_slot}"));
        self.line(&format!("  br label %frame.chain.loop{loop_label}"));
        self.line(&format!("frame.chain.loop{loop_label}:"));
        let current = self.temp();
        let present = self.temp();
        self.line(&format!("  %{current} = load ptr, ptr %{current_slot}"));
        self.line(&format!("  %{present} = icmp ne ptr %{current}, null"));
        self.line(&format!(
            "  br i1 %{present}, label %frame.chain.drop{drop_label}, label %frame.chain.done{done_label}"
        ));
        self.line(&format!("frame.chain.drop{drop_label}:"));
        let previous_address = self.temp();
        let previous = self.temp();
        self.line(&format!(
            "  %{previous_address} = getelementptr inbounds %g1.effect_frame, ptr %{current}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{previous} = load ptr, ptr %{previous_address}"
        ));
        self.emit_drop_effect_frame(&format!("%{current}"));
        self.line(&format!("  store ptr %{previous}, ptr %{current_slot}"));
        self.line(&format!("  br label %frame.chain.loop{loop_label}"));
        self.line(&format!("frame.chain.done{done_label}:"));
    }

    fn resumption_handler_capture_type(
        &self,
        function: &mir::Function,
        resumption_type: TypeId,
    ) -> Result<TypeId, Vec<Diagnostic>> {
        let matching_handlers = self
            .phases
            .artifact
            .handler_defs
            .iter()
            .enumerate()
            .filter(|(_, definition)| {
                definition
                    .clauses
                    .iter()
                    .any(|clause| clause.resumption_type == Some(resumption_type))
            })
            .map(|(index, _)| index as u32)
            .collect::<Vec<_>>();
        let [handler_def] = matching_handlers.as_slice() else {
            return Err(vec![unsupported(
                function,
                "resumption does not identify exactly one handler",
            )]);
        };
        self.phases
            .artifact
            .types
            .iter()
            .find_map(|ty| match ty.representation() {
                Type::Handler {
                    handler_def: described,
                    capture_type,
                    ..
                } if *described == *handler_def => Some(*capture_type),
                _ => None,
            })
            .ok_or_else(|| vec![unsupported(function, "resumption handler type is missing")])
    }

    fn resumption_handler_runtime_type(
        &self,
        function: &mir::Function,
        resumption_type: TypeId,
    ) -> Result<TypeId, Vec<Diagnostic>> {
        let matching_handlers = self
            .phases
            .artifact
            .handler_defs
            .iter()
            .enumerate()
            .filter(|(_, definition)| {
                definition
                    .clauses
                    .iter()
                    .any(|clause| clause.resumption_type == Some(resumption_type))
            })
            .map(|(index, _)| index as u32)
            .collect::<Vec<_>>();
        let [handler_def] = matching_handlers.as_slice() else {
            return Err(vec![unsupported(
                function,
                "resumption does not identify exactly one handler",
            )]);
        };
        self.handler_runtime_type(*handler_def)
    }

    fn emit_release_resumption(
        &mut self,
        resumption: &str,
        resumption_type: TypeId,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let references_address = self.temp();
        let references = self.temp();
        let valid = self.temp();
        let last = self.temp();
        let destroy_label = self.temp();
        let decrement_label = self.temp();
        let done_label = self.temp();
        self.line(&format!(
            "  %{references_address} = getelementptr inbounds %g1.resumption, ptr {resumption}, i32 0, i32 5"
        ));
        self.line(&format!(
            "  %{references} = load i64, ptr %{references_address}"
        ));
        self.line(&format!("  %{valid} = icmp ne i64 %{references}, 0"));
        let valid_label = self.temp();
        let invalid_label = self.temp();
        self.line(&format!(
            "  br i1 %{valid}, label %resumption.release.valid{valid_label}, label %resumption.release.invalid{invalid_label}"
        ));
        self.line(&format!("resumption.release.invalid{invalid_label}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        self.line(&format!("resumption.release.valid{valid_label}:"));
        self.line(&format!("  %{last} = icmp eq i64 %{references}, 1"));
        self.line(&format!(
            "  br i1 %{last}, label %resumption.release.destroy{destroy_label}, label %resumption.release.decrement{decrement_label}"
        ));
        self.line(&format!("resumption.release.decrement{decrement_label}:"));
        let next = self.temp();
        self.line(&format!("  %{next} = sub i64 %{references}, 1"));
        self.line(&format!("  store i64 %{next}, ptr %{references_address}"));
        self.line(&format!("  br label %resumption.release.done{done_label}"));
        self.line(&format!("resumption.release.destroy{destroy_label}:"));
        let top_address = self.temp();
        let top = self.temp();
        let handler_address = self.temp();
        let handler = self.temp();
        self.line(&format!(
            "  %{top_address} = getelementptr inbounds %g1.resumption, ptr {resumption}, i32 0, i32 0"
        ));
        self.line(&format!("  %{top} = load ptr, ptr %{top_address}"));
        self.line(&format!(
            "  %{handler_address} = getelementptr inbounds %g1.resumption, ptr {resumption}, i32 0, i32 4"
        ));
        self.line(&format!("  %{handler} = load ptr, ptr %{handler_address}"));
        self.emit_drop_effect_frame_chain(&format!("%{top}"));
        let clause_tuple = self.resumption_handler_capture_type(function, resumption_type)?;
        self.emit_destroy_handler(&format!("%{handler}"), clause_tuple, function)?;
        self.line(&format!("  call void @free(ptr {resumption})"));
        self.line(&format!("  br label %resumption.release.done{done_label}"));
        self.line(&format!("resumption.release.done{done_label}:"));
        Ok(())
    }

    fn load_effect_runtime_field(&mut self, runtime: &str, field: u32, ty: &str) -> String {
        let address = self.temp();
        let value = self.temp();
        self.line(&format!(
            "  %{address} = getelementptr inbounds %g1.effect_runtime, ptr {runtime}, i32 0, i32 {field}"
        ));
        self.line(&format!("  %{value} = load {ty}, ptr %{address}"));
        format!("%{value}")
    }

    fn emit_call_owned_callable_value(
        &mut self,
        function: &mir::Function,
        callable_type: TypeId,
        callable: &str,
        arguments: &[(TypeId, String)],
        consume_callable: bool,
    ) -> Result<Option<String>, Vec<Diagnostic>> {
        let Type::Callable {
            signature,
            capture_type,
            receiver_mode,
            ..
        } = self.runtime_type(callable_type)?.clone()
        else {
            return Err(vec![unsupported(
                function,
                "handler clause has a non-callable runtime type",
            )]);
        };
        if signature.params.as_slice() != arguments.iter().map(|(ty, _)| *ty).collect::<Vec<_>>()
            || receiver_mode > 2
            || !consume_callable && receiver_mode == 2
        {
            return Err(vec![unsupported(
                function,
                "handler clause must have an exact callable signature",
            )]);
        }
        let function_address = self.temp();
        let target = self.temp();
        let capture_address = self.temp();
        let capture_handle = self.temp();
        let data_address = self.temp();
        let data = self.temp();
        self.line(&format!(
            "  %{function_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 1"
        ));
        self.line(&format!("  %{target} = load ptr, ptr %{function_address}"));
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 2"
        ));
        self.line(&format!(
            "  %{capture_handle} = load ptr, ptr %{capture_address}"
        ));
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.capture, ptr %{capture_handle}, i32 0, i32 1"
        ));
        self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
        let mut call_arguments = if receiver_mode == 2 {
            let capture_ty = self.llvm_type(capture_type)?;
            let receiver = self.temp();
            self.line(&format!("  %{receiver} = load {capture_ty}, ptr %{data}"));
            let count_address = self.temp();
            let count = self.temp();
            let unique = self.temp();
            let move_label = self.temp();
            let copy_label = self.temp();
            let ready_label = self.temp();
            self.line(&format!(
                "  %{count_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 0"
            ));
            self.line(&format!("  %{count} = load i64, ptr %{count_address}"));
            self.line(&format!("  %{unique} = icmp eq i64 %{count}, 1"));
            self.line(&format!(
                "  br i1 %{unique}, label %callable.receiver.move{move_label}, label %callable.receiver.copy{copy_label}"
            ));
            self.line(&format!("callable.receiver.copy{copy_label}:"));
            self.emit_retain(capture_type, &format!("%{receiver}"), function)?;
            self.emit_destroy_callable(callable, capture_type, function)?;
            self.line(&format!("  br label %callable.receiver.ready{ready_label}"));
            self.line(&format!("callable.receiver.move{move_label}:"));
            self.line(&format!("  store ptr null, ptr %{data_address}"));
            self.line(&format!("  call void @free(ptr %{data})"));
            self.emit_release_capture(&format!("%{capture_handle}"), capture_type, function)?;
            self.line(&format!("  call void @free(ptr {callable})"));
            self.line(&format!("  br label %callable.receiver.ready{ready_label}"));
            self.line(&format!("callable.receiver.ready{ready_label}:"));
            vec![format!("{capture_ty} %{receiver}")]
        } else {
            vec![format!("ptr %{data}")]
        };
        call_arguments.extend(
            arguments
                .iter()
                .map(|(ty, value)| self.llvm_type(*ty).map(|ty| format!("{ty} {value}")))
                .collect::<Result<Vec<_>, _>>()?,
        );
        let result_ty = self.llvm_return_type(signature.result)?;
        let returned = if result_ty == "void" {
            self.line(&format!(
                "  call void %{target}({})",
                call_arguments.join(", ")
            ));
            None
        } else {
            let returned = self.temp();
            self.line(&format!(
                "  %{returned} = call {result_ty} %{target}({})",
                call_arguments.join(", ")
            ));
            Some(format!("%{returned}"))
        };
        if consume_callable && receiver_mode != 2 {
            self.emit_destroy_callable(callable, capture_type, function)?;
        }
        Ok(returned)
    }

    fn emit_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callee_index: usize,
        args: &[mir::Operand],
        normal: &mir::Edge,
        tail: bool,
    ) -> Result<(), Vec<Diagnostic>> {
        let callee = self
            .phases
            .mir
            .functions
            .get(callee_index)
            .ok_or_else(|| vec![unsupported(caller, "call to a missing function")])?;
        let arguments = args
            .iter()
            .map(|operand| {
                let ty = self.register_type(caller, operand.register)?;
                let value = self.load_operand(caller, operand)?;
                if operand.mode == mir::UseMode::Copy {
                    let runtime_ty = self.register_runtime_type(caller, operand.register)?;
                    self.emit_retain(runtime_ty, &value, caller)?;
                }
                Ok(format!("{ty} {value}"))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?
            .join(", ");
        let result_ty = self.llvm_return_type(callee.result)?;
        let call = if result_ty == "void" {
            self.line(&format!(
                "  {}call void @g1_f{callee_index}({arguments})",
                if tail { "tail " } else { "" }
            ));
            None
        } else {
            let temporary = self.temp();
            self.line(&format!(
                "  %{temporary} = {}call {result_ty} @g1_f{callee_index}({arguments})",
                if tail { "tail " } else { "" }
            ));
            Some(temporary)
        };
        if let (Some(dst), Some(value)) = (result, call) {
            self.line(&format!("  store {result_ty} %{value}, ptr %r{dst}"));
        }
        self.emit_edge_with_preassigned(caller, normal, result.into_iter().collect())
    }

    fn emit_call_with_receiver(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callee_index: usize,
        receiver: &mir::Operand,
        args: &[mir::Operand],
        normal: &mir::Edge,
        tail: bool,
    ) -> Result<(), Vec<Diagnostic>> {
        let callee = self
            .phases
            .mir
            .functions
            .get(callee_index)
            .ok_or_else(|| vec![unsupported(caller, "call to a missing receiver function")])?;
        if callee.receiver_mode != Some(0) {
            return Err(vec![unsupported(
                caller,
                "known-receiver calls whose target does not use a shared receiver",
            )]);
        }
        let receiver_ty = self.register_type(caller, receiver.register)?;
        let receiver_value = self.load_operand(caller, receiver)?;
        let mut arguments = vec![format!("{receiver_ty} {receiver_value}")];
        for operand in args {
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                let runtime_ty = self.register_runtime_type(caller, operand.register)?;
                self.emit_retain(runtime_ty, &value, caller)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let arguments = arguments.join(", ");
        let result_ty = self.llvm_return_type(callee.result)?;
        let call = if result_ty == "void" {
            self.line(&format!(
                "  {}call void @g1_f{callee_index}({arguments})",
                if tail { "tail " } else { "" }
            ));
            None
        } else {
            let temporary = self.temp();
            self.line(&format!(
                "  %{temporary} = {}call {result_ty} @g1_f{callee_index}({arguments})",
                if tail { "tail " } else { "" }
            ));
            Some(temporary)
        };
        if tail {
            if let Some(value) = call {
                self.line(&format!("  ret {result_ty} %{value}"));
            } else {
                self.line("  ret void");
            }
            return Ok(());
        }
        if let (Some(dst), Some(value)) = (result, call) {
            self.line(&format!("  store {result_ty} %{value}, ptr %r{dst}"));
        }
        self.emit_edge_with_preassigned(caller, normal, result.into_iter().collect())
    }

    fn emit_host_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        import: HostImportRole,
        args: &[mir::Operand],
        normal: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        let returned = self.emit_host_invocation(caller, result, import, args)?;
        if let Some(dst) = result {
            if let Some(value) = returned {
                self.line(&format!("  store ptr %{value}, ptr %r{dst}"));
            } else if matches!(
                self.runtime_type(self.register_runtime_type(caller, dst)?)?,
                Type::Unit
            ) {
                self.line(&format!("  store i8 0, ptr %r{dst}"));
            } else {
                return Err(vec![unsupported(
                    caller,
                    "host call returned no value for a non-Unit result",
                )]);
            }
        }
        self.emit_edge_with_preassigned(caller, normal, result.into_iter().collect())
    }

    fn emit_host_invocation(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        import: HostImportRole,
        args: &[mir::Operand],
    ) -> Result<Option<Temporary>, Vec<Diagnostic>> {
        let expected_args = match import {
            HostImportRole::ProcessArgsGet => Vec::new(),
            HostImportRole::FsRead | HostImportRole::DiagnosticWrite => vec![Type::Text],
            HostImportRole::FsWrite => vec![Type::Text, Type::Bytes],
        };
        if args.len() != expected_args.len() {
            return Err(vec![unsupported(
                caller,
                "host call argument count mismatch",
            )]);
        }
        let mut arguments = Vec::with_capacity(args.len());
        let mut loaded = Vec::with_capacity(args.len());
        for (operand, expected) in args.iter().zip(&expected_args) {
            let runtime_ty = self.register_runtime_type(caller, operand.register)?;
            if self.runtime_type(runtime_ty)? != expected {
                return Err(vec![unsupported(
                    caller,
                    "host call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(runtime_ty, &value, caller)?;
            }
            arguments.push(format!("{ty} {value}"));
            loaded.push((runtime_ty, value));
        }
        let arguments = arguments.join(", ");
        let returned = match import {
            HostImportRole::ProcessArgsGet => {
                let dst = result.ok_or_else(|| {
                    vec![unsupported(
                        caller,
                        "process-args host call without a result",
                    )]
                })?;
                let result_ty = self.register_runtime_type(caller, dst)?;
                let Type::Array { element } = self.runtime_type(result_ty)? else {
                    return Err(vec![unsupported(
                        caller,
                        "process-args host result is not an Array",
                    )]);
                };
                if !matches!(self.runtime_type(*element)?, Type::Text) {
                    return Err(vec![unsupported(
                        caller,
                        "process-args host result is not Array<Text>",
                    )]);
                }
                let value = self.temp();
                self.line(&format!(
                    "  %{value} = call ptr @g1_host_process_args_get()"
                ));
                let failed = self.temp();
                self.line(&format!("  %{failed} = icmp eq ptr %{value}, null"));
                self.emit_host_fault_if(failed, 1);
                Some(value)
            }
            HostImportRole::FsRead => {
                let dst = result.ok_or_else(|| {
                    vec![unsupported(caller, "fs-read host call without a result")]
                })?;
                let result_ty = self.register_runtime_type(caller, dst)?;
                if !matches!(self.runtime_type(result_ty)?, Type::Bytes) {
                    return Err(vec![unsupported(
                        caller,
                        "fs-read host result is not Bytes",
                    )]);
                }
                let value = self.temp();
                self.line(&format!(
                    "  %{value} = call ptr @g1_host_fs_read({arguments})"
                ));
                let failed = self.temp();
                self.line(&format!("  %{failed} = icmp eq ptr %{value}, null"));
                self.emit_host_fault_if(failed, 2);
                Some(value)
            }
            HostImportRole::FsWrite => {
                let status = self.temp();
                self.line(&format!(
                    "  %{status} = call i32 @g1_host_fs_write({arguments})"
                ));
                let failed = self.temp();
                self.line(&format!("  %{failed} = icmp ne i32 %{status}, 0"));
                self.emit_host_fault_if(failed, 3);
                None
            }
            HostImportRole::DiagnosticWrite => {
                let status = self.temp();
                self.line(&format!(
                    "  %{status} = call i32 @g1_host_diagnostic_write({arguments})"
                ));
                let failed = self.temp();
                self.line(&format!("  %{failed} = icmp ne i32 %{status}, 0"));
                self.emit_host_fault_if(failed, 4);
                None
            }
        };
        for (runtime_ty, value) in loaded {
            self.emit_destroy(runtime_ty, &value, caller)?;
        }
        Ok(returned)
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_indirect_call(
        &mut self,
        caller: &mir::Function,
        result: Option<u32>,
        callable_operand: &mir::Operand,
        known_function: Option<u32>,
        requested_mode: u32,
        cleanup_callable: bool,
        args: &[mir::Operand],
        normal: Option<&mir::Edge>,
    ) -> Result<(), Vec<Diagnostic>> {
        let callable_type = self.register_runtime_type(caller, callable_operand.register)?;
        let Type::Callable {
            signature,
            capture_type,
            receiver_mode,
            ..
        } = self.runtime_type(callable_type)?.clone()
        else {
            return Err(vec![unsupported(
                caller,
                "indirect call through a non-callable value",
            )]);
        };
        if requested_mode > 2 || requested_mode < receiver_mode {
            return Err(vec![unsupported(
                caller,
                "indirect call with an incompatible receiver mode",
            )]);
        }
        if signature.params.len() != args.len() {
            return Err(vec![unsupported(
                caller,
                "indirect call argument count mismatch",
            )]);
        }
        if let Some(target) = known_function {
            let target = self
                .phases
                .mir
                .functions
                .get(target as usize)
                .ok_or_else(|| vec![unsupported(caller, "missing known indirect-call target")])?;
            if target.receiver_mode != Some(receiver_mode) {
                return Err(vec![unsupported(
                    caller,
                    "known indirect-call receiver mode mismatch",
                )]);
            }
        }

        let callable = self.load_operand(caller, callable_operand)?;
        let function_address = self.temp();
        self.line(&format!(
            "  %{function_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 1"
        ));
        let target = self.temp();
        self.line(&format!("  %{target} = load ptr, ptr %{function_address}"));
        let capture_address = self.temp();
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 2"
        ));
        let capture_handle = self.temp();
        self.line(&format!(
            "  %{capture_handle} = load ptr, ptr %{capture_address}"
        ));
        let capture_data_address = self.temp();
        self.line(&format!(
            "  %{capture_data_address} = getelementptr inbounds %g1.capture, ptr %{capture_handle}, i32 0, i32 1"
        ));
        let capture = self.temp();
        self.line(&format!(
            "  %{capture} = load ptr, ptr %{capture_data_address}"
        ));

        let mut arguments = Vec::with_capacity(args.len() + 1);
        if receiver_mode == 2 {
            let capture_ty = self.llvm_type(capture_type)?;
            let receiver = self.temp();
            self.line(&format!(
                "  %{receiver} = load {capture_ty}, ptr %{capture}"
            ));
            self.line(&format!("  store ptr null, ptr %{capture_data_address}"));
            self.line(&format!("  call void @free(ptr %{capture})"));
            self.emit_release_capture(&format!("%{capture_handle}"), capture_type, caller)?;
            self.line(&format!("  call void @free(ptr {callable})"));
            arguments.push(format!("{capture_ty} %{receiver}"));
        } else {
            arguments.push(format!("ptr %{capture}"));
        }
        for (operand, expected) in args.iter().zip(&signature.params) {
            let runtime_ty = self.register_runtime_type(caller, operand.register)?;
            if runtime_ty != *expected {
                return Err(vec![unsupported(
                    caller,
                    "indirect call argument type mismatch",
                )]);
            }
            let ty = self.register_type(caller, operand.register)?;
            let value = self.load_operand(caller, operand)?;
            if operand.mode == mir::UseMode::Copy {
                self.emit_retain(runtime_ty, &value, caller)?;
            }
            arguments.push(format!("{ty} {value}"));
        }
        let arguments = arguments.join(", ");
        let result_ty = self.llvm_return_type(signature.result)?;
        let call = if result_ty == "void" {
            self.line(&format!("  call void %{target}({arguments})"));
            None
        } else {
            let value = self.temp();
            self.line(&format!(
                "  %{value} = call {result_ty} %{target}({arguments})"
            ));
            Some(value)
        };
        if receiver_mode != 2 && (requested_mode == 2 || cleanup_callable) {
            self.emit_destroy(callable_type, &callable, caller)?;
        }
        if let Some(normal) = normal {
            if let (Some(dst), Some(value)) = (result, call) {
                self.line(&format!("  store {result_ty} %{value}, ptr %r{dst}"));
            }
            self.emit_edge_with_preassigned(caller, normal, result.into_iter().collect())
        } else {
            if let Some(value) = call {
                self.line(&format!("  ret {result_ty} %{value}"));
            } else {
                self.line("  ret void");
            }
            Ok(())
        }
    }

    fn emit_tail_call(
        &mut self,
        caller: &mir::Function,
        callee: usize,
        args: &[mir::Operand],
    ) -> Result<(), Vec<Diagnostic>> {
        let target = self
            .phases
            .mir
            .functions
            .get(callee)
            .ok_or_else(|| vec![unsupported(caller, "tail call to a missing function")])?;
        let arguments = args
            .iter()
            .map(|operand| {
                let ty = self.register_type(caller, operand.register)?;
                let value = self.load_operand(caller, operand)?;
                if operand.mode == mir::UseMode::Copy {
                    let runtime_ty = self.register_runtime_type(caller, operand.register)?;
                    self.emit_retain(runtime_ty, &value, caller)?;
                }
                Ok(format!("{ty} {value}"))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?
            .join(", ");
        let result = self.llvm_return_type(target.result)?;
        if result == "void" {
            self.line(&format!("  tail call void @g1_f{callee}({arguments})"));
            self.line("  ret void");
        } else {
            let temporary = self.temp();
            self.line(&format!(
                "  %{temporary} = tail call {result} @g1_f{callee}({arguments})"
            ));
            self.line(&format!("  ret {result} %{temporary}"));
        }
        Ok(())
    }

    fn emit_edge(
        &mut self,
        function: &mir::Function,
        edge: &mir::Edge,
    ) -> Result<(), Vec<Diagnostic>> {
        self.emit_edge_with_preassigned(function, edge, BTreeSet::new())
    }

    fn emit_edge_with_preassigned(
        &mut self,
        function: &mir::Function,
        edge: &mir::Edge,
        preassigned: BTreeSet<u32>,
    ) -> Result<(), Vec<Diagnostic>> {
        for register in &preassigned {
            self.emit_set_ordinary_aggregate_fields(function, *register, true)?;
        }
        let target = function
            .blocks
            .iter()
            .find(|block| block.id == edge.target)
            .ok_or_else(|| vec![unsupported(function, "edge to a missing block")])?;
        let parameters = target
            .params
            .iter()
            .filter(|parameter| !preassigned.contains(&parameter.register))
            .collect::<Vec<_>>();
        if parameters.len() != edge.args.len() {
            return Err(vec![unsupported(function, "malformed block argument edge")]);
        }
        let relocations = self.emit_edge_reference_relocations(function, edge, &parameters)?;
        let mut values = edge
            .args
            .iter()
            .map(|operand| {
                let ty = self.register_type(function, operand.register)?;
                let value = self.load_operand(function, operand)?;
                if operand.mode == mir::UseMode::Copy {
                    if self
                        .ordinary_aggregate_field_layout(function, operand.register)?
                        .is_empty()
                    {
                        let runtime_ty = self.register_runtime_type(function, operand.register)?;
                        self.emit_retain(runtime_ty, &value, function)?;
                    } else {
                        self.emit_retain_ordinary_aggregate_register(
                            function,
                            operand.register,
                            &value,
                        )?;
                    }
                }
                let field_flags = self
                    .ordinary_aggregate_field_layout(function, operand.register)?
                    .into_iter()
                    .map(|field| {
                        let flag = self.temp();
                        self.line(&format!(
                            "  %{flag} = load i8, ptr %fieldinit{}.{}",
                            operand.register, field.owned_mask_index
                        ));
                        format!("%{flag}")
                    })
                    .collect::<Vec<_>>();
                Ok((ty, value, operand.register, operand.mode, field_flags))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        for (_, value, source, _, _) in &mut values {
            *value = self.emit_relocated_edge_reference(function, *source, value, &relocations)?;
        }
        let destination_registers = parameters
            .iter()
            .map(|parameter| parameter.register)
            .collect::<BTreeSet<_>>();
        let mut moved_sources = BTreeSet::new();
        for (parameter, (ty, value, source, mode, field_flags)) in
            parameters.into_iter().zip(values)
        {
            self.line(&format!(
                "  store {ty} {value}, ptr %r{}",
                parameter.register
            ));
            let target_fields =
                self.ordinary_aggregate_field_layout(function, parameter.register)?;
            if target_fields.len() != field_flags.len() {
                return Err(vec![unsupported(
                    function,
                    "block argument aggregate field-state layout mismatch",
                )]);
            }
            for (field, flag) in target_fields.iter().zip(&field_flags) {
                self.line(&format!(
                    "  store i8 {flag}, ptr %fieldinit{}.{}",
                    parameter.register, field.owned_mask_index
                ));
            }
            if mode == mir::UseMode::Move {
                moved_sources.insert(source);
            }
        }
        for source in moved_sources {
            if !destination_registers.contains(&source) {
                self.emit_set_ordinary_aggregate_fields(function, source, false)?;
            }
        }
        self.line(&format!("  br label %bb{}", edge.target));
        Ok(())
    }

    fn emit_entry_wrapper(&mut self, reachable: &[usize]) -> Result<(), Vec<Diagnostic>> {
        let entry = reachable
            .iter()
            .copied()
            .find(|index| self.phases.mir.functions[*index].name == "main")
            .unwrap();
        let function = &self.phases.mir.functions[entry];
        if !function.params.is_empty() || function.receiver_mode.is_some() {
            return Err(vec![unsupported(
                function,
                "native entry points with parameters",
            )]);
        }
        let result = self.llvm_return_type(function.result)?;
        if self.host_imports.contains(&HostImportRole::ProcessArgsGet) {
            self.line("define i32 @main(i32 %argc, ptr %argv) {");
            self.line("  call void @g1_host_process_init(i32 %argc, ptr %argv)");
        } else {
            self.line("define i32 @main() {");
        }
        if result == "void" {
            self.line(&format!("  call void @g1_f{entry}()"));
        } else {
            self.line(&format!("  %result = call {result} @g1_f{entry}()"));
        }
        self.line("  ret i32 0");
        self.line("}");
        self.line("");
        Ok(())
    }

    fn register_type(
        &self,
        function: &mir::Function,
        register: u32,
    ) -> Result<String, Vec<Diagnostic>> {
        let ty = function
            .register_types
            .get(register as usize)
            .copied()
            .ok_or_else(|| vec![unsupported(function, "register without a type")])?;
        self.llvm_type(ty)
    }

    fn register_runtime_type(
        &self,
        function: &mir::Function,
        register: u32,
    ) -> Result<TypeId, Vec<Diagnostic>> {
        function
            .register_types
            .get(register as usize)
            .copied()
            .ok_or_else(|| vec![unsupported(function, "register without a runtime type")])
    }

    fn runtime_type(&self, ty: TypeId) -> Result<&Type, Vec<Diagnostic>> {
        self.phases
            .artifact
            .types
            .get(ty as usize)
            .map(Type::representation)
            .ok_or_else(|| vec![backend_error(format!("missing runtime type t{ty}"))])
    }

    fn is_byte_object(&self, ty: TypeId) -> Result<bool, Vec<Diagnostic>> {
        Ok(matches!(self.runtime_type(ty)?, Type::Text | Type::Bytes))
    }

    fn type_contains_byte_object(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<bool, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(false);
        }
        let contains =
            match self.runtime_type(ty)? {
                Type::Text | Type::Bytes => true,
                Type::Tuple { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_byte_object(*field, visiting)
                        .unwrap_or(true)
                }),
                Type::Struct { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_byte_object(field.ty, visiting)
                        .unwrap_or(true)
                }),
                Type::Array { element } => self
                    .type_contains_byte_object(*element, visiting)
                    .unwrap_or(true),
                Type::Callable { capture_type, .. } => self
                    .type_contains_byte_object(*capture_type, visiting)
                    .unwrap_or(true),
                Type::BindingPack { payload_type, .. } => self
                    .type_contains_byte_object(*payload_type, visiting)
                    .unwrap_or(true),
                Type::Enum { variants, .. } => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| {
                        self.type_contains_byte_object(field.ty, visiting)
                            .unwrap_or(true)
                    }),
                _ => false,
            };
        visiting.remove(&ty);
        Ok(contains)
    }

    fn type_contains_array(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<bool, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(false);
        }
        let contains = match self.runtime_type(ty)? {
            Type::Array { .. } => true,
            Type::Tuple { fields, .. } => fields
                .iter()
                .any(|field| self.type_contains_array(*field, visiting).unwrap_or(true)),
            Type::Struct { fields, .. } => fields
                .iter()
                .any(|field| self.type_contains_array(field.ty, visiting).unwrap_or(true)),
            Type::Callable { capture_type, .. } => self
                .type_contains_array(*capture_type, visiting)
                .unwrap_or(true),
            Type::BindingPack { payload_type, .. } => self
                .type_contains_array(*payload_type, visiting)
                .unwrap_or(true),
            Type::Enum { variants, .. } => variants
                .iter()
                .flat_map(|variant| &variant.fields)
                .any(|field| self.type_contains_array(field.ty, visiting).unwrap_or(true)),
            _ => false,
        };
        visiting.remove(&ty);
        Ok(contains)
    }

    fn type_contains_callable(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<bool, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(false);
        }
        let contains =
            match self.runtime_type(ty)? {
                Type::Callable { .. } => true,
                Type::Tuple { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_callable(*field, visiting)
                        .unwrap_or(true)
                }),
                Type::Struct { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_callable(field.ty, visiting)
                        .unwrap_or(true)
                }),
                Type::Array { element } => self
                    .type_contains_callable(*element, visiting)
                    .unwrap_or(true),
                Type::BindingPack { payload_type, .. } => self
                    .type_contains_callable(*payload_type, visiting)
                    .unwrap_or(true),
                Type::Enum { variants, .. } => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| {
                        self.type_contains_callable(field.ty, visiting)
                            .unwrap_or(true)
                    }),
                _ => false,
            };
        visiting.remove(&ty);
        Ok(contains)
    }

    fn type_contains_handler(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<bool, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(false);
        }
        let contains =
            match self.runtime_type(ty)? {
                Type::Handler { .. } => true,
                Type::Array { element } => self
                    .type_contains_handler(*element, visiting)
                    .unwrap_or(true),
                Type::Callable { capture_type, .. } => self
                    .type_contains_handler(*capture_type, visiting)
                    .unwrap_or(true),
                Type::BindingPack { payload_type, .. } => self
                    .type_contains_handler(*payload_type, visiting)
                    .unwrap_or(true),
                Type::Tuple { fields, .. } => fields
                    .iter()
                    .any(|field| self.type_contains_handler(*field, visiting).unwrap_or(true)),
                Type::Struct { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_handler(field.ty, visiting)
                        .unwrap_or(true)
                }),
                Type::Enum { variants, .. } => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| {
                        self.type_contains_handler(field.ty, visiting)
                            .unwrap_or(true)
                    }),
                _ => false,
            };
        visiting.remove(&ty);
        Ok(contains)
    }

    fn type_contains_resumption(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<bool, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Ok(false);
        }
        let contains =
            match self.runtime_type(ty)? {
                Type::Resumption { .. } => true,
                Type::Array { element } => self
                    .type_contains_resumption(*element, visiting)
                    .unwrap_or(true),
                Type::Callable { capture_type, .. } => self
                    .type_contains_resumption(*capture_type, visiting)
                    .unwrap_or(true),
                Type::Handler { capture_type, .. } => self
                    .type_contains_resumption(*capture_type, visiting)
                    .unwrap_or(true),
                Type::BindingPack { payload_type, .. } => self
                    .type_contains_resumption(*payload_type, visiting)
                    .unwrap_or(true),
                Type::Tuple { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_resumption(*field, visiting)
                        .unwrap_or(true)
                }),
                Type::Struct { fields, .. } => fields.iter().any(|field| {
                    self.type_contains_resumption(field.ty, visiting)
                        .unwrap_or(true)
                }),
                Type::Enum { variants, .. } => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| {
                        self.type_contains_resumption(field.ty, visiting)
                            .unwrap_or(true)
                    }),
                _ => false,
            };
        visiting.remove(&ty);
        Ok(contains)
    }

    fn type_needs_destroy(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<bool, Vec<Diagnostic>> {
        if self
            .phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == ty)
        {
            return Ok(true);
        }
        if !visiting.insert(ty) {
            return Ok(false);
        }
        let needs_destroy = match self.runtime_type(ty)? {
            Type::Text
            | Type::Bytes
            | Type::Callable { .. }
            | Type::Handler { .. }
            | Type::Resumption { .. }
            | Type::Array { .. } => true,
            Type::BindingPack { payload_type, .. } => {
                self.type_needs_destroy(*payload_type, visiting)?
            }
            Type::Tuple { fields, .. } => fields.iter().try_fold(false, |needed, field| {
                Ok::<bool, Vec<Diagnostic>>(needed || self.type_needs_destroy(*field, visiting)?)
            })?,
            Type::Struct { fields, .. } => fields.iter().try_fold(false, |needed, field| {
                Ok::<bool, Vec<Diagnostic>>(needed || self.type_needs_destroy(field.ty, visiting)?)
            })?,
            Type::Enum { variants, .. } => variants
                .iter()
                .flat_map(|variant| &variant.fields)
                .try_fold(false, |needed, field| {
                    Ok::<bool, Vec<Diagnostic>>(
                        needed || self.type_needs_destroy(field.ty, visiting)?,
                    )
                })?,
            _ => false,
        };
        visiting.remove(&ty);
        Ok(needs_destroy)
    }

    fn ensure_plain_array_element(
        &self,
        ty: TypeId,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        self.ensure_plain_array_element_inner(ty, function, true)
    }

    fn ensure_plain_array_element_inner(
        &self,
        ty: TypeId,
        function: &mir::Function,
        root: bool,
    ) -> Result<(), Vec<Diagnostic>> {
        match self.runtime_type(ty)? {
            Type::Handler { .. } => {
                return Err(vec![unsupported(
                    function,
                    "Array elements with effect runtime state",
                )]);
            }
            Type::Available { .. } if root => {
                return Err(vec![unsupported(
                    function,
                    "Array elements cannot be standalone erased evidence",
                )]);
            }
            Type::Available { .. } => {}
            Type::Resumption { .. } => {}
            Type::Callable { capture_type, .. } => {
                self.ensure_plain_array_element_inner(*capture_type, function, false)?;
            }
            Type::BindingPack { payload_type, .. } => {
                self.ensure_plain_array_element_inner(*payload_type, function, false)?;
            }
            Type::Array { element } => {
                self.ensure_plain_array_element_inner(*element, function, true)?
            }
            Type::Tuple { fields, .. } => {
                for field in fields {
                    self.ensure_plain_array_element_inner(*field, function, false)?;
                }
            }
            Type::Struct { fields, .. } => {
                for field in fields {
                    self.ensure_plain_array_element_inner(field.ty, function, false)?;
                }
            }
            Type::Enum { variants, .. } => {
                for field in variants.iter().flat_map(|variant| &variant.fields) {
                    self.ensure_plain_array_element_inner(field.ty, function, false)?;
                }
            }
            _ => {}
        }
        self.llvm_type(ty)?;
        Ok(())
    }

    fn emit_retain(
        &mut self,
        ty: TypeId,
        value: &str,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        match self.runtime_type(ty)?.clone() {
            Type::Text | Type::Bytes => {
                self.line(&format!("  call void @g1_bytes_retain(ptr {value})"));
            }
            Type::Callable { .. } => {
                let count_address = self.temp();
                self.line(&format!(
                    "  %{count_address} = getelementptr inbounds %g1.callable, ptr {value}, i32 0, i32 0"
                ));
                let count = self.temp();
                self.line(&format!("  %{count} = load i64, ptr %{count_address}"));
                let next = self.temp();
                self.line(&format!("  %{next} = add i64 %{count}, 1"));
                self.line(&format!("  store i64 %{next}, ptr %{count_address}"));
            }
            Type::BindingPack { payload_type, .. } => {
                self.emit_retain(payload_type, value, function)?;
            }
            Type::Tuple { .. } | Type::Struct { .. } => {
                let aggregate_ty = self.llvm_type(ty)?;
                for field in self.runtime_aggregate_field_layout(ty, 0)? {
                    if self.type_contains_byte_object(field.runtime_type, &mut BTreeSet::new())?
                        || self.type_contains_callable(field.runtime_type, &mut BTreeSet::new())?
                        || self.type_contains_handler(field.runtime_type, &mut BTreeSet::new())?
                        || self
                            .type_contains_resumption(field.runtime_type, &mut BTreeSet::new())?
                    {
                        let extracted = self.temp();
                        self.line(&format!(
                            "  %{extracted} = extractvalue {aggregate_ty} {value}, {}",
                            field.physical_index
                        ));
                        self.emit_retain(field.runtime_type, &format!("%{extracted}"), function)?;
                    }
                }
            }
            Type::Enum { .. } if self.type_contains_array(ty, &mut BTreeSet::new())? => {
                return Err(vec![unsupported(
                    function,
                    "copying enum values that contain Array",
                )]);
            }
            Type::Enum { .. }
                if self.type_contains_byte_object(ty, &mut BTreeSet::new())?
                    || self.type_contains_callable(ty, &mut BTreeSet::new())?
                    || self.type_contains_handler(ty, &mut BTreeSet::new())?
                    || self.type_contains_resumption(ty, &mut BTreeSet::new())? =>
            {
                self.emit_visit_enum_payloads(ty, value, true, function)?;
            }
            Type::Array { .. } if self.type_contains_array(ty, &mut BTreeSet::new())? => {
                return Err(vec![unsupported(function, "copying Array values")]);
            }
            Type::Handler { .. } => self.emit_retain_handler(value),
            Type::Resumption {
                upper_uses, copy, ..
            } => {
                if copy || upper_uses.is_none_or(|upper| upper > 1) {
                    self.emit_retain_resumption(value);
                } else {
                    return Err(vec![unsupported(
                        function,
                        "copying one-shot Resumption values",
                    )]);
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn emit_clone_effect_snapshot_value(
        &mut self,
        ty: TypeId,
        value: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let contains_array = self.type_contains_array(ty, &mut BTreeSet::new())?;
        let contains_resumption = self.type_contains_resumption(ty, &mut BTreeSet::new())?;
        let contains_callable = self.type_contains_callable(ty, &mut BTreeSet::new())?;
        let is_handler = matches!(self.runtime_type(ty)?, Type::Handler { .. });
        if !contains_array && !contains_resumption && !contains_callable && !is_handler {
            self.emit_retain(ty, value, function)?;
            return Ok(value.to_owned());
        }
        match self.runtime_type(ty)?.clone() {
            Type::Resumption { .. } => {
                self.emit_clone_resumption_wrapper(ty, value, function, context)
            }
            Type::Callable { capture_type, .. } => {
                self.emit_clone_effect_snapshot_callable(ty, capture_type, value, function, context)
            }
            Type::BindingPack { payload_type, .. } => {
                self.emit_clone_effect_snapshot_value(payload_type, value, function, context)
            }
            Type::Tuple { .. } | Type::Struct { .. } => {
                let fields = self.runtime_aggregate_fields(ty)?;
                self.emit_clone_effect_snapshot_aggregate(ty, value, &fields, function, context)
            }
            Type::Enum { .. } => {
                if contains_resumption {
                    Err(vec![unsupported(
                        function,
                        "cloning effect-frame enum values that contain Resumption",
                    )])
                } else {
                    self.emit_transform_effect_snapshot_enum(ty, value, function, context, true)
                }
            }
            Type::Array { element } => {
                if contains_resumption {
                    return Err(vec![unsupported(
                        function,
                        "cloning effect-frame Array values that contain Resumption",
                    )]);
                }
                self.emit_clone_effect_snapshot_array(element, value, function, context)
            }
            Type::Handler { capture_type, .. } => {
                self.emit_clone_effect_snapshot_handler(ty, capture_type, value, function, context)
            }
            _ => Err(vec![unsupported(
                function,
                "cloning an unsupported effect-frame Resumption carrier",
            )]),
        }
    }

    fn effect_callable_capture_type(
        &self,
        function: &mir::Function,
    ) -> Result<TypeId, Vec<Diagnostic>> {
        match (
            function.receiver_mode,
            self.runtime_type(function.receiver_type)?,
        ) {
            (Some(0), Type::RefShared { referent }) | (Some(1), Type::RefUnique { referent }) => {
                Ok(*referent)
            }
            (Some(2), _) => Ok(function.receiver_type),
            _ => Err(vec![unsupported(
                function,
                "effect callable has an invalid receiver layout",
            )]),
        }
    }

    fn callable_runtime_type_for_capture(
        &self,
        capture_type: TypeId,
    ) -> Result<TypeId, Vec<Diagnostic>> {
        self.phases
            .artifact
            .types
            .iter()
            .enumerate()
            .find_map(|(index, ty)| match ty.representation() {
                Type::Callable {
                    capture_type: described,
                    ..
                } if *described == capture_type => Some(index as TypeId),
                _ => None,
            })
            .ok_or_else(|| {
                vec![backend_error(format!(
                    "capture type t{capture_type} has no runtime callable type"
                ))]
            })
    }

    fn emit_clone_effect_snapshot_guard_chain(
        &mut self,
        source: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let usize_ty = format!("i{}", self.pointer_width());
        let handler_cases = (0..self.phases.artifact.handler_defs.len())
            .map(|handler_def| {
                let handler_type = self.handler_runtime_type(handler_def as u32)?;
                let Type::Handler { capture_type, .. } = self.runtime_type(handler_type)?.clone()
                else {
                    unreachable!()
                };
                Ok((handler_def, handler_type, capture_type))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;
        let callable_cases = self
            .llvm_reachable_functions
            .iter()
            .copied()
            .filter(|index| {
                self.phases
                    .mir
                    .functions
                    .get(*index)
                    .is_some_and(|function| {
                        self.function_needs_effect_frame(function)
                            && function.receiver_mode.is_some()
                    })
            })
            .map(|index| {
                let target = self.phases.mir.functions[index].clone();
                let capture_type = self.effect_callable_capture_type(&target)?;
                let callable_type = self.callable_runtime_type_for_capture(capture_type)?;
                Ok((index, callable_type, capture_type))
            })
            .collect::<Result<Vec<_>, Vec<Diagnostic>>>()?;

        let result_slot = self.temp();
        let source_slot = self.temp();
        let previous_clone_slot = self.temp();
        let loop_label = self.temp();
        let inspect_label = self.temp();
        let finish_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  %{result_slot} = alloca ptr"));
        self.line(&format!("  %{source_slot} = alloca ptr"));
        self.line(&format!("  %{previous_clone_slot} = alloca ptr"));
        self.line(&format!("  store ptr null, ptr %{result_slot}"));
        self.line(&format!("  store ptr {source}, ptr %{source_slot}"));
        self.line(&format!("  store ptr null, ptr %{previous_clone_slot}"));
        self.line(&format!("  br label %guard.snapshot.loop{loop_label}"));
        self.line(&format!("guard.snapshot.loop{loop_label}:"));
        let current = self.temp();
        let present = self.temp();
        self.line(&format!("  %{current} = load ptr, ptr %{source_slot}"));
        self.line(&format!("  %{present} = icmp ne ptr %{current}, null"));
        self.line(&format!(
            "  br i1 %{present}, label %guard.snapshot.inspect{inspect_label}, label %guard.snapshot.finish{finish_label}"
        ));
        self.line(&format!("guard.snapshot.inspect{inspect_label}:"));
        let existing = self.temp();
        let found = self.temp();
        let reuse_label = self.temp();
        let clone_label = self.temp();
        self.line(&format!(
            "  %{existing} = call ptr @g1_snapshot_lookup_exact(ptr {context}, ptr %{current})"
        ));
        self.line(&format!("  %{found} = icmp ne ptr %{existing}, null"));
        self.line(&format!(
            "  br i1 %{found}, label %guard.snapshot.reuse{reuse_label}, label %guard.snapshot.clone{clone_label}"
        ));

        self.line(&format!("guard.snapshot.reuse{reuse_label}:"));
        self.line(&format!(
            "  call void @g1_effect_guard_retain(ptr %{existing})"
        ));
        self.emit_link_cloned_guard(
            &format!("%{result_slot}"),
            &format!("%{previous_clone_slot}"),
            &format!("%{existing}"),
        );
        self.line(&format!("  br label %guard.snapshot.done{done_label}"));

        self.line(&format!("guard.snapshot.clone{clone_label}:"));
        let guard_size = self.emit_array_element_size("%g1.effect_guard");
        let cloned = self.temp();
        let failed = self.temp();
        self.line(&format!(
            "  %{cloned} = call ptr @malloc({usize_ty} {guard_size})"
        ));
        self.line(&format!("  %{failed} = icmp eq ptr %{cloned}, null"));
        self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        self.line(&format!(
            "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{cloned}, ptr %{current}, {usize_ty} {guard_size}, i1 false)"
        ));
        let count_address = self.temp();
        let next_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.effect_guard, ptr %{cloned}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{count_address}"));
        self.line(&format!(
            "  %{next_address} = getelementptr inbounds %g1.effect_guard, ptr %{cloned}, i32 0, i32 3"
        ));
        self.line(&format!("  store ptr null, ptr %{next_address}"));
        self.line(&format!(
            "  call void @g1_snapshot_record(ptr {context}, ptr %{current}, {usize_ty} {guard_size}, ptr %{cloned}, ptr null)"
        ));

        let payload_address = self.temp();
        let payload = self.temp();
        let drop_address = self.temp();
        let drop = self.temp();
        self.line(&format!(
            "  %{payload_address} = getelementptr inbounds %g1.effect_guard, ptr %{current}, i32 0, i32 1"
        ));
        self.line(&format!("  %{payload} = load ptr, ptr %{payload_address}"));
        self.line(&format!(
            "  %{drop_address} = getelementptr inbounds %g1.effect_guard, ptr %{current}, i32 0, i32 2"
        ));
        self.line(&format!("  %{drop} = load ptr, ptr %{drop_address}"));
        let payload_slot = self.temp();
        self.line(&format!("  %{payload_slot} = alloca ptr"));
        let payload_ready = self.temp();

        let mut next_check = None;
        for (handler_def, handler_type, capture_type) in handler_cases {
            if let Some(label) = next_check.take() {
                self.line(&format!("guard.snapshot.payload.check{label}:"));
            }
            let matches = self.temp();
            let matched_label = self.temp();
            let otherwise_label = self.temp();
            self.line(&format!(
                "  %{matches} = icmp eq ptr %{drop}, @g1_effect_handler_drop_h{handler_def}"
            ));
            self.line(&format!(
                "  br i1 %{matches}, label %guard.snapshot.payload.handler{matched_label}, label %guard.snapshot.payload.check{otherwise_label}"
            ));
            self.line(&format!("guard.snapshot.payload.handler{matched_label}:"));
            let cloned_payload = self.emit_clone_effect_snapshot_handler(
                handler_type,
                capture_type,
                &format!("%{payload}"),
                function,
                context,
            )?;
            self.line(&format!(
                "  store ptr {cloned_payload}, ptr %{payload_slot}"
            ));
            self.line(&format!(
                "  br label %guard.snapshot.payload.ready{payload_ready}"
            ));
            next_check = Some(otherwise_label);
        }
        for (index, callable_type, capture_type) in callable_cases {
            if let Some(label) = next_check.take() {
                self.line(&format!("guard.snapshot.payload.check{label}:"));
            }
            let matches = self.temp();
            let matched_label = self.temp();
            let otherwise_label = self.temp();
            self.line(&format!(
                "  %{matches} = icmp eq ptr %{drop}, @g1_effect_guard_drop_f{index}"
            ));
            self.line(&format!(
                "  br i1 %{matches}, label %guard.snapshot.payload.callable{matched_label}, label %guard.snapshot.payload.check{otherwise_label}"
            ));
            self.line(&format!("guard.snapshot.payload.callable{matched_label}:"));
            let cloned_payload = self.emit_clone_effect_snapshot_callable(
                callable_type,
                capture_type,
                &format!("%{payload}"),
                function,
                context,
            )?;
            self.line(&format!(
                "  store ptr {cloned_payload}, ptr %{payload_slot}"
            ));
            self.line(&format!(
                "  br label %guard.snapshot.payload.ready{payload_ready}"
            ));
            next_check = Some(otherwise_label);
        }
        if let Some(label) = next_check.take() {
            self.line(&format!("guard.snapshot.payload.check{label}:"));
        }
        let is_chain = self.temp();
        let chain_label = self.temp();
        let invalid_label = self.temp();
        self.line(&format!(
            "  %{is_chain} = icmp eq ptr %{drop}, @g1_effect_guard_drop_chain"
        ));
        self.line(&format!(
            "  br i1 %{is_chain}, label %guard.snapshot.payload.chain{chain_label}, label %guard.snapshot.payload.invalid{invalid_label}"
        ));
        self.line(&format!("guard.snapshot.payload.chain{chain_label}:"));
        let cloned_chain = self.temp();
        self.line(&format!(
            "  %{cloned_chain} = call ptr @g1_effect_clone_chain_owners(ptr %{payload}, ptr {context})"
        ));
        self.line(&format!("  store ptr %{cloned_chain}, ptr %{payload_slot}"));
        self.line(&format!(
            "  br label %guard.snapshot.payload.ready{payload_ready}"
        ));
        self.line(&format!("guard.snapshot.payload.invalid{invalid_label}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");

        self.line(&format!("guard.snapshot.payload.ready{payload_ready}:"));
        let cloned_payload = self.temp();
        let cloned_payload_address = self.temp();
        self.line(&format!(
            "  %{cloned_payload} = load ptr, ptr %{payload_slot}"
        ));
        self.line(&format!(
            "  %{cloned_payload_address} = getelementptr inbounds %g1.effect_guard, ptr %{cloned}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  store ptr %{cloned_payload}, ptr %{cloned_payload_address}"
        ));
        self.emit_link_cloned_guard(
            &format!("%{result_slot}"),
            &format!("%{previous_clone_slot}"),
            &format!("%{cloned}"),
        );
        self.line(&format!(
            "  store ptr %{cloned}, ptr %{previous_clone_slot}"
        ));
        let source_next_address = self.temp();
        let source_next = self.temp();
        self.line(&format!(
            "  %{source_next_address} = getelementptr inbounds %g1.effect_guard, ptr %{current}, i32 0, i32 3"
        ));
        self.line(&format!(
            "  %{source_next} = load ptr, ptr %{source_next_address}"
        ));
        self.line(&format!("  store ptr %{source_next}, ptr %{source_slot}"));
        self.line(&format!("  br label %guard.snapshot.loop{loop_label}"));

        self.line(&format!("guard.snapshot.finish{finish_label}:"));
        self.line(&format!("  br label %guard.snapshot.done{done_label}"));
        self.line(&format!("guard.snapshot.done{done_label}:"));
        let result = self.temp();
        self.line(&format!("  %{result} = load ptr, ptr %{result_slot}"));
        Ok(format!("%{result}"))
    }

    fn emit_link_cloned_guard(&mut self, top_slot: &str, previous_slot: &str, guard: &str) {
        let previous = self.temp();
        let has_previous = self.temp();
        let previous_label = self.temp();
        let top_label = self.temp();
        let linked_label = self.temp();
        self.line(&format!("  %{previous} = load ptr, ptr {previous_slot}"));
        self.line(&format!(
            "  %{has_previous} = icmp ne ptr %{previous}, null"
        ));
        self.line(&format!(
            "  br i1 %{has_previous}, label %guard.snapshot.link.previous{previous_label}, label %guard.snapshot.link.top{top_label}"
        ));
        self.line(&format!("guard.snapshot.link.previous{previous_label}:"));
        let next_address = self.temp();
        self.line(&format!(
            "  %{next_address} = getelementptr inbounds %g1.effect_guard, ptr %{previous}, i32 0, i32 3"
        ));
        self.line(&format!("  store ptr {guard}, ptr %{next_address}"));
        self.line(&format!("  br label %guard.snapshot.linked{linked_label}"));
        self.line(&format!("guard.snapshot.link.top{top_label}:"));
        self.line(&format!("  store ptr {guard}, ptr {top_slot}"));
        self.line(&format!("  br label %guard.snapshot.linked{linked_label}"));
        self.line(&format!("guard.snapshot.linked{linked_label}:"));
    }

    fn emit_clone_effect_snapshot_aggregate(
        &mut self,
        aggregate_type: TypeId,
        aggregate: &str,
        fields: &[TypeId],
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let aggregate_ty = self.llvm_type(aggregate_type)?;
        let mut rebuilt = aggregate.to_owned();
        for (index, field_type) in fields.iter().copied().enumerate() {
            let extracted = self.temp();
            self.line(&format!(
                "  %{extracted} = extractvalue {aggregate_ty} {aggregate}, {index}"
            ));
            let cloned = self.emit_clone_effect_snapshot_value(
                field_type,
                &format!("%{extracted}"),
                function,
                context,
            )?;
            let inserted = self.temp();
            self.line(&format!(
                "  %{inserted} = insertvalue {aggregate_ty} {rebuilt}, {} {cloned}, {index}",
                self.llvm_type(field_type)?
            ));
            rebuilt = format!("%{inserted}");
        }
        Ok(rebuilt)
    }

    fn emit_clone_effect_snapshot_callable(
        &mut self,
        callable_type: TypeId,
        capture_type: TypeId,
        source: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let usize_ty = format!("i{}", self.pointer_width());
        let result_slot = self.temp();
        let existing = self.temp();
        let found = self.temp();
        let reuse_label = self.temp();
        let clone_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  %{result_slot} = alloca ptr"));
        self.line(&format!(
            "  %{existing} = call ptr @g1_snapshot_lookup_exact(ptr {context}, ptr {source})"
        ));
        self.line(&format!("  %{found} = icmp ne ptr %{existing}, null"));
        self.line(&format!(
            "  br i1 %{found}, label %callable.snapshot.reuse{reuse_label}, label %callable.snapshot.clone{clone_label}"
        ));
        self.line(&format!("callable.snapshot.reuse{reuse_label}:"));
        self.emit_retain(callable_type, &format!("%{existing}"), function)?;
        self.line(&format!("  store ptr %{existing}, ptr %{result_slot}"));
        self.line(&format!("  br label %callable.snapshot.done{done_label}"));

        self.line(&format!("callable.snapshot.clone{clone_label}:"));
        let shell_size = self.emit_array_element_size("%g1.callable");
        let cloned = self.temp();
        let failed = self.temp();
        self.line(&format!(
            "  %{cloned} = call ptr @malloc({usize_ty} {shell_size})"
        ));
        self.line(&format!("  %{failed} = icmp eq ptr %{cloned}, null"));
        self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        self.line(&format!(
            "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{cloned}, ptr {source}, {usize_ty} {shell_size}, i1 false)"
        ));
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.callable, ptr %{cloned}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{count_address}"));
        self.line(&format!(
            "  call void @g1_snapshot_record(ptr {context}, ptr {source}, {usize_ty} {shell_size}, ptr %{cloned}, ptr null)"
        ));
        let source_capture_address = self.temp();
        let source_capture = self.temp();
        self.line(&format!(
            "  %{source_capture_address} = getelementptr inbounds %g1.callable, ptr {source}, i32 0, i32 2"
        ));
        self.line(&format!(
            "  %{source_capture} = load ptr, ptr %{source_capture_address}"
        ));
        let cloned_capture = self.emit_clone_effect_snapshot_capture(
            capture_type,
            &format!("%{source_capture}"),
            function,
            context,
        )?;
        let cloned_capture_address = self.temp();
        self.line(&format!(
            "  %{cloned_capture_address} = getelementptr inbounds %g1.callable, ptr %{cloned}, i32 0, i32 2"
        ));
        self.line(&format!(
            "  store ptr {cloned_capture}, ptr %{cloned_capture_address}"
        ));
        self.line(&format!("  store ptr %{cloned}, ptr %{result_slot}"));
        self.line(&format!("  br label %callable.snapshot.done{done_label}"));

        self.line(&format!("callable.snapshot.done{done_label}:"));
        let result = self.temp();
        self.line(&format!("  %{result} = load ptr, ptr %{result_slot}"));
        Ok(format!("%{result}"))
    }

    fn emit_clone_effect_snapshot_handler(
        &mut self,
        handler_type: TypeId,
        capture_type: TypeId,
        source: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let clause_types = self.runtime_aggregate_fields(capture_type)?;
        let usize_ty = format!("i{}", self.pointer_width());
        let result_slot = self.temp();
        let existing = self.temp();
        let found = self.temp();
        let reuse_label = self.temp();
        let clone_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  %{result_slot} = alloca ptr"));
        self.line(&format!(
            "  %{existing} = call ptr @g1_snapshot_lookup_exact(ptr {context}, ptr {source})"
        ));
        self.line(&format!("  %{found} = icmp ne ptr %{existing}, null"));
        self.line(&format!(
            "  br i1 %{found}, label %handler.snapshot.reuse{reuse_label}, label %handler.snapshot.clone{clone_label}"
        ));
        self.line(&format!("handler.snapshot.reuse{reuse_label}:"));
        self.emit_retain_handler(&format!("%{existing}"));
        self.line(&format!("  store ptr %{existing}, ptr %{result_slot}"));
        self.line(&format!("  br label %handler.snapshot.done{done_label}"));

        self.line(&format!("handler.snapshot.clone{clone_label}:"));
        let shell_size = self.emit_array_element_size("%g1.handler");
        let cloned = self.temp();
        let failed = self.temp();
        self.line(&format!(
            "  %{cloned} = call ptr @malloc({usize_ty} {shell_size})"
        ));
        self.line(&format!("  %{failed} = icmp eq ptr %{cloned}, null"));
        self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        self.line(&format!(
            "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{cloned}, ptr {source}, {usize_ty} {shell_size}, i1 false)"
        ));
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.handler, ptr %{cloned}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{count_address}"));
        self.line(&format!(
            "  call void @g1_snapshot_record(ptr {context}, ptr {source}, {usize_ty} {shell_size}, ptr %{cloned}, ptr null)"
        ));

        let source_clauses_address = self.temp();
        let source_clauses = self.temp();
        self.line(&format!(
            "  %{source_clauses_address} = getelementptr inbounds %g1.handler, ptr {source}, i32 0, i32 3"
        ));
        self.line(&format!(
            "  %{source_clauses} = load ptr, ptr %{source_clauses_address}"
        ));
        let cloned_clauses = if clause_types.is_empty() {
            "null".to_owned()
        } else {
            let storage = self.temp();
            let storage_failed = self.temp();
            let pointer_size = usize::from(self.pointer_width() / 8);
            self.line(&format!(
                "  %{storage} = call ptr @malloc({usize_ty} {})",
                clause_types.len() * pointer_size
            ));
            self.line(&format!(
                "  %{storage_failed} = icmp eq ptr %{storage}, null"
            ));
            self.emit_runtime_fault_if(storage_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
            format!("%{storage}")
        };
        let cloned_clauses_address = self.temp();
        self.line(&format!(
            "  %{cloned_clauses_address} = getelementptr inbounds %g1.handler, ptr %{cloned}, i32 0, i32 3"
        ));
        self.line(&format!(
            "  store ptr {cloned_clauses}, ptr %{cloned_clauses_address}"
        ));

        for (index, clause_type) in clause_types.into_iter().enumerate() {
            let Type::Callable { capture_type, .. } = self.runtime_type(clause_type)?.clone()
            else {
                return Err(vec![unsupported(
                    function,
                    "handler clause has a non-callable runtime type",
                )]);
            };
            let clause_result_slot = self.temp();
            self.line(&format!("  %{clause_result_slot} = alloca ptr"));
            let source_slot = self.temp();
            let source_clause = self.temp();
            let present = self.temp();
            let clone_clause_label = self.temp();
            let null_clause_label = self.temp();
            let clause_done_label = self.temp();
            self.line(&format!(
                "  %{source_slot} = getelementptr inbounds ptr, ptr %{source_clauses}, {usize_ty} {index}"
            ));
            self.line(&format!(
                "  %{source_clause} = load ptr, ptr %{source_slot}"
            ));
            self.line(&format!(
                "  %{present} = icmp ne ptr %{source_clause}, null"
            ));
            self.line(&format!(
                "  br i1 %{present}, label %handler.snapshot.clause{clone_clause_label}, label %handler.snapshot.null{null_clause_label}"
            ));
            self.line(&format!("handler.snapshot.clause{clone_clause_label}:"));
            let cloned_clause = self.emit_clone_effect_snapshot_callable(
                clause_type,
                capture_type,
                &format!("%{source_clause}"),
                function,
                context,
            )?;
            self.line(&format!(
                "  store ptr {cloned_clause}, ptr %{clause_result_slot}"
            ));
            self.line(&format!(
                "  br label %handler.snapshot.clause.done{clause_done_label}"
            ));
            self.line(&format!("handler.snapshot.null{null_clause_label}:"));
            self.line(&format!("  store ptr null, ptr %{clause_result_slot}"));
            self.line(&format!(
                "  br label %handler.snapshot.clause.done{clause_done_label}"
            ));
            self.line(&format!("handler.snapshot.clause.done{clause_done_label}:"));
            let final_clause = self.temp();
            let cloned_slot = self.temp();
            self.line(&format!(
                "  %{final_clause} = load ptr, ptr %{clause_result_slot}"
            ));
            self.line(&format!(
                "  %{cloned_slot} = getelementptr inbounds ptr, ptr {cloned_clauses}, {usize_ty} {index}"
            ));
            self.line(&format!("  store ptr %{final_clause}, ptr %{cloned_slot}"));
        }

        self.line(&format!("  store ptr %{cloned}, ptr %{result_slot}"));
        self.line(&format!("  br label %handler.snapshot.done{done_label}"));
        self.line(&format!("handler.snapshot.done{done_label}:"));
        let result = self.temp();
        self.line(&format!("  %{result} = load ptr, ptr %{result_slot}"));
        let _ = handler_type;
        Ok(format!("%{result}"))
    }

    fn emit_clone_effect_snapshot_capture(
        &mut self,
        capture_type: TypeId,
        source: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let usize_ty = format!("i{}", self.pointer_width());
        let result_slot = self.temp();
        let existing = self.temp();
        let found = self.temp();
        let reuse_label = self.temp();
        let clone_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  %{result_slot} = alloca ptr"));
        self.line(&format!(
            "  %{existing} = call ptr @g1_snapshot_lookup_exact(ptr {context}, ptr {source})"
        ));
        self.line(&format!("  %{found} = icmp ne ptr %{existing}, null"));
        self.line(&format!(
            "  br i1 %{found}, label %capture.snapshot.reuse{reuse_label}, label %capture.snapshot.clone{clone_label}"
        ));
        self.line(&format!("capture.snapshot.reuse{reuse_label}:"));
        self.emit_retain_capture(&format!("%{existing}"));
        self.line(&format!("  store ptr %{existing}, ptr %{result_slot}"));
        self.line(&format!("  br label %capture.snapshot.done{done_label}"));

        self.line(&format!("capture.snapshot.clone{clone_label}:"));
        let handle_size = self.emit_array_element_size("%g1.capture");
        let cloned = self.temp();
        let failed = self.temp();
        self.line(&format!(
            "  %{cloned} = call ptr @malloc({usize_ty} {handle_size})"
        ));
        self.line(&format!("  %{failed} = icmp eq ptr %{cloned}, null"));
        self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.capture, ptr %{cloned}, i32 0, i32 0"
        ));
        self.line(&format!("  store i64 1, ptr %{count_address}"));
        let cloned_data_address = self.temp();
        self.line(&format!(
            "  %{cloned_data_address} = getelementptr inbounds %g1.capture, ptr %{cloned}, i32 0, i32 1"
        ));
        self.line(&format!("  store ptr null, ptr %{cloned_data_address}"));
        self.line(&format!(
            "  call void @g1_snapshot_record(ptr {context}, ptr {source}, {usize_ty} {handle_size}, ptr %{cloned}, ptr null)"
        ));

        let data_result_slot = self.temp();
        let source_data_address = self.temp();
        let source_data = self.temp();
        let has_data = self.temp();
        let data_label = self.temp();
        let empty_label = self.temp();
        let data_done_label = self.temp();
        self.line(&format!("  %{data_result_slot} = alloca ptr"));
        self.line(&format!(
            "  %{source_data_address} = getelementptr inbounds %g1.capture, ptr {source}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{source_data} = load ptr, ptr %{source_data_address}"
        ));
        self.line(&format!("  %{has_data} = icmp ne ptr %{source_data}, null"));
        self.line(&format!(
            "  br i1 %{has_data}, label %capture.snapshot.data{data_label}, label %capture.snapshot.empty{empty_label}"
        ));
        self.line(&format!("capture.snapshot.data{data_label}:"));
        let capture_ty = self.llvm_type(capture_type)?;
        let data_size = self.emit_array_element_size(&capture_ty);
        let cloned_data = self.temp();
        let data_failed = self.temp();
        self.line(&format!(
            "  %{cloned_data} = call ptr @malloc({usize_ty} {data_size})"
        ));
        self.line(&format!(
            "  %{data_failed} = icmp eq ptr %{cloned_data}, null"
        ));
        self.emit_runtime_fault_if(data_failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        self.snapshot_capture_fix_types.insert(capture_type);
        self.line(&format!(
            "  call void @g1_snapshot_record(ptr {context}, ptr %{source_data}, {usize_ty} {data_size}, ptr %{cloned_data}, ptr @g1_snapshot_fix_capture_t{capture_type})"
        ));
        let source_value = self.temp();
        self.line(&format!(
            "  %{source_value} = load {capture_ty}, ptr %{source_data}"
        ));
        let cloned_value = self.emit_clone_effect_snapshot_value(
            capture_type,
            &format!("%{source_value}"),
            function,
            context,
        )?;
        self.line(&format!(
            "  store {capture_ty} {cloned_value}, ptr %{cloned_data}"
        ));
        self.line(&format!(
            "  store ptr %{cloned_data}, ptr %{data_result_slot}"
        ));
        self.line(&format!(
            "  br label %capture.snapshot.data.done{data_done_label}"
        ));
        self.line(&format!("capture.snapshot.empty{empty_label}:"));
        self.line(&format!("  store ptr null, ptr %{data_result_slot}"));
        self.line(&format!(
            "  br label %capture.snapshot.data.done{data_done_label}"
        ));
        self.line(&format!("capture.snapshot.data.done{data_done_label}:"));
        let final_data = self.temp();
        self.line(&format!(
            "  %{final_data} = load ptr, ptr %{data_result_slot}"
        ));
        self.line(&format!(
            "  store ptr %{final_data}, ptr %{cloned_data_address}"
        ));
        self.line(&format!("  store ptr %{cloned}, ptr %{result_slot}"));
        self.line(&format!("  br label %capture.snapshot.done{done_label}"));

        self.line(&format!("capture.snapshot.done{done_label}:"));
        let result = self.temp();
        self.line(&format!("  %{result} = load ptr, ptr %{result_slot}"));
        Ok(format!("%{result}"))
    }

    fn emit_clone_effect_snapshot_array(
        &mut self,
        element_type: TypeId,
        source: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let usize_ty = format!("i{}", self.pointer_width());
        let element_ty = self.llvm_type(element_type)?;
        let capacity_address = self.temp();
        let capacity = self.temp();
        let element_size_address = self.temp();
        let element_size = self.temp();
        self.line(&format!(
            "  %{capacity_address} = getelementptr inbounds %g1.array, ptr {source}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{capacity} = load {usize_ty}, ptr %{capacity_address}"
        ));
        self.line(&format!(
            "  %{element_size_address} = getelementptr inbounds %g1.array, ptr {source}, i32 0, i32 2"
        ));
        self.line(&format!(
            "  %{element_size} = load {usize_ty}, ptr %{element_size_address}"
        ));
        let clone = self.temp();
        self.line(&format!(
            "  %{clone} = call ptr @g1_array_allocate({usize_ty} %{capacity}, {usize_ty} %{element_size})"
        ));
        let header_size = self.emit_array_element_size("%g1.array");
        self.line(&format!(
            "  call void @g1_snapshot_record(ptr {context}, ptr {source}, {usize_ty} {header_size}, ptr %{clone}, ptr null)"
        ));
        let source_data_address = self.temp();
        let source_data = self.temp();
        let clone_data_address = self.temp();
        let clone_data = self.temp();
        let data_size = self.temp();
        self.line(&format!(
            "  %{source_data_address} = getelementptr inbounds %g1.array, ptr {source}, i32 0, i32 3"
        ));
        self.line(&format!(
            "  %{source_data} = load ptr, ptr %{source_data_address}"
        ));
        self.line(&format!(
            "  %{clone_data_address} = getelementptr inbounds %g1.array, ptr %{clone}, i32 0, i32 3"
        ));
        self.line(&format!(
            "  %{clone_data} = load ptr, ptr %{clone_data_address}"
        ));
        self.line(&format!(
            "  %{data_size} = mul {usize_ty} %{capacity}, %{element_size}"
        ));
        let has_data = self.temp();
        let record_data = self.temp();
        let data_recorded = self.temp();
        self.line(&format!(
            "  %{has_data} = icmp ne {usize_ty} %{data_size}, 0"
        ));
        self.line(&format!(
            "  br i1 %{has_data}, label %array.clone.record{record_data}, label %array.clone.recorded{data_recorded}"
        ));
        self.line(&format!("array.clone.record{record_data}:"));
        self.line(&format!(
            "  call void @g1_snapshot_record(ptr {context}, ptr %{source_data}, {usize_ty} %{data_size}, ptr %{clone_data}, ptr null)"
        ));
        self.line(&format!("  br label %array.clone.recorded{data_recorded}"));
        self.line(&format!("array.clone.recorded{data_recorded}:"));
        let source_length_address = self.temp();
        let source_length = self.temp();
        let clone_length_address = self.temp();
        self.line(&format!(
            "  %{source_length_address} = getelementptr inbounds %g1.array, ptr {source}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{source_length} = load {usize_ty}, ptr %{source_length_address}"
        ));
        self.line(&format!(
            "  %{clone_length_address} = getelementptr inbounds %g1.array, ptr %{clone}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  store {usize_ty} %{source_length}, ptr %{clone_length_address}"
        ));
        let source_flags_address = self.temp();
        let source_flags = self.temp();
        let clone_flags_address = self.temp();
        let clone_flags = self.temp();
        self.line(&format!(
            "  %{source_flags_address} = getelementptr inbounds %g1.array, ptr {source}, i32 0, i32 4"
        ));
        self.line(&format!(
            "  %{source_flags} = load ptr, ptr %{source_flags_address}"
        ));
        self.line(&format!(
            "  %{clone_flags_address} = getelementptr inbounds %g1.array, ptr %{clone}, i32 0, i32 4"
        ));
        self.line(&format!(
            "  %{clone_flags} = load ptr, ptr %{clone_flags_address}"
        ));
        let loop_label = self.temp();
        let inspect_label = self.temp();
        let clone_label = self.temp();
        let next_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  br label %array.clone.loop{loop_label}"));
        self.line(&format!("array.clone.loop{loop_label}:"));
        let index = self.temp();
        self.line(&format!(
            "  %{index} = phi {usize_ty} [ 0, %array.clone.recorded{data_recorded} ], [ %array.clone.next.index{next_label}, %array.clone.next{next_label} ]"
        ));
        let in_bounds = self.temp();
        self.line(&format!(
            "  %{in_bounds} = icmp ult {usize_ty} %{index}, %{capacity}"
        ));
        self.line(&format!(
            "  br i1 %{in_bounds}, label %array.clone.inspect{inspect_label}, label %array.clone.done{done_label}"
        ));
        self.line(&format!("array.clone.inspect{inspect_label}:"));
        let flag_address = self.temp();
        let flag = self.temp();
        let initialized = self.temp();
        self.line(&format!(
            "  %{flag_address} = getelementptr inbounds i8, ptr %{source_flags}, {usize_ty} %{index}"
        ));
        self.line(&format!("  %{flag} = load i8, ptr %{flag_address}"));
        self.line(&format!("  %{initialized} = icmp ne i8 %{flag}, 0"));
        self.line(&format!(
            "  br i1 %{initialized}, label %array.clone.value{clone_label}, label %array.clone.next{next_label}"
        ));
        self.line(&format!("array.clone.value{clone_label}:"));
        let source_slot = self.temp();
        let source_value = self.temp();
        self.line(&format!(
            "  %{source_slot} = getelementptr inbounds {element_ty}, ptr %{source_data}, {usize_ty} %{index}"
        ));
        self.line(&format!(
            "  %{source_value} = load {element_ty}, ptr %{source_slot}"
        ));
        let cloned_value = self.emit_clone_effect_snapshot_value(
            element_type,
            &format!("%{source_value}"),
            function,
            context,
        )?;
        let clone_slot = self.temp();
        let clone_flag = self.temp();
        self.line(&format!(
            "  %{clone_slot} = getelementptr inbounds {element_ty}, ptr %{clone_data}, {usize_ty} %{index}"
        ));
        self.line(&format!(
            "  store {element_ty} {cloned_value}, ptr %{clone_slot}"
        ));
        self.line(&format!(
            "  %{clone_flag} = getelementptr inbounds i8, ptr %{clone_flags}, {usize_ty} %{index}"
        ));
        self.line(&format!("  store i8 1, ptr %{clone_flag}"));
        self.line(&format!("  br label %array.clone.next{next_label}"));
        self.line(&format!("array.clone.next{next_label}:"));
        self.line(&format!(
            "  %array.clone.next.index{next_label} = add {usize_ty} %{index}, 1"
        ));
        self.line(&format!("  br label %array.clone.loop{loop_label}"));
        self.line(&format!("array.clone.done{done_label}:"));
        Ok(format!("%{clone}"))
    }

    fn emit_clone_resumption_wrapper(
        &mut self,
        resumption_type: TypeId,
        source: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let result_slot = self.temp();
        let existing = self.temp();
        let found = self.temp();
        let reuse_label = self.temp();
        let clone_label = self.temp();
        let done_label = self.temp();
        self.line(&format!("  %{result_slot} = alloca ptr"));
        self.line(&format!(
            "  %{existing} = call ptr @g1_snapshot_lookup_exact(ptr {context}, ptr {source})"
        ));
        self.line(&format!("  %{found} = icmp ne ptr %{existing}, null"));
        self.line(&format!(
            "  br i1 %{found}, label %resumption.snapshot.reuse{reuse_label}, label %resumption.snapshot.clone{clone_label}"
        ));
        self.line(&format!("resumption.snapshot.reuse{reuse_label}:"));
        self.emit_retain_resumption(&format!("%{existing}"));
        self.line(&format!("  store ptr %{existing}, ptr %{result_slot}"));
        self.line(&format!("  br label %resumption.snapshot.done{done_label}"));
        self.line(&format!("resumption.snapshot.clone{clone_label}:"));
        let cloned =
            self.emit_clone_resumption_wrapper_fresh(resumption_type, source, function, context)?;
        self.line(&format!("  store ptr {cloned}, ptr %{result_slot}"));
        self.line(&format!("  br label %resumption.snapshot.done{done_label}"));
        self.line(&format!("resumption.snapshot.done{done_label}:"));
        let result = self.temp();
        self.line(&format!("  %{result} = load ptr, ptr %{result_slot}"));
        Ok(format!("%{result}"))
    }

    fn emit_clone_resumption_wrapper_fresh(
        &mut self,
        resumption_type: TypeId,
        source: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let fields = (0..5)
            .map(|field| {
                let address = self.temp();
                let value = self.temp();
                self.line(&format!(
                    "  %{address} = getelementptr inbounds %g1.resumption, ptr {source}, i32 0, i32 {field}"
                ));
                self.line(&format!("  %{value} = load ptr, ptr %{address}"));
                format!("%{value}")
            })
            .collect::<Vec<_>>();
        let [top, _, resume_slot, resume_init, handler] = fields.as_slice() else {
            unreachable!()
        };
        let usize_ty = format!("i{}", self.pointer_width());
        let size = self.emit_array_element_size("%g1.resumption");
        let cloned = self.temp();
        let failed = self.temp();
        self.line(&format!(
            "  %{cloned} = call ptr @malloc({usize_ty} {size})"
        ));
        self.line(&format!("  %{failed} = icmp eq ptr %{cloned}, null"));
        self.emit_runtime_fault_if(failed, RUNTIME_FAULT_ALLOCATION_LIMIT);
        for field in 0..5 {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.resumption, ptr %{cloned}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store ptr null, ptr %{address}"));
        }
        let references_address = self.temp();
        self.line(&format!(
            "  %{references_address} = getelementptr inbounds %g1.resumption, ptr %{cloned}, i32 0, i32 5"
        ));
        self.line(&format!("  store i64 1, ptr %{references_address}"));
        let preserve_address = self.temp();
        self.line(&format!(
            "  %{preserve_address} = getelementptr inbounds %g1.resumption, ptr %{cloned}, i32 0, i32 6"
        ));
        self.line(&format!("  store i1 true, ptr %{preserve_address}"));
        self.line(&format!(
            "  call void @g1_snapshot_record(ptr {context}, ptr {source}, {usize_ty} {size}, ptr %{cloned}, ptr null)"
        ));
        let cloned_top = self.temp();
        let cloned_bottom = self.temp();
        self.line(&format!(
            "  %{cloned_top} = call ptr @g1_effect_clone_chain_owners(ptr {top}, ptr {context})"
        ));
        self.line(&format!(
            "  %{cloned_bottom} = call ptr @g1_effect_chain_bottom(ptr %{cloned_top})"
        ));
        let mut rebased = Vec::with_capacity(2);
        for pointer in [resume_slot, resume_init] {
            let present = self.temp();
            let rebase_label = self.temp();
            let null_label = self.temp();
            let done_label = self.temp();
            self.line(&format!("  %{present} = icmp ne ptr {pointer}, null"));
            self.line(&format!(
                "  br i1 %{present}, label %resumption.clone.rebase{rebase_label}, label %resumption.clone.null{null_label}"
            ));
            self.line(&format!("resumption.clone.rebase{rebase_label}:"));
            let pointer_integer = self.temp();
            let top_integer = self.temp();
            let offset = self.temp();
            let cloned_pointer = self.temp();
            self.line(&format!(
                "  %{pointer_integer} = ptrtoint ptr {pointer} to {usize_ty}"
            ));
            self.line(&format!(
                "  %{top_integer} = ptrtoint ptr {top} to {usize_ty}"
            ));
            self.line(&format!(
                "  %{offset} = sub {usize_ty} %{pointer_integer}, %{top_integer}"
            ));
            self.line(&format!(
                "  %{cloned_pointer} = getelementptr inbounds i8, ptr %{cloned_top}, {usize_ty} %{offset}"
            ));
            self.line(&format!("  br label %resumption.clone.done{done_label}"));
            self.line(&format!("resumption.clone.null{null_label}:"));
            self.line(&format!("  br label %resumption.clone.done{done_label}"));
            self.line(&format!("resumption.clone.done{done_label}:"));
            let final_pointer = self.temp();
            self.line(&format!(
                "  %{final_pointer} = phi ptr [ %{cloned_pointer}, %resumption.clone.rebase{rebase_label} ], [ null, %resumption.clone.null{null_label} ]"
            ));
            rebased.push(format!("%{final_pointer}"));
        }
        let handler_type = self.resumption_handler_runtime_type(function, resumption_type)?;
        let Type::Handler { capture_type, .. } = self.runtime_type(handler_type)?.clone() else {
            unreachable!()
        };
        let cloned_handler = self.emit_clone_effect_snapshot_handler(
            handler_type,
            capture_type,
            handler,
            function,
            context,
        )?;
        for (field, value) in [
            (0, format!("%{cloned_top}")),
            (1, format!("%{cloned_bottom}")),
            (2, rebased[0].clone()),
            (3, rebased[1].clone()),
            (4, cloned_handler),
        ] {
            let address = self.temp();
            self.line(&format!(
                "  %{address} = getelementptr inbounds %g1.resumption, ptr %{cloned}, i32 0, i32 {field}"
            ));
            self.line(&format!("  store ptr {value}, ptr %{address}"));
        }
        Ok(format!("%{cloned}"))
    }

    fn emit_fix_effect_snapshot_value(
        &mut self,
        ty: TypeId,
        value: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        match self.runtime_type(ty)?.clone() {
            Type::RefShared { .. } => {
                let remapped = self.temp();
                self.line(&format!(
                    "  %{remapped} = call ptr @g1_snapshot_remap(ptr {context}, ptr {value})"
                ));
                Ok(format!("%{remapped}"))
            }
            Type::RefUnique { .. } => {
                // Unique loans are not valid snapshot state. Keep this check on
                // the initialized path so functions may still use short-lived
                // unique borrows before or after a suspension.
                self.line("  call void @llvm.trap()");
                Ok(value.to_owned())
            }
            Type::BindingPack { payload_type, .. } => {
                self.emit_fix_effect_snapshot_value(payload_type, value, function, context)
            }
            Type::Tuple { .. } | Type::Struct { .. } => {
                let fields = self.runtime_aggregate_fields(ty)?;
                self.emit_fix_effect_snapshot_aggregate(ty, value, &fields, function, context)
            }
            Type::Array { element } => {
                self.emit_fix_effect_snapshot_array(element, value, function, context)?;
                Ok(value.to_owned())
            }
            Type::Enum { .. } => {
                self.emit_transform_effect_snapshot_enum(ty, value, function, context, false)
            }
            _ => Ok(value.to_owned()),
        }
    }

    fn emit_snapshot_capture_fix_callbacks(
        &mut self,
        reachable: &[usize],
    ) -> Result<(), Vec<Diagnostic>> {
        let Some(&function_index) = reachable.first() else {
            return Ok(());
        };
        let function = self.phases.mir.functions[function_index].clone();
        let capture_types = self
            .snapshot_capture_fix_types
            .iter()
            .copied()
            .collect::<Vec<_>>();
        for capture_type in capture_types {
            let capture_ty = self.llvm_type(capture_type)?;
            self.line(&format!(
                "define internal void @g1_snapshot_fix_capture_t{capture_type}(ptr %source, ptr %clone, ptr %context) {{"
            ));
            self.line("entry:");
            let value = self.temp();
            self.line(&format!("  %{value} = load {capture_ty}, ptr %clone"));
            let fixed = self.emit_fix_effect_snapshot_value(
                capture_type,
                &format!("%{value}"),
                &function,
                "%context",
            )?;
            self.line(&format!("  store {capture_ty} {fixed}, ptr %clone"));
            self.line("  ret void");
            self.line("}");
            self.line("");
        }
        Ok(())
    }

    fn emit_transform_effect_snapshot_enum(
        &mut self,
        ty: TypeId,
        value: &str,
        function: &mir::Function,
        context: &str,
        clone_owners: bool,
    ) -> Result<String, Vec<Diagnostic>> {
        let Type::Enum { variants, .. } = self.runtime_type(ty)?.clone() else {
            unreachable!()
        };
        let enum_ty = self.llvm_type(ty)?;
        let tag = self.temp();
        let trap = self.temp();
        let join = self.temp();
        let cases = (0..variants.len()).map(|_| self.temp()).collect::<Vec<_>>();
        self.line(&format!("  %{tag} = extractvalue {enum_ty} {value}, 0"));
        self.line(&format!(
            "  switch i32 %{tag}, label %enum.snapshot.trap{trap} ["
        ));
        for (variant, label) in cases.iter().enumerate() {
            self.line(&format!(
                "    i32 {variant}, label %enum.snapshot.case{label}"
            ));
        }
        self.line("  ]");
        self.line(&format!("enum.snapshot.trap{trap}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        let mut incoming = Vec::with_capacity(variants.len());
        for (variant, label) in variants.iter().zip(cases) {
            self.line(&format!("enum.snapshot.case{label}:"));
            let mut rebuilt = value.to_owned();
            for (field_index, field) in variant.fields.iter().enumerate() {
                let unpacked =
                    self.emit_unpack_enum_field(ty, &rebuilt, field_index as u32, field.ty)?;
                let transformed = if clone_owners {
                    self.emit_clone_effect_snapshot_value(field.ty, &unpacked, function, context)?
                } else {
                    self.emit_fix_effect_snapshot_value(field.ty, &unpacked, function, context)?
                };
                let words = self.enum_slot_words(ty, field_index as u32)?;
                let slot_ty = format!("[{words} x i128]");
                let slot = self.temp();
                self.line(&format!("  %{slot} = alloca {slot_ty}"));
                self.line(&format!(
                    "  store {slot_ty} zeroinitializer, ptr %{slot}, align 1"
                ));
                self.line(&format!(
                    "  store {} {transformed}, ptr %{slot}, align 1",
                    self.llvm_type(field.ty)?
                ));
                let packed = self.temp();
                self.line(&format!(
                    "  %{packed} = load {slot_ty}, ptr %{slot}, align 1"
                ));
                let inserted = self.temp();
                self.line(&format!(
                    "  %{inserted} = insertvalue {enum_ty} {rebuilt}, {slot_ty} %{packed}, {}",
                    field_index + 1
                ));
                rebuilt = format!("%{inserted}");
            }
            let case_done = self.temp();
            self.line(&format!("  br label %enum.snapshot.case.done{case_done}"));
            self.line(&format!("enum.snapshot.case.done{case_done}:"));
            self.line(&format!("  br label %enum.snapshot.join{join}"));
            incoming.push((rebuilt, case_done));
        }
        self.line(&format!("enum.snapshot.join{join}:"));
        let result = self.temp();
        let arms = incoming
            .into_iter()
            .map(|(incoming, label)| format!("[ {incoming}, %enum.snapshot.case.done{label} ]"))
            .collect::<Vec<_>>()
            .join(", ");
        self.line(&format!("  %{result} = phi {enum_ty} {arms}"));
        Ok(format!("%{result}"))
    }

    fn emit_fix_effect_snapshot_aggregate(
        &mut self,
        aggregate_type: TypeId,
        aggregate: &str,
        fields: &[TypeId],
        function: &mir::Function,
        context: &str,
    ) -> Result<String, Vec<Diagnostic>> {
        let aggregate_ty = self.llvm_type(aggregate_type)?;
        let mut rebuilt = aggregate.to_owned();
        for (index, field_type) in fields.iter().copied().enumerate() {
            let extracted = self.temp();
            self.line(&format!(
                "  %{extracted} = extractvalue {aggregate_ty} {rebuilt}, {index}"
            ));
            let fixed = self.emit_fix_effect_snapshot_value(
                field_type,
                &format!("%{extracted}"),
                function,
                context,
            )?;
            let inserted = self.temp();
            self.line(&format!(
                "  %{inserted} = insertvalue {aggregate_ty} {rebuilt}, {} {fixed}, {index}",
                self.llvm_type(field_type)?
            ));
            rebuilt = format!("%{inserted}");
        }
        Ok(rebuilt)
    }

    fn emit_fix_effect_snapshot_array(
        &mut self,
        element_type: TypeId,
        array: &str,
        function: &mir::Function,
        context: &str,
    ) -> Result<(), Vec<Diagnostic>> {
        let usize_ty = format!("i{}", self.pointer_width());
        let element_ty = self.llvm_type(element_type)?;
        let capacity_address = self.temp();
        let capacity = self.temp();
        let data_address = self.temp();
        let data = self.temp();
        let flags_address = self.temp();
        let flags = self.temp();
        self.line(&format!(
            "  %{capacity_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{capacity} = load {usize_ty}, ptr %{capacity_address}"
        ));
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 3"
        ));
        self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
        self.line(&format!(
            "  %{flags_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
        ));
        self.line(&format!("  %{flags} = load ptr, ptr %{flags_address}"));
        let loop_label = self.temp();
        let inspect_label = self.temp();
        let fix_label = self.temp();
        let next_label = self.temp();
        let done_label = self.temp();
        let index_address = self.temp();
        self.line(&format!("  %{index_address} = alloca {usize_ty}"));
        self.line(&format!("  store {usize_ty} 0, ptr %{index_address}"));
        self.line(&format!("  br label %array.fix.loop{loop_label}"));
        self.line(&format!("array.fix.loop{loop_label}:"));
        let index = self.temp();
        self.line(&format!(
            "  %{index} = load {usize_ty}, ptr %{index_address}"
        ));
        let in_bounds = self.temp();
        self.line(&format!(
            "  %{in_bounds} = icmp ult {usize_ty} %{index}, %{capacity}"
        ));
        self.line(&format!(
            "  br i1 %{in_bounds}, label %array.fix.inspect{inspect_label}, label %array.fix.done{done_label}"
        ));
        self.line(&format!("array.fix.inspect{inspect_label}:"));
        let flag_address = self.temp();
        let flag = self.temp();
        let initialized = self.temp();
        self.line(&format!(
            "  %{flag_address} = getelementptr inbounds i8, ptr %{flags}, {usize_ty} %{index}"
        ));
        self.line(&format!("  %{flag} = load i8, ptr %{flag_address}"));
        self.line(&format!("  %{initialized} = icmp ne i8 %{flag}, 0"));
        self.line(&format!(
            "  br i1 %{initialized}, label %array.fix.value{fix_label}, label %array.fix.next{next_label}"
        ));
        self.line(&format!("array.fix.value{fix_label}:"));
        let slot = self.temp();
        let current = self.temp();
        self.line(&format!(
            "  %{slot} = getelementptr inbounds {element_ty}, ptr %{data}, {usize_ty} %{index}"
        ));
        self.line(&format!("  %{current} = load {element_ty}, ptr %{slot}"));
        let fixed = self.emit_fix_effect_snapshot_value(
            element_type,
            &format!("%{current}"),
            function,
            context,
        )?;
        self.line(&format!("  store {element_ty} {fixed}, ptr %{slot}"));
        self.line(&format!("  br label %array.fix.next{next_label}"));
        self.line(&format!("array.fix.next{next_label}:"));
        let next = self.temp();
        self.line(&format!("  %{next} = add {usize_ty} %{index}, 1"));
        self.line(&format!("  store {usize_ty} %{next}, ptr %{index_address}"));
        self.line(&format!("  br label %array.fix.loop{loop_label}"));
        self.line(&format!("array.fix.done{done_label}:"));
        Ok(())
    }

    fn emit_clone_masked_effect_snapshot_fields(
        &mut self,
        function: &mir::Function,
        aggregate_type: TypeId,
        frame_type: &str,
        frame: &str,
        aggregate_address: &str,
        flags_field: usize,
        fields: &[AggregateFieldLayout],
        context: &str,
    ) -> Result<(), Vec<Diagnostic>> {
        let aggregate_ty = self.llvm_type(aggregate_type)?;
        for field in fields {
            let flag_address = self.temp();
            let flag = self.temp();
            let present = self.temp();
            let visit_label = self.temp();
            let done_label = self.temp();
            self.line(&format!(
                "  %{flag_address} = getelementptr inbounds {frame_type}, ptr {frame}, i32 0, i32 {flags_field}, i32 {}",
                field.owned_mask_index
            ));
            self.line(&format!("  %{flag} = load i8, ptr %{flag_address}"));
            self.line(&format!("  %{present} = icmp ne i8 %{flag}, 0"));
            self.line(&format!(
                "  br i1 %{present}, label %frame.field.clone{visit_label}, label %frame.field.cloned{done_label}"
            ));
            self.line(&format!("frame.field.clone{visit_label}:"));
            let current = self.temp();
            let extracted = self.temp();
            self.line(&format!(
                "  %{current} = load {aggregate_ty}, ptr {aggregate_address}"
            ));
            self.line(&format!(
                "  %{extracted} = extractvalue {aggregate_ty} %{current}, {}",
                field.physical_index
            ));
            let cloned = self.emit_clone_effect_snapshot_value(
                field.runtime_type,
                &format!("%{extracted}"),
                function,
                context,
            )?;
            let inserted = self.temp();
            self.line(&format!(
                "  %{inserted} = insertvalue {aggregate_ty} %{current}, {} {cloned}, {}",
                self.llvm_type(field.runtime_type)?,
                field.physical_index
            ));
            self.line(&format!(
                "  store {aggregate_ty} %{inserted}, ptr {aggregate_address}"
            ));
            self.line(&format!("  br label %frame.field.cloned{done_label}"));
            self.line(&format!("frame.field.cloned{done_label}:"));
        }
        Ok(())
    }

    fn emit_fix_masked_effect_snapshot_fields(
        &mut self,
        function: &mir::Function,
        aggregate_type: TypeId,
        frame_type: &str,
        frame: &str,
        aggregate_address: &str,
        flags_field: usize,
        fields: &[AggregateFieldLayout],
        context: &str,
    ) -> Result<(), Vec<Diagnostic>> {
        let aggregate_ty = self.llvm_type(aggregate_type)?;
        for field in fields {
            let flag_address = self.temp();
            let flag = self.temp();
            let present = self.temp();
            let fix_label = self.temp();
            let done_label = self.temp();
            self.line(&format!(
                "  %{flag_address} = getelementptr inbounds {frame_type}, ptr {frame}, i32 0, i32 {flags_field}, i32 {}",
                field.owned_mask_index
            ));
            self.line(&format!("  %{flag} = load i8, ptr %{flag_address}"));
            self.line(&format!("  %{present} = icmp ne i8 %{flag}, 0"));
            self.line(&format!(
                "  br i1 %{present}, label %frame.field.fix{fix_label}, label %frame.field.fixed{done_label}"
            ));
            self.line(&format!("frame.field.fix{fix_label}:"));
            let current = self.temp();
            let extracted = self.temp();
            self.line(&format!(
                "  %{current} = load {aggregate_ty}, ptr {aggregate_address}"
            ));
            self.line(&format!(
                "  %{extracted} = extractvalue {aggregate_ty} %{current}, {}",
                field.physical_index
            ));
            let fixed = self.emit_fix_effect_snapshot_value(
                field.runtime_type,
                &format!("%{extracted}"),
                function,
                context,
            )?;
            let inserted = self.temp();
            self.line(&format!(
                "  %{inserted} = insertvalue {aggregate_ty} %{current}, {} {fixed}, {}",
                self.llvm_type(field.runtime_type)?,
                field.physical_index
            ));
            self.line(&format!(
                "  store {aggregate_ty} %{inserted}, ptr {aggregate_address}"
            ));
            self.line(&format!("  br label %frame.field.fixed{done_label}"));
            self.line(&format!("frame.field.fixed{done_label}:"));
        }
        Ok(())
    }

    fn emit_retain_handler(&mut self, handler: &str) {
        let references_address = self.temp();
        let references = self.temp();
        let next = self.temp();
        self.line(&format!(
            "  %{references_address} = getelementptr inbounds %g1.handler, ptr {handler}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{references} = load i64, ptr %{references_address}"
        ));
        self.line(&format!("  %{next} = add i64 %{references}, 1"));
        self.line(&format!("  store i64 %{next}, ptr %{references_address}"));
    }

    fn emit_retain_capture(&mut self, capture: &str) {
        let references_address = self.temp();
        let references = self.temp();
        let next = self.temp();
        self.line(&format!(
            "  %{references_address} = getelementptr inbounds %g1.capture, ptr {capture}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{references} = load i64, ptr %{references_address}"
        ));
        self.line(&format!("  %{next} = add i64 %{references}, 1"));
        self.line(&format!("  store i64 %{next}, ptr %{references_address}"));
    }

    fn emit_retain_resumption(&mut self, resumption: &str) {
        let references_address = self.temp();
        let references = self.temp();
        let overflow = self.temp();
        let next = self.temp();
        self.line(&format!(
            "  %{references_address} = getelementptr inbounds %g1.resumption, ptr {resumption}, i32 0, i32 5"
        ));
        self.line(&format!(
            "  %{references} = load i64, ptr %{references_address}"
        ));
        self.line(&format!("  %{overflow} = icmp eq i64 %{references}, -1"));
        self.emit_trap_if(overflow);
        self.line(&format!("  %{next} = add i64 %{references}, 1"));
        self.line(&format!("  store i64 %{next}, ptr %{references_address}"));
    }

    fn emit_masked_aggregate_fields(
        &mut self,
        function: &mir::Function,
        aggregate_type: TypeId,
        aggregate: &str,
        frame_type: &str,
        frame: &str,
        flags_field: usize,
        fields: &[AggregateFieldLayout],
        retain: bool,
    ) -> Result<(), Vec<Diagnostic>> {
        let aggregate_ty = self.llvm_type(aggregate_type)?;
        let indices = if retain {
            (0..fields.len()).collect::<Vec<_>>()
        } else {
            (0..fields.len()).rev().collect::<Vec<_>>()
        };
        for index in indices {
            let field = fields[index];
            let flag_address = self.temp();
            let flag = self.temp();
            let present = self.temp();
            let visit_label = self.temp();
            let done_label = self.temp();
            self.line(&format!(
                "  %{flag_address} = getelementptr inbounds {frame_type}, ptr {frame}, i32 0, i32 {flags_field}, i32 {}",
                field.owned_mask_index
            ));
            self.line(&format!("  %{flag} = load i8, ptr %{flag_address}"));
            self.line(&format!("  %{present} = icmp ne i8 %{flag}, 0"));
            self.line(&format!(
                "  br i1 %{present}, label %frame.field.visit{visit_label}, label %frame.field.done{done_label}"
            ));
            self.line(&format!("frame.field.visit{visit_label}:"));
            let extracted = self.temp();
            self.line(&format!(
                "  %{extracted} = extractvalue {aggregate_ty} {aggregate}, {}",
                field.physical_index
            ));
            if retain {
                self.emit_retain(field.runtime_type, &format!("%{extracted}"), function)?;
            } else {
                self.emit_destroy(field.runtime_type, &format!("%{extracted}"), function)?;
            }
            self.line(&format!("  br label %frame.field.done{done_label}"));
            self.line(&format!("frame.field.done{done_label}:"));
        }
        Ok(())
    }

    fn emit_destroy(
        &mut self,
        ty: TypeId,
        value: &str,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let value = if let Some(glue) = self
            .phases
            .artifact
            .drop_glue
            .iter()
            .find(|glue| glue.ty == ty)
        {
            let hook = self
                .phases
                .mir
                .functions
                .get(glue.function as usize)
                .ok_or_else(|| vec![unsupported(function, "missing custom drop hook")])?;
            if hook.params.len() != 1
                || !matches!(
                    self.runtime_type(hook.params[0])?,
                    Type::RefUnique { referent } if *referent == ty
                )
                || !matches!(self.runtime_type(hook.result)?, Type::Unit)
            {
                return Err(vec![unsupported(
                    function,
                    "custom drop hook with an incompatible signature",
                )]);
            }
            let llvm_ty = self.llvm_type(ty)?;
            let slot = self.temp();
            self.line(&format!("  %{slot} = alloca {llvm_ty}"));
            self.line(&format!("  store {llvm_ty} {value}, ptr %{slot}"));
            self.line(&format!("  call void @g1_f{}(ptr %{slot})", glue.function));
            let reloaded = self.temp();
            self.line(&format!("  %{reloaded} = load {llvm_ty}, ptr %{slot}"));
            format!("%{reloaded}")
        } else {
            value.to_owned()
        };
        match self.runtime_type(ty)?.clone() {
            Type::Text | Type::Bytes => {
                self.line(&format!("  call void @g1_bytes_release(ptr {value})"));
            }
            Type::Callable { capture_type, .. } => {
                self.emit_destroy_callable(&value, capture_type, function)?;
            }
            Type::Handler { capture_type, .. } => {
                self.emit_destroy_handler(&value, capture_type, function)?;
            }
            Type::Resumption { .. } => {
                self.emit_release_resumption(&value, ty, function)?;
            }
            Type::BindingPack { payload_type, .. } => {
                self.emit_destroy(payload_type, &value, function)?;
            }
            Type::Array { element } => {
                self.ensure_plain_array_element(element, function)?;
                self.emit_destroy_array_elements(&value, element, function)?;
                self.line(&format!("  call void @g1_array_free(ptr {value})"));
            }
            Type::Tuple { .. } | Type::Struct { .. } => {
                let aggregate_ty = self.llvm_type(ty)?;
                for field in self
                    .runtime_aggregate_field_layout(ty, 0)?
                    .into_iter()
                    .rev()
                {
                    if self.type_needs_destroy(field.runtime_type, &mut BTreeSet::new())? {
                        let extracted = self.temp();
                        self.line(&format!(
                            "  %{extracted} = extractvalue {aggregate_ty} {value}, {}",
                            field.physical_index
                        ));
                        self.emit_destroy(field.runtime_type, &format!("%{extracted}"), function)?;
                    }
                }
            }
            Type::Enum { .. } if self.type_needs_destroy(ty, &mut BTreeSet::new())? => {
                self.emit_visit_enum_payloads(ty, &value, false, function)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn emit_destroy_callable(
        &mut self,
        callable: &str,
        capture_type: TypeId,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 0"
        ));
        let count = self.temp();
        self.line(&format!("  %{count} = load i64, ptr %{count_address}"));
        let last = self.temp();
        self.line(&format!("  %{last} = icmp eq i64 %{count}, 1"));
        let destroy_label = self.temp();
        let decrement_label = self.temp();
        let done_label = self.temp();
        self.line(&format!(
            "  br i1 %{last}, label %callable.destroy{destroy_label}, label %callable.decrement{decrement_label}"
        ));
        self.line(&format!("callable.decrement{decrement_label}:"));
        let next = self.temp();
        self.line(&format!("  %{next} = sub i64 %{count}, 1"));
        self.line(&format!("  store i64 %{next}, ptr %{count_address}"));
        self.line(&format!("  br label %callable.done{done_label}"));
        self.line(&format!("callable.destroy{destroy_label}:"));
        let capture_address = self.temp();
        self.line(&format!(
            "  %{capture_address} = getelementptr inbounds %g1.callable, ptr {callable}, i32 0, i32 2"
        ));
        let capture_handle = self.temp();
        self.line(&format!(
            "  %{capture_handle} = load ptr, ptr %{capture_address}"
        ));
        self.emit_release_capture(&format!("%{capture_handle}"), capture_type, function)?;
        self.line(&format!("  call void @free(ptr {callable})"));
        self.line(&format!("  br label %callable.done{done_label}"));
        self.line(&format!("callable.done{done_label}:"));
        Ok(())
    }

    fn emit_release_capture(
        &mut self,
        capture: &str,
        capture_type: TypeId,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let count_address = self.temp();
        self.line(&format!(
            "  %{count_address} = getelementptr inbounds %g1.capture, ptr {capture}, i32 0, i32 0"
        ));
        let count = self.temp();
        self.line(&format!("  %{count} = load i64, ptr %{count_address}"));
        let last = self.temp();
        self.line(&format!("  %{last} = icmp eq i64 %{count}, 1"));
        let decrement_label = self.temp();
        let destroy_label = self.temp();
        let empty_label = self.temp();
        let release_label = self.temp();
        let done_label = self.temp();
        self.line(&format!(
            "  br i1 %{last}, label %capture.destroy{destroy_label}, label %capture.decrement{decrement_label}"
        ));
        self.line(&format!("capture.decrement{decrement_label}:"));
        let next = self.temp();
        self.line(&format!("  %{next} = sub i64 %{count}, 1"));
        self.line(&format!("  store i64 %{next}, ptr %{count_address}"));
        self.line(&format!("  br label %capture.done{done_label}"));
        self.line(&format!("capture.destroy{destroy_label}:"));
        let data_address = self.temp();
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.capture, ptr {capture}, i32 0, i32 1"
        ));
        let data = self.temp();
        self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
        let empty = self.temp();
        self.line(&format!("  %{empty} = icmp eq ptr %{data}, null"));
        self.line(&format!(
            "  br i1 %{empty}, label %capture.empty{empty_label}, label %capture.release{release_label}"
        ));
        self.line(&format!("capture.release{release_label}:"));
        let capture_ty = self.llvm_type(capture_type)?;
        let capture_value = self.temp();
        self.line(&format!(
            "  %{capture_value} = load {capture_ty}, ptr %{data}"
        ));
        self.emit_destroy(capture_type, &format!("%{capture_value}"), function)?;
        self.line(&format!("  call void @free(ptr %{data})"));
        self.line(&format!("  br label %capture.empty{empty_label}"));
        self.line(&format!("capture.empty{empty_label}:"));
        self.line(&format!("  call void @free(ptr {capture})"));
        self.line(&format!("  br label %capture.done{done_label}"));
        self.line(&format!("capture.done{done_label}:"));
        Ok(())
    }

    fn emit_destroy_handler(
        &mut self,
        handler: &str,
        capture_type: TypeId,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let references_address = self.temp();
        let references = self.temp();
        let last = self.temp();
        let destroy_label = self.temp();
        let decrement_label = self.temp();
        let released_label = self.temp();
        self.line(&format!(
            "  %{references_address} = getelementptr inbounds %g1.handler, ptr {handler}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{references} = load i64, ptr %{references_address}"
        ));
        self.line(&format!("  %{last} = icmp eq i64 %{references}, 1"));
        self.line(&format!(
            "  br i1 %{last}, label %handler.destroy{destroy_label}, label %handler.decrement{decrement_label}"
        ));
        self.line(&format!("handler.decrement{decrement_label}:"));
        let next = self.temp();
        self.line(&format!("  %{next} = sub i64 %{references}, 1"));
        self.line(&format!("  store i64 %{next}, ptr %{references_address}"));
        self.line(&format!("  br label %handler.released{released_label}"));
        self.line(&format!("handler.destroy{destroy_label}:"));
        let clause_types = self.runtime_aggregate_fields(capture_type)?;
        let clauses_address = self.temp();
        self.line(&format!(
            "  %{clauses_address} = getelementptr inbounds %g1.handler, ptr {handler}, i32 0, i32 3"
        ));
        let clauses = self.temp();
        self.line(&format!("  %{clauses} = load ptr, ptr %{clauses_address}"));
        let usize_ty = format!("i{}", self.pointer_width());
        for (index, clause_type) in clause_types.into_iter().enumerate().rev() {
            let slot = self.temp();
            self.line(&format!(
                "  %{slot} = getelementptr inbounds ptr, ptr %{clauses}, {usize_ty} {index}"
            ));
            let clause = self.temp();
            self.line(&format!("  %{clause} = load ptr, ptr %{slot}"));
            let missing = self.temp();
            let destroy_label = self.temp();
            let done_label = self.temp();
            self.line(&format!("  %{missing} = icmp eq ptr %{clause}, null"));
            self.line(&format!(
                "  br i1 %{missing}, label %handler.clause.done{done_label}, label %handler.clause.destroy{destroy_label}"
            ));
            self.line(&format!("handler.clause.destroy{destroy_label}:"));
            self.emit_destroy(clause_type, &format!("%{clause}"), function)?;
            self.line(&format!("  br label %handler.clause.done{done_label}"));
            self.line(&format!("handler.clause.done{done_label}:"));
        }
        self.line(&format!("  call void @free(ptr %{clauses})"));
        self.line(&format!("  call void @free(ptr {handler})"));
        self.line(&format!("  br label %handler.released{released_label}"));
        self.line(&format!("handler.released{released_label}:"));
        Ok(())
    }

    fn emit_visit_enum_payloads(
        &mut self,
        ty: TypeId,
        value: &str,
        retain: bool,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        let Type::Enum { variants, .. } = self.runtime_type(ty)?.clone() else {
            return Err(vec![unsupported(
                function,
                "owned enum traversal on a non-enum value",
            )]);
        };
        let enum_ty = self.llvm_type(ty)?;
        let tag = self.temp();
        self.line(&format!("  %{tag} = extractvalue {enum_ty} {value}, 0"));
        let traversal = self.temp();
        let trap = self.temp();
        let done = self.temp();
        let cases = (0..variants.len()).map(|_| self.temp()).collect::<Vec<_>>();
        self.line(&format!(
            "  switch i32 %{tag}, label %enum.owned.trap{trap} ["
        ));
        for (variant, label) in cases.iter().enumerate() {
            self.line(&format!(
                "    i32 {variant}, label %enum.owned.case{traversal}.{label}"
            ));
        }
        self.line("  ]");
        self.line(&format!("enum.owned.trap{trap}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        for (variant, label) in variants.iter().zip(cases) {
            self.line(&format!("enum.owned.case{traversal}.{label}:"));
            let fields = if retain {
                variant.fields.iter().enumerate().collect::<Vec<_>>()
            } else {
                variant.fields.iter().enumerate().rev().collect::<Vec<_>>()
            };
            for (field_index, field) in fields {
                let owned = if retain {
                    self.type_contains_byte_object(field.ty, &mut BTreeSet::new())?
                        || self.type_contains_array(field.ty, &mut BTreeSet::new())?
                        || self.type_contains_callable(field.ty, &mut BTreeSet::new())?
                        || self.type_contains_handler(field.ty, &mut BTreeSet::new())?
                        || self.type_contains_resumption(field.ty, &mut BTreeSet::new())?
                } else {
                    self.type_needs_destroy(field.ty, &mut BTreeSet::new())?
                };
                if !owned {
                    continue;
                }
                let field_value =
                    self.emit_unpack_enum_field(ty, value, field_index as u32, field.ty)?;
                if retain {
                    self.emit_retain(field.ty, &field_value, function)?;
                } else {
                    self.emit_destroy(field.ty, &field_value, function)?;
                }
            }
            self.line(&format!("  br label %enum.owned.done{done}"));
        }
        self.line(&format!("enum.owned.done{done}:"));
        Ok(())
    }

    fn emit_unpack_enum_field(
        &mut self,
        enum_type: TypeId,
        value: &str,
        field: u32,
        field_type: TypeId,
    ) -> Result<String, Vec<Diagnostic>> {
        let enum_ty = self.llvm_type(enum_type)?;
        let words = self.enum_slot_words(enum_type, field)?;
        let slot_ty = format!("[{words} x i128]");
        let packed = self.temp();
        self.line(&format!(
            "  %{packed} = extractvalue {enum_ty} {value}, {}",
            field + 1
        ));
        let slot = self.temp();
        self.line(&format!("  %{slot} = alloca {slot_ty}"));
        self.line(&format!(
            "  store {slot_ty} %{packed}, ptr %{slot}, align 1"
        ));
        let field_ty = self.llvm_type(field_type)?;
        let unpacked = self.temp();
        self.line(&format!(
            "  %{unpacked} = load {field_ty}, ptr %{slot}, align 1"
        ));
        Ok(format!("%{unpacked}"))
    }

    fn release_byte_operands(
        &mut self,
        function: &mir::Function,
        operands: &[mir::Operand],
        loaded: &[(String, String)],
    ) -> Result<(), Vec<Diagnostic>> {
        for (operand, (_, value)) in operands.iter().zip(loaded) {
            let ty = self.register_runtime_type(function, operand.register)?;
            if self.is_byte_object(ty)? {
                self.line(&format!("  call void @g1_bytes_release(ptr {value})"));
            }
        }
        Ok(())
    }

    fn emit_byte_concat(&mut self, left: &str, right: &str) -> String {
        let usize_ty = format!("i{}", self.pointer_width());
        self.overflow_widths.insert((self.pointer_width(), "uadd"));
        let left_length_address = self.temp();
        let left_length = self.temp();
        let right_length_address = self.temp();
        let right_length = self.temp();
        let pair = self.temp();
        let length = self.temp();
        let overflow = self.temp();
        self.line(&format!(
            "  %{left_length_address} = getelementptr inbounds %g1.bytes, ptr {left}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{left_length} = load {usize_ty}, ptr %{left_length_address}"
        ));
        self.line(&format!(
            "  %{right_length_address} = getelementptr inbounds %g1.bytes, ptr {right}, i32 0, i32 1"
        ));
        self.line(&format!(
            "  %{right_length} = load {usize_ty}, ptr %{right_length_address}"
        ));
        self.line(&format!(
            "  %{pair} = call {{ {usize_ty}, i1 }} @llvm.uadd.with.overflow.{usize_ty}({usize_ty} %{left_length}, {usize_ty} %{right_length})"
        ));
        self.line(&format!(
            "  %{length} = extractvalue {{ {usize_ty}, i1 }} %{pair}, 0"
        ));
        self.line(&format!(
            "  %{overflow} = extractvalue {{ {usize_ty}, i1 }} %{pair}, 1"
        ));
        self.emit_runtime_fault_if(overflow, RUNTIME_FAULT_ALLOCATION_OVERFLOW);
        let result = self.temp();
        let result_data = self.temp();
        let left_data = self.temp();
        let result_right = self.temp();
        let right_data = self.temp();
        self.line(&format!(
            "  %{result} = call ptr @g1_bytes_allocate({usize_ty} %{length})"
        ));
        self.line(&format!(
            "  %{result_data} = call ptr @g1_bytes_data(ptr %{result})"
        ));
        self.line(&format!(
            "  %{left_data} = call ptr @g1_bytes_data(ptr {left})"
        ));
        self.line(&format!(
            "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{result_data}, ptr %{left_data}, {usize_ty} %{left_length}, i1 false)"
        ));
        self.line(&format!(
            "  %{result_right} = getelementptr inbounds i8, ptr %{result_data}, {usize_ty} %{left_length}"
        ));
        self.line(&format!(
            "  %{right_data} = call ptr @g1_bytes_data(ptr {right})"
        ));
        self.line(&format!(
            "  call void @llvm.memcpy.p0.p0.{usize_ty}(ptr %{result_right}, ptr %{right_data}, {usize_ty} %{right_length}, i1 false)"
        ));
        format!("%{result}")
    }

    fn array_element(&self, array: TypeId) -> Result<TypeId, Vec<Diagnostic>> {
        match self.runtime_type(array)? {
            Type::Array { element } => Ok(*element),
            other => Err(vec![backend_error(format!(
                "LLVM Array operation requires an Array type, found {other:?}"
            ))]),
        }
    }

    fn referenced_array_element(
        &self,
        function: &mir::Function,
        reference_register: u32,
    ) -> Result<TypeId, Vec<Diagnostic>> {
        let reference = self.register_runtime_type(function, reference_register)?;
        let array = match self.runtime_type(reference)? {
            Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
            other => {
                return Err(vec![unsupported(
                    function,
                    format!("Array operation through non-reference {other:?}"),
                )]);
            }
        };
        let element = self.array_element(array)?;
        self.ensure_plain_array_element(element, function)?;
        Ok(element)
    }

    fn emit_array_element_size(&mut self, element_ty: &str) -> String {
        let usize_ty = format!("i{}", self.pointer_width());
        let end = self.temp();
        let size = self.temp();
        self.line(&format!(
            "  %{end} = getelementptr {element_ty}, ptr null, {usize_ty} 1"
        ));
        self.line(&format!("  %{size} = ptrtoint ptr %{end} to {usize_ty}"));
        format!("%{size}")
    }

    fn emit_array_from_reference(&mut self, reference: &str) -> String {
        let array = self.temp();
        self.line(&format!("  %{array} = load ptr, ptr {reference}"));
        format!("%{array}")
    }

    fn emit_checked_array_slot(
        &mut self,
        array: &str,
        index_ty: &str,
        index: &str,
        element_ty: &str,
        require_initialized: bool,
    ) -> (String, String) {
        let length_address = self.temp();
        let length = self.temp();
        let out_of_bounds = self.temp();
        let initialized_address_address = self.temp();
        let initialized = self.temp();
        let initialized_slot = self.temp();
        let state = self.temp();
        let wrong_state = self.temp();
        self.line(&format!(
            "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{length} = load {index_ty}, ptr %{length_address}"
        ));
        self.line(&format!(
            "  %{out_of_bounds} = icmp uge {index_ty} {index}, %{length}"
        ));
        self.emit_runtime_fault_if(out_of_bounds, RUNTIME_FAULT_INDEX_OUT_OF_BOUNDS);
        self.line(&format!(
            "  %{initialized_address_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
        ));
        self.line(&format!(
            "  %{initialized} = load ptr, ptr %{initialized_address_address}"
        ));
        self.line(&format!(
            "  %{initialized_slot} = getelementptr inbounds i8, ptr %{initialized}, {index_ty} {index}"
        ));
        self.line(&format!("  %{state} = load i8, ptr %{initialized_slot}"));
        self.line(&format!(
            "  %{wrong_state} = icmp {} i8 %{state}, 0",
            if require_initialized { "eq" } else { "ne" }
        ));
        self.emit_runtime_fault_if(
            wrong_state,
            if require_initialized {
                RUNTIME_FAULT_EMPTY_ARRAY_SLOT
            } else {
                RUNTIME_FAULT_ARRAY_SLOT_ALREADY_INITIALIZED
            },
        );
        let data_address = self.temp();
        let data = self.temp();
        let slot = self.temp();
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 3"
        ));
        self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
        self.line(&format!(
            "  %{slot} = getelementptr inbounds {element_ty}, ptr %{data}, {index_ty} {index}"
        ));
        (format!("%{slot}"), format!("%{initialized_slot}"))
    }

    fn emit_array_dense_check(&mut self, array: &str, length: &str, usize_ty: &str) {
        let empty = self.temp();
        let loop_id = self.temp();
        let index_address = self.temp();
        self.line(&format!("  %{empty} = icmp eq {usize_ty} {length}, 0"));
        self.line(&format!("  %{index_address} = alloca {usize_ty}"));
        self.line(&format!("  store {usize_ty} 0, ptr %{index_address}"));
        self.line(&format!(
            "  br i1 %{empty}, label %array.dense.done{loop_id}, label %array.dense.check{loop_id}"
        ));
        self.line(&format!("array.dense.check{loop_id}:"));
        let index = self.temp();
        let initialized_address = self.temp();
        let initialized = self.temp();
        let slot = self.temp();
        let state = self.temp();
        let empty_slot = self.temp();
        self.line(&format!(
            "  %{index} = load {usize_ty}, ptr %{index_address}"
        ));
        self.line(&format!(
            "  %{initialized_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
        ));
        self.line(&format!(
            "  %{initialized} = load ptr, ptr %{initialized_address}"
        ));
        self.line(&format!(
            "  %{slot} = getelementptr inbounds i8, ptr %{initialized}, {usize_ty} %{index}"
        ));
        self.line(&format!("  %{state} = load i8, ptr %{slot}"));
        self.line(&format!("  %{empty_slot} = icmp eq i8 %{state}, 0"));
        let trap_label = self.temp();
        let continue_label = self.temp();
        self.line(&format!(
            "  br i1 %{empty_slot}, label %array.dense.trap{trap_label}, label %array.dense.continue{continue_label}"
        ));
        self.line(&format!("array.dense.trap{trap_label}:"));
        self.emit_runtime_fault(RUNTIME_FAULT_EMPTY_ARRAY_SLOT, "0", "0", "null", "0");
        self.line(&format!("array.dense.continue{continue_label}:"));
        let next = self.temp();
        let more = self.temp();
        self.line(&format!("  %{next} = add {usize_ty} %{index}, 1"));
        self.line(&format!("  store {usize_ty} %{next}, ptr %{index_address}"));
        self.line(&format!(
            "  %{more} = icmp ult {usize_ty} %{next}, {length}"
        ));
        self.line(&format!(
            "  br i1 %{more}, label %array.dense.check{loop_id}, label %array.dense.done{loop_id}"
        ));
        self.line(&format!("array.dense.done{loop_id}:"));
    }

    fn emit_destroy_array_elements(
        &mut self,
        array: &str,
        element: TypeId,
        function: &mir::Function,
    ) -> Result<(), Vec<Diagnostic>> {
        if !self.type_needs_destroy(element, &mut BTreeSet::new())? {
            return Ok(());
        }
        let usize_ty = format!("i{}", self.pointer_width());
        let element_ty = self.llvm_type(element)?;
        let length_address = self.temp();
        let length = self.temp();
        let empty = self.temp();
        let loop_id = self.temp();
        let index_address = self.temp();
        self.line(&format!(
            "  %{length_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 0"
        ));
        self.line(&format!(
            "  %{length} = load {usize_ty}, ptr %{length_address}"
        ));
        self.line(&format!("  %{empty} = icmp eq {usize_ty} %{length}, 0"));
        self.line(&format!("  %{index_address} = alloca {usize_ty}"));
        self.line(&format!(
            "  store {usize_ty} %{length}, ptr %{index_address}"
        ));
        self.line(&format!(
            "  br i1 %{empty}, label %array.destroy.done{loop_id}, label %array.destroy.check{loop_id}"
        ));
        self.line(&format!("array.destroy.check{loop_id}:"));
        let cursor = self.temp();
        let index = self.temp();
        let initialized_address = self.temp();
        let initialized = self.temp();
        let initialized_slot = self.temp();
        let state = self.temp();
        let occupied = self.temp();
        let destroy_label = self.temp();
        let continue_label = self.temp();
        self.line(&format!(
            "  %{cursor} = load {usize_ty}, ptr %{index_address}"
        ));
        self.line(&format!("  %{index} = sub {usize_ty} %{cursor}, 1"));
        self.line(&format!(
            "  %{initialized_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 4"
        ));
        self.line(&format!(
            "  %{initialized} = load ptr, ptr %{initialized_address}"
        ));
        self.line(&format!(
            "  %{initialized_slot} = getelementptr inbounds i8, ptr %{initialized}, {usize_ty} %{index}"
        ));
        self.line(&format!("  %{state} = load i8, ptr %{initialized_slot}"));
        self.line(&format!("  %{occupied} = icmp ne i8 %{state}, 0"));
        self.line(&format!(
            "  br i1 %{occupied}, label %array.destroy.value{destroy_label}, label %array.destroy.continue{continue_label}"
        ));
        self.line(&format!("array.destroy.value{destroy_label}:"));
        let data_address = self.temp();
        let data = self.temp();
        let slot = self.temp();
        let value = self.temp();
        self.line(&format!(
            "  %{data_address} = getelementptr inbounds %g1.array, ptr {array}, i32 0, i32 3"
        ));
        self.line(&format!("  %{data} = load ptr, ptr %{data_address}"));
        self.line(&format!(
            "  %{slot} = getelementptr inbounds {element_ty}, ptr %{data}, {usize_ty} %{index}"
        ));
        self.line(&format!("  %{value} = load {element_ty}, ptr %{slot}"));
        self.emit_destroy(element, &format!("%{value}"), function)?;
        self.line(&format!(
            "  br label %array.destroy.continue{continue_label}"
        ));
        self.line(&format!("array.destroy.continue{continue_label}:"));
        let more = self.temp();
        self.line(&format!(
            "  store {usize_ty} %{index}, ptr %{index_address}"
        ));
        self.line(&format!("  %{more} = icmp ne {usize_ty} %{index}, 0"));
        self.line(&format!(
            "  br i1 %{more}, label %array.destroy.check{loop_id}, label %array.destroy.done{loop_id}"
        ));
        self.line(&format!("array.destroy.done{loop_id}:"));
        Ok(())
    }

    fn llvm_constant(&self, value: &Constant) -> Result<String, Vec<Diagnostic>> {
        match value {
            Constant::Text(value) => self.byte_literal(value.as_bytes()),
            Constant::Bytes(value) => self.byte_literal(value),
            _ => llvm_scalar_constant(value),
        }
    }

    fn byte_literal(&self, bytes: &[u8]) -> Result<String, Vec<Diagnostic>> {
        self.byte_literals
            .get(bytes)
            .map(|index| format!("@g1.bytes.{index}"))
            .ok_or_else(|| vec![backend_error("missing prepared Text or Bytes literal")])
    }

    fn enum_slot_words(&self, ty: TypeId, field: u32) -> Result<usize, Vec<Diagnostic>> {
        let Type::Enum { variants, .. } = self.runtime_type(ty)? else {
            return Err(vec![backend_error(format!(
                "runtime type t{ty} is not an enum"
            ))]);
        };
        let mut maximum = 0usize;
        for variant in variants {
            if let Some(field) = variant.fields.get(field as usize) {
                maximum = maximum.max(self.storage_size(field.ty, &mut BTreeSet::new())?);
            }
        }
        if maximum == 0 {
            return Err(vec![backend_error(format!(
                "enum t{ty} has no payload field {field}"
            ))]);
        }
        Ok(maximum.div_ceil(16).max(1))
    }

    /// Conservative byte size used only for enum payload slots. Slots are
    /// i128-aligned and all payload accesses carry `align 1`, so overestimating
    /// padding is ABI-safe and keeps this independent of host `size_of`.
    fn storage_size(
        &self,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> Result<usize, Vec<Diagnostic>> {
        if !visiting.insert(ty) {
            return Err(vec![backend_error(format!(
                "recursive by-value runtime type t{ty}"
            ))]);
        }
        let size = match self.runtime_type(ty)? {
            Type::Unit => 1,
            Type::Available { .. } => 1,
            Type::Never => 0,
            Type::U8 | Type::I8 => 1,
            Type::U16 | Type::I16 => 2,
            Type::U32 | Type::I32 | Type::Char | Type::F32 => 4,
            Type::U64 | Type::I64 | Type::F64 => 8,
            Type::Usize | Type::Isize => usize::from(self.pointer_width() / 8),
            Type::U128 | Type::I128 => 16,
            Type::Text
            | Type::Bytes
            | Type::Array { .. }
            | Type::Callable { .. }
            | Type::Handler { .. }
            | Type::Resumption { .. }
            | Type::RefShared { .. }
            | Type::RefUnique { .. } => usize::from(self.pointer_width() / 8),
            Type::BindingPack { payload_type, .. } => self.storage_size(*payload_type, visiting)?,
            Type::Tuple { fields, .. } => {
                let mut size = 0usize;
                for field in fields {
                    if matches!(self.runtime_type(*field)?, Type::Available { .. }) {
                        continue;
                    }
                    let field_size = self.storage_size(*field, visiting)?;
                    size += field_size.div_ceil(16) * 16;
                }
                size.max(1)
            }
            Type::Struct { fields, .. } => {
                let mut size = 0usize;
                for field in fields {
                    if matches!(self.runtime_type(field.ty)?, Type::Available { .. }) {
                        continue;
                    }
                    let field_size = self.storage_size(field.ty, visiting)?;
                    size += field_size.div_ceil(16) * 16;
                }
                size.max(1)
            }
            Type::Enum { variants, .. } => {
                let fields = variants
                    .iter()
                    .map(|variant| variant.fields.len())
                    .max()
                    .unwrap_or(0);
                let mut size = 16usize;
                for index in 0..fields {
                    let mut maximum = 1usize;
                    for variant in variants {
                        if let Some(field) = variant.fields.get(index) {
                            maximum = maximum.max(self.storage_size(field.ty, visiting)?);
                        }
                    }
                    size += maximum.div_ceil(16) * 16;
                }
                size
            }
            other => {
                return Err(vec![backend_error(format!(
                    "LLVM enum payload layout does not yet support {other:?}"
                ))]);
            }
        };
        visiting.remove(&ty);
        Ok(size)
    }

    fn runtime_aggregate_fields(&self, aggregate: TypeId) -> Result<Vec<TypeId>, Vec<Diagnostic>> {
        let fields = match self.runtime_type(aggregate)? {
            Type::Tuple { fields, .. } => fields.clone(),
            Type::Struct { fields, .. } => fields.iter().map(|field| field.ty).collect(),
            Type::BindingPack { payload_type, .. } => {
                return self.runtime_aggregate_fields(*payload_type);
            }
            other => {
                return Err(vec![backend_error(format!(
                    "LLVM runtime field layout requires a tuple or struct, found {other:?}"
                ))]);
            }
        };
        fields
            .into_iter()
            .filter_map(|field| match self.runtime_type(field) {
                Ok(Type::Available { .. }) => None,
                Ok(_) => Some(Ok(field)),
                Err(error) => Some(Err(error)),
            })
            .collect()
    }

    fn runtime_aggregate_field_layout(
        &self,
        aggregate: TypeId,
        owned_mask_offset: usize,
    ) -> Result<Vec<AggregateFieldLayout>, Vec<Diagnostic>> {
        let fields = match self.runtime_type(aggregate)? {
            Type::Tuple { fields, .. } => fields.clone(),
            Type::Struct { fields, .. } => fields.iter().map(|field| field.ty).collect(),
            Type::BindingPack { payload_type, .. } => {
                return self.runtime_aggregate_field_layout(*payload_type, owned_mask_offset);
            }
            other => {
                return Err(vec![backend_error(format!(
                    "LLVM runtime field layout requires a tuple or struct, found {other:?}"
                ))]);
            }
        };
        let mut layout = Vec::with_capacity(fields.len());
        for (nominal_index, runtime_type) in fields.into_iter().enumerate() {
            if matches!(self.runtime_type(runtime_type)?, Type::Available { .. }) {
                continue;
            }
            layout.push(AggregateFieldLayout {
                nominal_index,
                physical_index: layout.len(),
                runtime_type,
                owned_mask_index: owned_mask_offset + layout.len(),
            });
        }
        Ok(layout)
    }

    fn runtime_aggregate_owned_field_index(
        &self,
        aggregate: TypeId,
        field: u32,
    ) -> Result<usize, Vec<Diagnostic>> {
        self.runtime_aggregate_field_layout(aggregate, 0)?
            .iter()
            .find(|layout| layout.nominal_index == field as usize)
            .map(|layout| layout.owned_mask_index)
            .ok_or_else(|| {
                vec![backend_error(format!(
                    "aggregate t{aggregate} has no runtime-owned field {field}"
                ))]
            })
    }

    fn runtime_aggregate_physical_field_index(
        &self,
        aggregate: TypeId,
        field: u32,
    ) -> Result<usize, Vec<Diagnostic>> {
        self.runtime_aggregate_field_layout(aggregate, 0)?
            .iter()
            .find(|layout| layout.nominal_index == field as usize)
            .map(|layout| layout.physical_index)
            .ok_or_else(|| {
                vec![backend_error(format!(
                    "aggregate t{aggregate} has no runtime-owned field {field}"
                ))]
            })
    }

    fn register_is_signed(
        &self,
        function: &mir::Function,
        register: u32,
    ) -> Result<bool, Vec<Diagnostic>> {
        let ty = function
            .register_types
            .get(register as usize)
            .and_then(|ty| self.phases.artifact.types.get(*ty as usize))
            .ok_or_else(|| vec![unsupported(function, "register without a runtime type")])?;
        Ok(matches!(
            ty.representation(),
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::Isize
        ))
    }

    fn integer_type_info(&self, ty: TypeId) -> Option<(bool, u16)> {
        Some(match self.runtime_type(ty).ok()? {
            Type::U8 => (false, 8),
            Type::U16 => (false, 16),
            Type::U32 | Type::Char => (false, 32),
            Type::U64 => (false, 64),
            Type::Usize => (false, self.pointer_width()),
            Type::U128 => (false, 128),
            Type::I8 => (true, 8),
            Type::I16 => (true, 16),
            Type::I32 => (true, 32),
            Type::I64 => (true, 64),
            Type::Isize => (true, self.pointer_width()),
            Type::I128 => (true, 128),
            _ => return None,
        })
    }

    fn load_operand(
        &mut self,
        function: &mir::Function,
        operand: &mir::Operand,
    ) -> Result<String, Vec<Diagnostic>> {
        let ty = self.register_type(function, operand.register)?;
        let temporary = self.temp();
        self.line(&format!(
            "  %{temporary} = load {ty}, ptr %r{}",
            operand.register
        ));
        Ok(format!("%{temporary}"))
    }

    fn load_register(
        &mut self,
        function: &mir::Function,
        register: u32,
    ) -> Result<String, Vec<Diagnostic>> {
        self.load_operand(
            function,
            &mir::Operand {
                register,
                mode: mir::UseMode::Copy,
            },
        )
    }

    fn llvm_type(&self, id: TypeId) -> Result<String, Vec<Diagnostic>> {
        let Some(ty) = self.phases.artifact.types.get(id as usize) else {
            return Err(vec![backend_error(format!("missing runtime type t{id}"))]);
        };
        Ok(match ty.representation() {
            Type::Unit => "i8".into(),
            // Tuple, struct, and BindingPack layouts erase Available fields.
            // Keep a concrete scalar only for the legacy nominal enum-slot
            // representation; Available is otherwise never a value/register.
            Type::Available { .. } => "i8".into(),
            Type::Never => "void".into(),
            Type::U8 | Type::I8 => "i8".into(),
            Type::U16 | Type::I16 => "i16".into(),
            Type::U32 | Type::I32 | Type::Char => "i32".into(),
            Type::U64 | Type::I64 => "i64".into(),
            Type::Usize | Type::Isize => format!("i{}", self.pointer_width()),
            Type::U128 | Type::I128 => "i128".into(),
            Type::F32 => "float".into(),
            Type::F64 => "double".into(),
            Type::Text
            | Type::Bytes
            | Type::Array { .. }
            | Type::Callable { .. }
            | Type::Handler { .. }
            | Type::Resumption { .. }
            | Type::RefShared { .. }
            | Type::RefUnique { .. } => "ptr".into(),
            Type::BindingPack { payload_type, .. } => self.llvm_type(*payload_type)?,
            Type::Tuple { .. } | Type::Struct { .. } => {
                let fields = self
                    .runtime_aggregate_fields(id)?
                    .into_iter()
                    .map(|field| self.llvm_type(field))
                    .collect::<Result<Vec<_>, _>>()?;
                if fields.is_empty() {
                    "{ i8 }".into()
                } else {
                    format!("{{ {} }}", fields.join(", "))
                }
            }
            Type::Enum { variants, .. } => {
                let fields = variants
                    .iter()
                    .map(|variant| variant.fields.len())
                    .max()
                    .unwrap_or(0);
                let slots = (0..fields)
                    .map(|field| {
                        self.enum_slot_words(id, field as u32)
                            .map(|words| format!("[{words} x i128]"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if slots.is_empty() {
                    "{ i32 }".into()
                } else {
                    format!("{{ i32, {} }}", slots.join(", "))
                }
            }
            other => {
                return Err(vec![backend_error(format!(
                    "LLVM scalar slice does not yet lower runtime type {other:?}"
                ))]);
            }
        })
    }

    fn llvm_return_type(&self, id: TypeId) -> Result<String, Vec<Diagnostic>> {
        let Some(ty) = self.phases.artifact.types.get(id as usize) else {
            return Err(vec![backend_error(format!("missing runtime type t{id}"))]);
        };
        if matches!(ty.representation(), Type::Unit | Type::Never) {
            Ok("void".into())
        } else {
            self.llvm_type(id)
        }
    }

    fn temp(&mut self) -> Temporary {
        let temporary = self.temporary;
        self.temporary += 1;
        Temporary(temporary)
    }

    fn line(&mut self, line: &str) {
        self.output.push_str(line);
        self.output.push('\n');
    }

    fn emit_trap_if(&mut self, condition: Temporary) {
        let trap = self.temp();
        let continuation = self.temp();
        self.line(&format!(
            "  br i1 %{condition}, label %trap{trap}, label %cont{continuation}"
        ));
        self.line(&format!("trap{trap}:"));
        self.line("  call void @llvm.trap()");
        self.line("  unreachable");
        self.line(&format!("cont{continuation}:"));
    }

    fn emit_runtime_fault(
        &mut self,
        detail: u32,
        arg0: &str,
        arg1: &str,
        message: &str,
        message_len: &str,
    ) {
        self.line(&format!(
            "  call void @g1_runtime_fault(i32 {detail}, i32 {arg0}, i32 {arg1}, ptr {message}, i{} {message_len})",
            self.pointer_width()
        ));
        self.line("  unreachable");
    }

    fn emit_runtime_fault_if(&mut self, condition: Temporary, detail: u32) {
        let fault = self.temp();
        let continuation = self.temp();
        self.line(&format!(
            "  br i1 %{condition}, label %runtime.fault{fault}, label %runtime.cont{continuation}"
        ));
        self.line(&format!("runtime.fault{fault}:"));
        self.emit_runtime_fault(detail, "0", "0", "null", "0");
        self.line(&format!("runtime.cont{continuation}:"));
    }

    fn emit_abort(&mut self, message: Option<&str>) {
        if let Some(message) = message {
            let bytes = message.as_bytes();
            let index = self.runtime_fault_literals[bytes];
            let pointer = format!(
                "getelementptr inbounds ([{} x i8], ptr @g1.runtime_fault.{index}, i32 0, i32 0)",
                bytes.len()
            );
            self.emit_runtime_fault(
                RUNTIME_FAULT_EXPLICIT_ABORT,
                "1",
                "0",
                &pointer,
                &bytes.len().to_string(),
            );
        } else {
            self.emit_runtime_fault(RUNTIME_FAULT_EXPLICIT_ABORT, "0", "0", "null", "0");
        }
    }

    fn emit_host_fault_if(&mut self, condition: Temporary, operation: u32) {
        let fault = self.temp();
        let continuation = self.temp();
        self.line(&format!(
            "  br i1 %{condition}, label %host.fault{fault}, label %host.cont{continuation}"
        ));
        self.line(&format!("host.fault{fault}:"));
        self.line(&format!("  call void @g1_host_fault(i32 {operation})"));
        self.line("  unreachable");
        self.line(&format!("host.cont{continuation}:"));
    }

    fn pointer_width(&self) -> u16 {
        pointer_width_for_target(&self.options.target_triple)
    }
}

fn integer_width(ty: &str) -> Option<u16> {
    ty.strip_prefix('i')?.parse().ok()
}

fn signed_minimum(width: u16) -> String {
    if width == 128 {
        i128::MIN.to_string()
    } else {
        (-(1_i128 << (width - 1))).to_string()
    }
}

fn signed_maximum(width: u16) -> String {
    if width == 128 {
        i128::MAX.to_string()
    } else {
        ((1_u128 << (width - 1)) - 1).to_string()
    }
}

fn unsigned_maximum(width: u16) -> String {
    if width == 128 {
        u128::MAX.to_string()
    } else {
        ((1_u128 << width) - 1).to_string()
    }
}

fn llvm_float_power(
    llvm_type: &str,
    exponent: i32,
    negative: bool,
) -> Result<String, Vec<Diagnostic>> {
    let mut value = 2_f64.powi(exponent);
    if negative {
        value = -value;
    }
    Ok(match llvm_type {
        "float" => format!("0x{:016X}", f64::from(value as f32).to_bits()),
        "double" => format!("0x{:016X}", value.to_bits()),
        _ => {
            return Err(vec![backend_error(format!(
                "checked float conversion requires float or double, found {llvm_type}"
            ))]);
        }
    })
}

fn binary_operands(loaded: &[(String, String)]) -> Option<(&str, &str, &str)> {
    let left = loaded.first()?;
    let right = loaded.get(1)?;
    Some((left.0.as_str(), left.1.as_str(), right.1.as_str()))
}

fn llvm_scalar_constant(value: &Constant) -> Result<String, Vec<Diagnostic>> {
    Ok(match value {
        Constant::Unit => "0".into(),
        Constant::U8(value) => value.to_string(),
        Constant::U16(value) => value.to_string(),
        Constant::U32(value) => value.to_string(),
        Constant::U64(value) | Constant::Usize(value) => value.to_string(),
        Constant::U128(value) => value.to_string(),
        Constant::I8(value) => value.to_string(),
        Constant::I16(value) => value.to_string(),
        Constant::I32(value) => value.to_string(),
        Constant::I64(value) | Constant::Isize(value) => value.to_string(),
        Constant::I128(value) => value.to_string(),
        // LLVM's hexadecimal spelling for `float` constants uses the
        // corresponding exactly-representable IEEE-754 double bit pattern.
        Constant::F32(value) => format!("0x{:016X}", f64::from(*value).to_bits()),
        Constant::F64(value) => format!("0x{:016X}", value.to_bits()),
        Constant::Char(value) => u32::from(*value).to_string(),
        Constant::Text(_) | Constant::Bytes(_) => unreachable!("byte literals use runtime globals"),
    })
}

fn unsupported(function: &mir::Function, feature: impl std::fmt::Display) -> Diagnostic {
    backend_error(format!(
        "LLVM backend does not yet support {feature} in `{}`",
        function.name
    ))
}

fn backend_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic::plain(message).with_code("G1LLVM001").with_help(
        "use the bytecode backend, or lower this program within the supported LLVM scalar slice",
    )
}

fn llvm_string(value: &str) -> String {
    value.replace('\\', "\\5C").replace('"', "\\22")
}

fn llvm_bytes(value: &[u8]) -> String {
    value.iter().map(|byte| format!("\\{byte:02X}")).collect()
}
