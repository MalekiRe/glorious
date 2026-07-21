#![allow(clippy::result_large_err)]

pub mod ast;
mod compiler;
pub mod compiler_core;
pub mod compiler_mir;
mod compiler_regions;
mod compiler_specialization;
mod compiler_traits;
mod compiler_typeck;
pub mod diagnostic;
pub mod eval;
pub mod interface;
pub mod lexer;
pub mod lossless;
pub mod parser;
pub mod resolve;
pub mod source_bundle;
pub mod span;
pub mod validate;

use std::path::Path;

use diagnostic::Diagnostic;
use eval::{Host, Value};
use source_bundle::{Segment, SourceBundle};

pub use ast::ConstKind;
pub use compiler::{
    CompileOptions, CompiledPhases, compile_bundle_to_bytecode,
    compile_bundle_to_bytecode_with_manifest, compile_bundle_to_bytecode_with_manifest_and_options,
    compile_bundle_to_bytecode_with_options, compile_bundle_to_phases,
    compile_bundle_to_phases_with_manifest, compile_bundle_to_phases_with_manifest_and_options,
    compile_bundle_to_phases_with_options, compile_source_to_bytecode,
    compile_source_to_bytecode_with_manifest, compile_source_to_bytecode_with_manifest_and_options,
    compile_source_to_bytecode_with_options, compile_source_to_phases,
    compile_source_to_phases_with_manifest, compile_source_to_phases_with_manifest_and_options,
    compile_source_to_phases_with_options,
};
pub use compiler_mir::{
    OptimizationLevel, OptimizationPass, OptimizationPassOutcome, OptimizationPassReport,
    OptimizationReport,
};
pub use compiler_traits::{
    AssociatedItemKind, GenericParameterKind, HostImportRole, IntrinsicRole, MachineTypeRole,
    ManifestAssociatedItem, ManifestHostImportLeaf, ManifestMachineType, ManifestPrimitiveLeaf,
    ManifestTrait, TraitKey, TraitPolicy, TrustedRuntimeManifest, TrustedTraitManifest,
};

fn run_source_stream(
    source: &str,
    args: Vec<String>,
    host: &mut dyn Host,
    runtime_leaves: eval::RuntimeLeafAuthority,
) -> Result<Value, Vec<Diagnostic>> {
    run_source_entry_stream(source, "main", args, host, runtime_leaves)
}

fn run_source_entry_stream(
    source: &str,
    entry_name: &str,
    args: Vec<String>,
    host: &mut dyn Host,
    runtime_leaves: eval::RuntimeLeafAuthority,
) -> Result<Value, Vec<Diagnostic>> {
    let tokens = lexer::lex(source).map_err(|error| vec![error])?;
    let (program, parse_diagnostics) = parser::parse_recovering(tokens);
    if !parse_diagnostics.is_empty() {
        return Err(parse_diagnostics);
    }
    let program = parser::normalize_for_legacy_consumers(program);
    validate::validate(&program)?;
    let program = compiler::normalize_trait_surface_for_recovery(&program)?;
    let program = compiler::normalize_constructor_aliases(&program)?;
    eval::run_entry_with_runtime(&program, entry_name, args, host, runtime_leaves)
        .map_err(|error| vec![error])
}

pub fn run_source(
    source_name: &str,
    source: &str,
    args: Vec<String>,
    host: &mut dyn Host,
) -> Result<Value, Vec<Diagnostic>> {
    let bundle = SourceBundle::distributed(Segment::new(source_name, source), []);
    run_bundle(&bundle, args, host).map_err(|errors| {
        errors
            .into_iter()
            .map(|error| {
                let error = bundle.localize_diagnostic(error);
                if error.span.is_none() {
                    error.with_source(source_name)
                } else {
                    error
                }
            })
            .collect::<Vec<_>>()
    })
}

/// Runs a generation-1 bundle as one source stream. Diagnostics retain global
/// spans and can be localized with [`SourceBundle::map_diagnostic`] or rendered
/// with [`SourceBundle::write_diagnostic`].
pub fn run_bundle(
    bundle: &SourceBundle,
    args: Vec<String>,
    host: &mut dyn Host,
) -> Result<Value, Vec<Diagnostic>> {
    let runtime_leaves = if bundle.is_canonical_distribution() {
        runtime_leaf_authority(bundle, TrustedRuntimeManifest::distributed_generation_1())
    } else {
        eval::RuntimeLeafAuthority::default()
    };
    run_source_stream(bundle.source(), args, host, runtime_leaves)
}

/// Runs an explicitly trusted conformance bundle with its supplied finite
/// runtime manifest. This is a recovery/differential-testing entry point; the
/// distribution-facing [`run_bundle`] always chooses its embedded manifest.
pub fn run_bundle_with_manifest_for_conformance(
    bundle: &SourceBundle,
    args: Vec<String>,
    host: &mut dyn Host,
    manifest: &TrustedTraitManifest,
) -> Result<Value, Vec<Diagnostic>> {
    run_source_stream(
        bundle.source(),
        args,
        host,
        runtime_leaf_authority(bundle, manifest.runtime().clone()),
    )
}

/// Executes one named zero-argument callable from an explicitly trusted
/// conformance bundle. This lets differential tests compare a library callable
/// even though a valid bytecode executable's `main` must return unit.
pub fn run_bundle_entry_with_manifest_for_conformance(
    bundle: &SourceBundle,
    entry_name: &str,
    host: &mut dyn Host,
    manifest: &TrustedTraitManifest,
) -> Result<Value, Vec<Diagnostic>> {
    run_source_entry_stream(
        bundle.source(),
        entry_name,
        vec![],
        host,
        runtime_leaf_authority(bundle, manifest.runtime().clone()),
    )
}

fn runtime_leaf_authority(
    bundle: &SourceBundle,
    runtime: TrustedRuntimeManifest,
) -> eval::RuntimeLeafAuthority {
    let Some(range) = bundle.trusted_standard_global_range() else {
        return eval::RuntimeLeafAuthority::default();
    };
    // Declaration indices are resolved after parsing below. Bind by the exact
    // trusted declaration identity, never by a call-site spelling.
    let leaves = runtime
        .primitive_leaves()
        .iter()
        .map(|leaf| {
            (
                leaf.display_name.clone(),
                eval::RuntimeLeaf::Primitive(leaf.primitive),
            )
        })
        .chain(runtime.host_import_leaves().iter().map(|leaf| {
            (
                leaf.display_name.clone(),
                eval::RuntimeLeaf::HostImport(leaf.role),
            )
        }))
        .chain(
            [
                (
                    "__g1_int_wrapping_add",
                    grandiose_vm::Primitive::IntWrappingAdd,
                ),
                (
                    "__g1_int_wrapping_sub",
                    grandiose_vm::Primitive::IntWrappingSub,
                ),
                (
                    "__g1_int_wrapping_mul",
                    grandiose_vm::Primitive::IntWrappingMul,
                ),
                ("__g1_int_bit_and", grandiose_vm::Primitive::IntBitAnd),
                ("__g1_int_bit_or", grandiose_vm::Primitive::IntBitOr),
                ("__g1_int_bit_xor", grandiose_vm::Primitive::IntBitXor),
                ("__g1_int_bit_not", grandiose_vm::Primitive::IntBitNot),
                ("__g1_int_shl", grandiose_vm::Primitive::IntShl),
                ("__g1_int_shr", grandiose_vm::Primitive::IntShr),
                (
                    "__g1_int_convert_checked_to_u8",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_u16",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_u32",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_u64",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_u128",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_usize",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_i8",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_i16",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_i32",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_i64",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_i128",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_checked_to_isize",
                    grandiose_vm::Primitive::IntConvertChecked,
                ),
                (
                    "__g1_int_convert_wrapping_to_u8",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_u16",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_u32",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_u64",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_u128",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_usize",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_i8",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_i16",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_i32",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_i64",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_i128",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
                (
                    "__g1_int_convert_wrapping_to_isize",
                    grandiose_vm::Primitive::IntConvertWrapping,
                ),
            ]
            .into_iter()
            .map(|(name, primitive)| (name.to_owned(), eval::RuntimeLeaf::Primitive(primitive))),
        )
        .collect::<Vec<_>>();
    // The Program is not available until `run_source_stream` has parsed it, so
    // preserve the finite table and trusted range in a deferred authority.
    eval::RuntimeLeafAuthority::unbound(leaves, range)
}

pub fn run_file(
    path: &Path,
    args: Vec<String>,
    host: &mut dyn Host,
) -> Result<Value, Vec<Diagnostic>> {
    let source = std::fs::read_to_string(path).map_err(|error| {
        vec![Diagnostic::plain(format!(
            "could not read {}: {error}",
            path.display()
        ))]
    })?;
    run_source(&path.display().to_string(), &source, args, host)
}
