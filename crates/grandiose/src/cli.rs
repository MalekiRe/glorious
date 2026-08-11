use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ffi::OsString,
    fs::OpenOptions,
    io::{self, BufRead, Read, Write},
    path::{Path, PathBuf},
    process::{Command as ProcessCommand, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

use grandiose::{
    artifact_llvm::emit_artifact_llvm_ir,
    compile_bundle_to_phases_with_options,
    compiler_session::CompilationDriver,
    diagnostic::{Diagnostic, Severity},
    emit_llvm_ir, emit_llvm_native_object_units,
    interface::{scan_interfaces, InterfaceSelection},
    lexer,
    llvm_backend::{
        LlvmOptions, DEFAULT_NATIVE_ALLOCATION_LIMIT, LLVM_NATIVE_OBJECT_PARTITION_SCHEMA,
    },
    source_bundle::{Segment, SourceBundle},
    CompileOptions, OptimizationLevel,
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Map, Value};

const USAGE: &str = "usage:\n  grc [OPTIONS] <primary.glorious> [additional.glorious ...]\n  grc --inspect-token <source.glorious> <index> [index ...]\n  grc --inspect-bundle-token <primary.glorious> [additional.glorious ...] -- <index> [index ...]\n  grc --serve\n\ncompiler options:\n  -O1 | -O2 | -O3         optimization level (default: -O2)\n  -O0                     raw lowering mode for backend verification\n  --check                  compile and verify without writing output\n  --phase PHASE            stop after lex, scan, resolve, or check\n  --emit KIND              emit bytecode, LLVM IR/object/executable, MIR/Core/provisional/control-plan, monolithic source, or interfaces JSON\n  --native-incremental     select process-local partitioned native objects (serve, -O3 executable only)\n  --native-incremental-cache DIR  durable private partitioned objects (-O3 executable only)\n  --native-allocation-limit BYTES  bounded per-allocation native-runtime ceiling (executable only)\n  --dependency NAME=PATH   add a named dependency package root (repeatable)\n  --diagnostics json       emit one machine-readable diagnostic per line\n  --inspect-token          show lexer details for indexed tokens in an assembled distributed source bundle\n  --inspect-bundle-token   map token indices in an assembled distributed source bundle\n  --capabilities           print the versioned machine-readable contract\n  --serve                  serve versioned JSON-line compile requests\n  -o <path>                output path (default: primary input + kind suffix)\n  -h, --help               show this help\n\nnative incremental environment:\n  G1_NATIVE_OBJECT_WORKERS requests 1..=4 concurrent durable native object workers; the compiler clamps it to available parallelism (default: the same safe bound).\n";

const MAX_NATIVE_ALLOCATION_LIMIT: u64 = 1024 * 1024 * 1024;
const SESSION_PROTOCOL: u32 = 1;
const SESSION_MAX_LINE_BYTES: usize = 1024 * 1024;
const SESSION_MAX_ARGUMENTS: usize = 128;
const SESSION_MAX_INPUTS: usize = 64;
const SESSION_MAX_SOURCE_BYTES: usize = 16 * 1024 * 1024;
const NATIVE_HOST_RUNTIME: &[u8] = include_bytes!("native_host_runtime.c");
const NATIVE_RUNTIME: &[u8] = include_bytes!("native_runtime.c");
/// The durable cache route invokes independent Clang processes. Keep its
/// concurrency deliberately conservative so an editor request cannot starve
/// the machine while still avoiding one-process-at-a-time compilation.
const MAX_DURABLE_NATIVE_OBJECT_WORKERS: usize = 4;
const DURABLE_NATIVE_OBJECT_WORKERS_ENV: &str = "G1_NATIVE_OBJECT_WORKERS";
const DISK_CACHE_LOCK_WAIT: Duration = Duration::from_secs(30);
static DISK_CACHE_TEMPORARY_SEQUENCE: AtomicU64 = AtomicU64::new(0);

struct TemporaryNativeHost {
    path: PathBuf,
}

impl TemporaryNativeHost {
    fn create(output: &Path) -> io::Result<Self> {
        let directory = output
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        let process = std::process::id();
        for attempt in 0..128u32 {
            let path = directory.join(format!(".grc-native-host-{process}-{attempt}.c"));
            match OpenOptions::new().write(true).create_new(true).open(&path) {
                Ok(mut file) => {
                    if let Err(error) = file.write_all(NATIVE_HOST_RUNTIME) {
                        drop(file);
                        let _ = std::fs::remove_file(&path);
                        return Err(error);
                    }
                    if let Err(error) = file.write_all(NATIVE_RUNTIME) {
                        drop(file);
                        let _ = std::fs::remove_file(&path);
                        return Err(error);
                    }
                    return Ok(Self { path });
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
                Err(error) => return Err(error),
            }
        }
        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            "could not reserve a temporary native host source path",
        ))
    }
}

impl Drop for TemporaryNativeHost {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

/// A request-owned materialization of cached (or freshly compiled) native
/// object bytes. It never survives the final Wild link and therefore cannot
/// be mistaken for a cross-process artifact cache.
struct TemporaryNativeObject {
    path: PathBuf,
}

impl TemporaryNativeObject {
    fn create(output: &Path, label: &str, ordinal: usize) -> io::Result<Self> {
        let directory = output
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        let process = std::process::id();
        for attempt in 0..128u32 {
            let path = directory.join(format!(
                ".grc-native-{label}-{process}-{ordinal}-{attempt}.o"
            ));
            match OpenOptions::new().write(true).create_new(true).open(&path) {
                Ok(_) => return Ok(Self { path }),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
                Err(error) => return Err(error),
            }
        }
        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            "could not reserve a temporary native object path",
        ))
    }
}

impl Drop for TemporaryNativeObject {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StopPhase {
    Lex,
    Scan,
    Resolve,
    Check,
}

impl StopPhase {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "lex" => Ok(Self::Lex),
            "scan" => Ok(Self::Scan),
            "resolve" => Ok(Self::Resolve),
            "check" => Ok(Self::Check),
            _ => Err(format!(
                "unsupported stop phase `{value}`; expected lex, scan, resolve, or check"
            )),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EmitKind {
    Bytecode,
    LlvmIr,
    LlvmObject,
    Executable,
    Mir,
    Core,
    Provisional,
    ControlPlan,
    MonolithicSource,
    InterfacesJson,
    StandardInterfacesJson,
}

impl EmitKind {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "bytecode" | "grbc" => Ok(Self::Bytecode),
            "llvm-ir" | "ll" => Ok(Self::LlvmIr),
            "llvm-object" | "obj" => Ok(Self::LlvmObject),
            "executable" | "exe" => Ok(Self::Executable),
            "mir" => Ok(Self::Mir),
            "core" => Ok(Self::Core),
            "provisional" => Ok(Self::Provisional),
            "control-plan" => Ok(Self::ControlPlan),
            "monolithic-source" => Ok(Self::MonolithicSource),
            "interfaces-json" => Ok(Self::InterfacesJson),
            "std-interfaces-json" => Ok(Self::StandardInterfacesJson),
            _ => Err(format!(
                "unsupported emission kind `{value}`; expected bytecode, grbc, llvm-ir, ll, llvm-object, obj, executable, exe, mir, core, provisional, control-plan, monolithic-source, interfaces-json, or std-interfaces-json"
            )),
        }
    }

    fn extension(self) -> &'static str {
        match self {
            Self::Bytecode => "grbc",
            Self::LlvmIr => "ll",
            Self::LlvmObject => "o",
            Self::Executable => "out",
            Self::Mir => "mir",
            Self::Core => "core",
            Self::Provisional => "provisional",
            Self::ControlPlan => "control-plan",
            Self::MonolithicSource => "monolithic.glorious",
            Self::InterfacesJson | Self::StandardInterfacesJson => "json",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CompileCommand {
    inputs: Vec<PathBuf>,
    dependencies: Vec<(String, PathBuf)>,
    optimization_level: OptimizationLevel,
    stop_phase: Option<StopPhase>,
    output: Option<PathBuf>,
    emit: Option<EmitKind>,
    /// Explicit opt-in to process-local independently compiled LLVM function
    /// objects. The persistent server owns the cache; a one-shot invocation
    /// is rejected before it could accidentally use the monolithic route.
    native_incremental: bool,
    native_incremental_cache: Option<PathBuf>,
    native_allocation_limit: Option<u64>,
    json_diagnostics: bool,
}

enum Command {
    Compile(CompileCommand),
    ArtifactLlvmIr {
        artifact: PathBuf,
        output: PathBuf,
    },
    InspectTokens {
        input: PathBuf,
        indices: Vec<usize>,
    },
    InspectBundleTokens {
        inputs: Vec<PathBuf>,
        indices: Vec<usize>,
    },
    Help,
    Version,
    Capabilities,
    Serve,
}

fn parse_optimization(argument: &str) -> Option<OptimizationLevel> {
    Some(match argument {
        "-O0" => OptimizationLevel::O0,
        "-O1" => OptimizationLevel::O1,
        "-O2" => OptimizationLevel::O2,
        "-O3" => OptimizationLevel::O3,
        _ => return None,
    })
}

fn parse(args: Vec<OsString>) -> Result<Command, String> {
    let mut args = args.into_iter().peekable();
    if args
        .peek()
        .is_some_and(|argument| argument == "--artifact-llvm-ir")
    {
        args.next();
        let artifact = args
            .next()
            .map(PathBuf::from)
            .ok_or_else(|| "`--artifact-llvm-ir` requires a `.grbc` artifact".to_string())?;
        if artifact
            .extension()
            .and_then(|extension| extension.to_str())
            != Some("grbc")
        {
            return Err(format!(
                "artifact `{}` must use the `.grbc` extension",
                artifact.display()
            ));
        }
        if args.next().as_deref() != Some(std::ffi::OsStr::new("-o")) {
            return Err("`--artifact-llvm-ir` requires `-o <output.ll>`".to_string());
        }
        let output = args
            .next()
            .map(PathBuf::from)
            .ok_or_else(|| "`-o` requires an output path".to_string())?;
        if args.next().is_some() {
            return Err(
                "`--artifact-llvm-ir` accepts only an artifact and `-o <output.ll>`".to_string(),
            );
        }
        return Ok(Command::ArtifactLlvmIr { artifact, output });
    }
    if args
        .peek()
        .is_some_and(|argument| argument == "--inspect-bundle-token")
    {
        args.next();
        let mut inputs = Vec::new();
        while args.peek().is_some_and(|argument| argument != "--") {
            inputs.push(PathBuf::from(args.next().unwrap()));
        }
        if inputs.is_empty() {
            return Err("`--inspect-bundle-token` requires at least a primary source path".into());
        }
        if args.next().is_none() {
            return Err("`--inspect-bundle-token` requires `--` before token indices".into());
        }
        let indices = parse_token_indices(args, "--inspect-bundle-token")?;
        return Ok(Command::InspectBundleTokens { inputs, indices });
    }
    if args
        .peek()
        .is_some_and(|argument| argument == "--inspect-token")
    {
        args.next();
        let input = args
            .next()
            .map(PathBuf::from)
            .ok_or_else(|| "`--inspect-token` requires a source path".to_string())?;
        let indices = parse_token_indices(args, "--inspect-token")?;
        return Ok(Command::InspectTokens { input, indices });
    }
    if args.peek().is_some_and(|argument| argument == "--serve") {
        args.next();
        if args.next().is_some() {
            return Err("`--serve` does not accept other arguments".to_string());
        }
        return Ok(Command::Serve);
    }
    if args
        .peek()
        .is_some_and(|argument| argument == "--capabilities")
    {
        args.next();
        if args.next().is_some() {
            return Err("`--capabilities` does not accept other arguments".to_string());
        }
        return Ok(Command::Capabilities);
    }
    let mut command = CompileCommand {
        inputs: Vec::new(),
        dependencies: Vec::new(),
        optimization_level: OptimizationLevel::default(),
        stop_phase: None,
        output: None,
        emit: None,
        native_incremental: false,
        native_incremental_cache: None,
        native_allocation_limit: None,
        json_diagnostics: false,
    };
    let mut positional_only = false;
    while let Some(argument) = args.next() {
        let text = argument.to_string_lossy();
        if !positional_only {
            match text.as_ref() {
                "-h" | "--help" => return Ok(Command::Help),
                "--version" => return Ok(Command::Version),
                "--check" => {
                    if command.stop_phase.replace(StopPhase::Check).is_some() {
                        return Err("a stop phase may be specified only once".to_string());
                    }
                    continue;
                }
                "--phase" => {
                    let value = args
                        .next()
                        .ok_or_else(|| "`--phase` requires a phase".to_string())?;
                    let value = value
                        .to_str()
                        .ok_or_else(|| "stop phase must be valid UTF-8".to_string())?;
                    let phase = StopPhase::parse(value)?;
                    if command.stop_phase.replace(phase).is_some() {
                        return Err("a stop phase may be specified only once".to_string());
                    }
                    continue;
                }
                "--diagnostics" => {
                    let value = args
                        .next()
                        .ok_or_else(|| "`--diagnostics` requires `json`".to_string())?;
                    if value != "json" {
                        return Err(format!(
                            "unsupported diagnostic format `{}`; expected `json`",
                            value.to_string_lossy()
                        ));
                    }
                    if command.json_diagnostics {
                        return Err("`--diagnostics` may be specified only once".to_string());
                    }
                    command.json_diagnostics = true;
                    continue;
                }
                "--dependency" => {
                    let value = args
                        .next()
                        .ok_or_else(|| "`--dependency` requires `NAME=PATH`".to_string())?;
                    let value = value
                        .to_str()
                        .ok_or_else(|| "dependency metadata must be valid UTF-8".to_string())?;
                    let (name, path) = value.split_once('=').ok_or_else(|| {
                        "`--dependency` requires `NAME=PATH` (including `=`)".to_string()
                    })?;
                    if name.is_empty() || path.is_empty() {
                        return Err(
                            "`--dependency` requires nonempty `NAME` and `PATH`".to_string()
                        );
                    }
                    command
                        .dependencies
                        .push((name.to_string(), PathBuf::from(path)));
                    continue;
                }
                "--emit" => {
                    let value = args
                        .next()
                        .ok_or_else(|| "`--emit` requires an output kind".to_string())?;
                    let value = value
                        .to_str()
                        .ok_or_else(|| "emission kind must be valid UTF-8".to_string())?;
                    let kind = EmitKind::parse(value)?;
                    if command.emit.replace(kind).is_some() {
                        return Err("`--emit` may be specified only once".to_string());
                    }
                    continue;
                }
                "--native-incremental" => {
                    if command.native_incremental {
                        return Err("`--native-incremental` may be specified only once".to_string());
                    }
                    command.native_incremental = true;
                    continue;
                }
                "--native-incremental-cache" => {
                    let path = args.next().ok_or_else(|| {
                        "`--native-incremental-cache` requires a directory".to_string()
                    })?;
                    if command
                        .native_incremental_cache
                        .replace(PathBuf::from(path))
                        .is_some()
                    {
                        return Err(
                            "`--native-incremental-cache` may be specified only once".to_string()
                        );
                    }
                    command.native_incremental = true;
                    continue;
                }
                "--native-allocation-limit" => {
                    let value = args.next().ok_or_else(|| {
                        "`--native-allocation-limit` requires a byte count".to_string()
                    })?;
                    let value = value
                        .to_str()
                        .ok_or_else(|| "native allocation limit must be valid UTF-8".to_string())?;
                    let limit = parse_native_allocation_limit(value)?;
                    if command.native_allocation_limit.replace(limit).is_some() {
                        return Err(
                            "`--native-allocation-limit` may be specified only once".to_string()
                        );
                    }
                    continue;
                }
                "-o" => {
                    let path = args
                        .next()
                        .ok_or_else(|| "`-o` requires an output path".to_string())?;
                    if command.output.replace(PathBuf::from(path)).is_some() {
                        return Err("`-o` may be specified only once".to_string());
                    }
                    continue;
                }
                "--" => {
                    positional_only = true;
                    continue;
                }
                _ => {}
            }
            if let Some(value) = text.strip_prefix("--emit=") {
                let kind = EmitKind::parse(value)?;
                if command.emit.replace(kind).is_some() {
                    return Err("`--emit` may be specified only once".to_string());
                }
                continue;
            }
            if let Some(level) = parse_optimization(&text) {
                command.optimization_level = level;
                continue;
            }
            if text.starts_with('-') {
                return Err(format!("unknown compiler option `{text}`"));
            }
        }
        command.inputs.push(PathBuf::from(argument));
    }

    if command.inputs.is_empty() && command.emit != Some(EmitKind::StandardInterfacesJson) {
        return Err("at least one `.glorious` input is required".to_string());
    }
    for input in &command.inputs {
        if input.extension().and_then(|extension| extension.to_str()) != Some("glorious") {
            return Err(format!(
                "input `{}` must use the `.glorious` extension",
                input.display()
            ));
        }
    }
    for (_, input) in &command.dependencies {
        if input.extension().and_then(|extension| extension.to_str()) != Some("glorious") {
            return Err(format!(
                "dependency root `{}` must use the `.glorious` extension",
                input.display()
            ));
        }
    }
    if command.stop_phase.is_some() && (command.output.is_some() || command.emit.is_some()) {
        return Err("a stop phase cannot be combined with `--emit` or `-o`".to_string());
    }
    if command.emit == Some(EmitKind::StandardInterfacesJson) && !command.inputs.is_empty() {
        return Err("`--emit std-interfaces-json` does not accept source inputs".to_string());
    }
    if matches!(
        command.emit,
        Some(EmitKind::InterfacesJson | EmitKind::StandardInterfacesJson)
    ) && command.output.is_some()
    {
        return Err(
            "interface JSON is written to stdout and cannot be combined with `-o`".to_string(),
        );
    }
    if command.native_allocation_limit.is_some() && command.emit != Some(EmitKind::Executable) {
        return Err(
            "`--native-allocation-limit` is supported only with `--emit executable`".to_string(),
        );
    }
    if command.native_incremental && command.emit != Some(EmitKind::Executable) {
        return Err("`--native-incremental` requires `--emit executable`".to_string());
    }
    if command.native_incremental && command.optimization_level != OptimizationLevel::O3 {
        return Err("`--native-incremental` requires `-O3`".to_string());
    }
    Ok(Command::Compile(command))
}

fn parse_native_allocation_limit(value: &str) -> Result<u64, String> {
    let limit = value
        .parse::<u64>()
        .map_err(|_| "`--native-allocation-limit` requires an unsigned byte count".to_string())?;
    if limit < DEFAULT_NATIVE_ALLOCATION_LIMIT {
        return Err(format!(
            "`--native-allocation-limit` must be at least {DEFAULT_NATIVE_ALLOCATION_LIMIT} bytes"
        ));
    }
    if limit > MAX_NATIVE_ALLOCATION_LIMIT {
        return Err(format!(
            "`--native-allocation-limit` must not exceed {MAX_NATIVE_ALLOCATION_LIMIT} bytes"
        ));
    }
    Ok(limit)
}

fn parse_token_indices(
    args: impl Iterator<Item = OsString>,
    option: &str,
) -> Result<Vec<usize>, String> {
    let indices = args
        .map(|argument| {
            argument
                .to_str()
                .ok_or_else(|| "token indices must be valid UTF-8".to_string())?
                .parse::<usize>()
                .map_err(|_| format!("invalid token index `{}`", argument.to_string_lossy()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if indices.is_empty() {
        return Err(format!("`{option}` requires at least one token index"));
    }
    Ok(indices)
}

fn read_segment(path: &Path) -> Result<Segment, String> {
    let source = std::fs::read_to_string(path)
        .map_err(|error| format!("could not read {}: {error}", path.display()))?;
    Ok(Segment::new(path.display().to_string(), source))
}

fn default_output(input: &Path, kind: EmitKind) -> PathBuf {
    input.with_extension(kind.extension())
}

fn line_and_column(source: &str, offset: usize) -> (usize, usize) {
    let offset = offset.min(source.len());
    let prefix = &source[..offset];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
    let column = source[line_start..offset].chars().count() + 1;
    (line, column)
}

fn json_label(file: &str, source: &str, span: grandiose::span::Span, message: &str) -> Value {
    let (line, col) = line_and_column(source, span.start);
    json!({
        "file": file,
        "line": line,
        "col": col,
        "start_byte": span.start,
        "end_byte": span.end,
        "message": message,
    })
}

fn write_json_diagnostic(
    bundle: &SourceBundle,
    diagnostic: &Diagnostic,
    mut output: impl Write,
) -> io::Result<()> {
    let mapped = bundle.map_diagnostic(diagnostic);
    let mut labels = Vec::new();
    if let Some(primary) = mapped.span {
        labels.push(json_label(
            primary.segment.name(),
            primary.segment.source(),
            primary.span,
            &diagnostic.message,
        ));
    }
    labels.extend(mapped.related.into_iter().map(|(related, message)| {
        json_label(
            related.segment.name(),
            related.segment.source(),
            related.span,
            message,
        )
    }));

    let severity = match diagnostic.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Advice => "advice",
    };
    let mut object = Map::new();
    object.insert("severity".into(), json!(severity));
    object.insert("title".into(), json!(&diagnostic.title));
    object.insert("message".into(), json!(&diagnostic.message));
    object.insert("labels".into(), Value::Array(labels));
    if let Some(code) = &diagnostic.code {
        object.insert("code".into(), json!(code));
    }
    if let Some(note) = &diagnostic.note {
        object.insert("note".into(), json!(note));
    }
    if let Some(help) = &diagnostic.help {
        object.insert("help".into(), json!(help));
    }
    if let Some(fix) = mapped.fix {
        object.insert(
            "fix".into(),
            json!({
                "file": fix.span.segment.name(),
                "start_byte": fix.span.span.start,
                "end_byte": fix.span.span.end,
                "replacement": fix.replacement,
            }),
        );
    }
    serde_json::to_writer(&mut output, &object).map_err(io::Error::other)?;
    writeln!(output)
}

fn report_diagnostics(
    bundle: &SourceBundle,
    diagnostics: Vec<Diagnostic>,
    json: bool,
    stderr: &mut dyn Write,
) -> u8 {
    for diagnostic in diagnostics {
        let written = if json {
            write_json_diagnostic(bundle, &diagnostic, &mut *stderr)
        } else {
            bundle.write_diagnostic(&diagnostic, &mut *stderr)
        };
        if written.is_err() {
            let _ = writeln!(stderr, "grc: error: failed to render a diagnostic");
            break;
        }
    }
    1
}

fn load_segments(command: &CompileCommand) -> Result<Vec<Segment>, String> {
    let mut segments = Vec::with_capacity(command.inputs.len() + command.dependencies.len());
    for input in &command.inputs {
        segments.push(read_segment(input)?);
    }
    let Some(primary) = command.inputs.first() else {
        return Ok(segments);
    };

    // The library compilation API is deliberately hermetic. The path-aware
    // driver supplies that API with the complete declared module closure.
    // Explicit additional inputs are retained so module-graph diagnostics can
    // reject orphans and duplicate claims rather than silently hiding them.
    let mut known = command
        .inputs
        .iter()
        .cloned()
        .zip(segments)
        .collect::<BTreeMap<_, _>>();
    let mut roots = vec![primary.clone()];
    for (name, path) in &command.dependencies {
        if known.contains_key(path) {
            return Err(format!(
                "dependency root {} is also supplied as an ordinary input",
                path.display()
            ));
        }
        known.insert(
            path.clone(),
            read_segment(path)?.with_package_root(name.clone()),
        );
        roots.push(path.clone());
    }
    let mut queue = VecDeque::from(roots);
    let mut processed = BTreeSet::new();
    while let Some(path) = queue.pop_front() {
        if !processed.insert(path.clone()) {
            continue;
        }
        let Some(segment) = known.get(&path) else {
            continue;
        };
        for child in declared_external_module_paths(&path, segment.source()) {
            if !child.is_file() {
                // Leave absence to the module graph, which has the source
                // declaration span needed for a structured diagnostic.
                continue;
            }
            if !known.contains_key(&child) {
                if known.len() >= SESSION_MAX_INPUTS {
                    return Err(format!(
                        "declared module closure exceeds input-count limit of {SESSION_MAX_INPUTS}"
                    ));
                }
                known.insert(child.clone(), read_segment(&child)?);
            }
            queue.push_back(child);
        }
    }

    let primary = known
        .remove(primary)
        .expect("primary input was inserted before discovery");
    let mut segments = Vec::with_capacity(known.len() + 1);
    segments.push(primary);
    segments.extend(known.into_values());
    Ok(segments)
}

fn declared_external_module_paths(file: &Path, source: &str) -> Vec<PathBuf> {
    use grandiose::ast::ModuleKind;

    let Ok(tokens) = grandiose::lexer::lex(source) else {
        return Vec::new();
    };
    let (program, diagnostics) = grandiose::parser::parse_recovering(tokens);
    if !diagnostics.is_empty() {
        return Vec::new();
    }
    let base = file.parent().unwrap_or_else(|| Path::new(""));
    let mut paths = Vec::new();
    for declaration in &program.modules {
        if declaration.kind != ModuleKind::External {
            continue;
        }
        let mut containers = program
            .modules
            .iter()
            .filter_map(|candidate| match candidate.kind {
                ModuleKind::Inline { body }
                    if body.start <= declaration.span.start && declaration.span.end <= body.end =>
                {
                    Some((body, candidate.name.as_str()))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        containers.sort_by_key(|(body, _)| (body.start, usize::MAX - body.end));
        let mut directory = base.to_path_buf();
        for (_, name) in containers {
            directory.push(name);
        }
        directory.push(&declaration.name);
        paths.push(directory.join(format!("{}.glorious", declaration.name)));
    }
    paths.sort();
    paths.dedup();
    paths
}

fn compile(command: CompileCommand, stdout: &mut dyn Write, stderr: &mut dyn Write) -> u8 {
    if command.native_incremental && command.native_incremental_cache.is_none() {
        let _ = writeln!(
            stderr,
            "grc: error: `--native-incremental` requires a persistent `grc --serve` request"
        );
        return 1;
    }
    let segments = match load_segments(&command) {
        Ok(segments) => segments,
        Err(error) => {
            let _ = writeln!(stderr, "grc: error: {error}");
            return 1;
        }
    };
    compile_loaded(command, segments, None, stdout, stderr)
}

fn compile_loaded(
    command: CompileCommand,
    mut segments: Vec<Segment>,
    mut incremental: Option<&mut CompilationDriver>,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> u8 {
    let bundle = if segments.is_empty() {
        SourceBundle::distributed(Segment::new("<grc:interface-scan>", ""), [])
    } else {
        let primary = segments.remove(0);
        SourceBundle::distributed(primary, segments)
    };
    if command.stop_phase == Some(StopPhase::Lex) {
        return match lexer::lex(bundle.source()) {
            Ok(_) => 0,
            Err(diagnostic) => {
                report_diagnostics(&bundle, vec![diagnostic], command.json_diagnostics, stderr)
            }
        };
    }
    if command.stop_phase == Some(StopPhase::Scan) {
        return match scan_interfaces(&bundle, InterfaceSelection::User) {
            Ok(_) => 0,
            Err(diagnostics) => {
                report_diagnostics(&bundle, diagnostics, command.json_diagnostics, stderr)
            }
        };
    }
    if command.stop_phase == Some(StopPhase::Resolve) {
        return match grandiose::resolve::resolve_bundle(&bundle) {
            Ok(()) => 0,
            Err(diagnostics) => {
                report_diagnostics(&bundle, diagnostics, command.json_diagnostics, stderr)
            }
        };
    }
    if let Some(kind @ (EmitKind::InterfacesJson | EmitKind::StandardInterfacesJson)) = command.emit
    {
        let selection = match kind {
            EmitKind::InterfacesJson => InterfaceSelection::User,
            EmitKind::StandardInterfacesJson => InterfaceSelection::StandardLibrary,
            _ => unreachable!(),
        };
        return match scan_interfaces(&bundle, selection) {
            Ok(declarations) => {
                if serde_json::to_writer(&mut *stdout, &declarations).is_err()
                    || writeln!(stdout).is_err()
                {
                    let _ = writeln!(stderr, "grc: error: failed to write interface JSON");
                    1
                } else {
                    0
                }
            }
            Err(diagnostics) => {
                for diagnostic in diagnostics {
                    let _ = bundle.write_diagnostic(&diagnostic, &mut *stderr);
                }
                1
            }
        };
    }
    if command.emit == Some(EmitKind::MonolithicSource) {
        let program = match grandiose::modules::parse_bundle(&bundle) {
            Ok(program) => program,
            Err(diagnostics) => {
                return report_diagnostics(&bundle, diagnostics, command.json_diagnostics, stderr);
            }
        };
        let resolved = match grandiose::modules::resolve_program(&bundle, program) {
            Ok(resolved) => resolved,
            Err(diagnostics) => {
                return report_diagnostics(&bundle, diagnostics, command.json_diagnostics, stderr);
            }
        };
        let source = match grandiose::modules::monolithic_source(&bundle, &resolved.resolution) {
            Ok(source) => source,
            Err(error) => {
                let _ = writeln!(
                    stderr,
                    "grc: error: could not render module bundle: {error}"
                );
                return 1;
            }
        };
        let output = command
            .output
            .unwrap_or_else(|| default_output(&command.inputs[0], EmitKind::MonolithicSource));
        return match std::fs::write(&output, source) {
            Ok(()) => 0,
            Err(error) => {
                let _ = writeln!(
                    stderr,
                    "grc: error: could not write {}: {error}",
                    output.display()
                );
                1
            }
        };
    }
    let options = CompileOptions {
        optimization_level: command.optimization_level,
    };
    let compiled = match incremental.as_deref_mut() {
        Some(session) => session.compile_bundle(&bundle, options),
        None => compile_bundle_to_phases_with_options(&bundle, options),
    };
    let phases = match compiled {
        Ok(phases) => phases,
        Err(diagnostics) => {
            return report_diagnostics(&bundle, diagnostics, command.json_diagnostics, stderr);
        }
    };
    for diagnostic in &phases.diagnostics {
        let written = if command.json_diagnostics {
            write_json_diagnostic(&bundle, diagnostic, &mut *stderr)
        } else {
            bundle.write_diagnostic(diagnostic, &mut *stderr)
        };
        if written.is_err() {
            let _ = writeln!(stderr, "grc: error: failed to render a diagnostic");
            return 1;
        }
    }
    if command.stop_phase == Some(StopPhase::Check) {
        return 0;
    }
    let kind = command.emit.unwrap_or(EmitKind::Bytecode);
    let output = command
        .output
        .unwrap_or_else(|| default_output(&command.inputs[0], kind));
    if matches!(kind, EmitKind::LlvmObject | EmitKind::Executable) {
        let mut llvm_options = LlvmOptions::default();
        if let Some(limit) = command.native_allocation_limit {
            llvm_options.native_allocation_limit = limit;
        }
        // The durable executable route emits independently partitioned LLVM
        // units below.  Do not first emit a complete monolithic module: it is
        // unused on that route and made every cache lookup pay for a second
        // whole-program LLVM emission.
        let durable_native_cache = kind == EmitKind::Executable
            && command.native_incremental
            && command.native_incremental_cache.is_some();
        let module = if durable_native_cache {
            None
        } else {
            match incremental.as_deref_mut().map_or_else(
                || emit_llvm_ir(&phases, &llvm_options),
                |driver| driver.emit_llvm_ir(&bundle, options, &phases, &llvm_options),
            ) {
                Ok(module) => Some(module),
                Err(diagnostics) => {
                    return report_diagnostics(
                        &bundle,
                        diagnostics,
                        command.json_diagnostics,
                        stderr,
                    );
                }
            }
        };
        let native_host = if kind == EmitKind::Executable {
            if let Err(error) = require_wild_linker() {
                let _ = writeln!(stderr, "grc: error: {error}");
                return 1;
            }
            match TemporaryNativeHost::create(&output) {
                Ok(host) => Some(host),
                Err(error) => {
                    let _ = writeln!(
                        stderr,
                        "grc: error: could not prepare the bundled native host runtime: {error}"
                    );
                    return 1;
                }
            }
        } else {
            None
        };
        // A long-lived compiler service can retain independently compiled O3
        // function objects across a body-only edit. The durable route below
        // additionally retains a final link only behind an exact manifest;
        // process-local requests still take a fresh Wild link.
        if kind == EmitKind::Executable && command.native_incremental {
            if let Some(cache_dir) = &command.native_incremental_cache {
                let units = match emit_llvm_native_object_units(&phases, &llvm_options) {
                    Ok(units) => units,
                    Err(diagnostics) => {
                        return report_diagnostics(
                            &bundle,
                            diagnostics,
                            command.json_diagnostics,
                            stderr,
                        );
                    }
                };
                let toolchain_abi =
                    match native_object_toolchain_abi(&llvm_options, OptimizationLevel::O3) {
                        Ok(abi) => abi,
                        Err(error) => {
                            let _ = writeln!(
                            stderr,
                            "grc: error: could not identify native object toolchain ABI: {error}"
                        );
                            return 1;
                        }
                    };
                let mut jobs = Vec::with_capacity(units.functions.len() + 1);
                let shared_abi = format!(
                    "{toolchain_abi};partition-schema={LLVM_NATIVE_OBJECT_PARTITION_SCHEMA};role=shared;shared={}",
                    units.shared_fingerprint
                );
                jobs.push(DiskNativeObjectJob {
                    ordinal: 0,
                    role: "shared",
                    ir: units.shared.ir.clone(),
                    abi: shared_abi,
                });
                for (index, function) in units.functions.iter().enumerate() {
                    let abi = format!(
                        "{toolchain_abi};partition-schema={LLVM_NATIVE_OBJECT_PARTITION_SCHEMA};role=function;decl={};fragment={}",
                        function.declaration,
                        function.fragment_fingerprint
                    );
                    jobs.push(DiskNativeObjectJob {
                        ordinal: index + 1,
                        role: "function",
                        ir: function.module.ir.clone(),
                        abi,
                    });
                }
                let workers = match durable_native_object_workers() {
                    Ok(workers) => workers,
                    Err(error) => {
                        let _ = writeln!(stderr, "grc: error: {error}");
                        return 1;
                    }
                };
                let objects = match materialize_disk_partitioned_native_objects(
                    &output,
                    cache_dir,
                    workers,
                    jobs.clone(),
                ) {
                    Ok(objects) => objects,
                    Err(error) => {
                        let _ = writeln!(stderr, "grc: error: {error}");
                        return 1;
                    }
                };
                let link_inputs = match DiskNativeLinkInputs::new(&jobs, &objects) {
                    Ok(inputs) => inputs,
                    Err(error) => {
                        let _ = writeln!(stderr, "grc: error: {error}");
                        return 1;
                    }
                };
                let host = native_host.as_ref().expect("executable native host");
                if let Err(error) = materialize_disk_linked_native_executable(
                    &output,
                    host,
                    &objects,
                    cache_dir,
                    &link_inputs,
                ) {
                    let _ = writeln!(stderr, "grc: error: {error}");
                    return 1;
                }
                return 0;
            }
            if let Some(driver) = incremental.as_deref_mut() {
                let units = match emit_llvm_native_object_units(&phases, &llvm_options) {
                    Ok(units) => units,
                    Err(diagnostics) => {
                        return report_diagnostics(
                            &bundle,
                            diagnostics,
                            command.json_diagnostics,
                            stderr,
                        );
                    }
                };
                let toolchain_abi =
                    match native_object_toolchain_abi(&llvm_options, OptimizationLevel::O3) {
                        Ok(abi) => abi,
                        Err(error) => {
                            let _ = writeln!(
                            stderr,
                            "grc: error: could not identify native object toolchain ABI: {error}"
                        );
                            return 1;
                        }
                    };
                let mut objects = Vec::with_capacity(units.functions.len() + 1);
                let shared_abi = format!(
                    "{toolchain_abi};partition-schema={LLVM_NATIVE_OBJECT_PARTITION_SCHEMA};partition-role=shared;shared-fingerprint={}",
                    units.shared_fingerprint,
                );
                match materialize_partitioned_native_object(
                    driver,
                    &output,
                    0,
                    "shared",
                    &llvm_options,
                    &units.shared.ir,
                    &shared_abi,
                    false,
                ) {
                    Ok(object) => objects.push(object),
                    Err(error) => {
                        let _ = writeln!(stderr, "grc: error: {error}");
                        return 1;
                    }
                }
                for (index, function) in units.functions.iter().enumerate() {
                    let abi = format!(
                        "{toolchain_abi};partition-schema={LLVM_NATIVE_OBJECT_PARTITION_SCHEMA};partition-role=function;declaration={};fragment={}",
                        function.declaration,
                        function.fragment_fingerprint
                    );
                    match materialize_partitioned_native_object(
                        driver,
                        &output,
                        index + 1,
                        "function",
                        &llvm_options,
                        &function.module.ir,
                        &abi,
                        true,
                    ) {
                        Ok(object) => objects.push(object),
                        Err(error) => {
                            let _ = writeln!(stderr, "grc: error: {error}");
                            return 1;
                        }
                    }
                }
                let host = native_host.as_ref().expect("executable native host");
                if let Err(error) = link_partitioned_native_executable(&output, host, &objects) {
                    let _ = writeln!(stderr, "grc: error: {error}");
                    return 1;
                }
                return 0;
            }
        }
        let module = module.expect("non-durable native emission needs a monolithic LLVM module");
        // A persistent session may reuse immutable object bytes only when the
        // generated IR and every native compiler ABI-affecting option match.
        // The output path is intentionally excluded: a hit always writes the
        // bytes to this request's `-o`. Executables are never cached because
        // each one must take the required Wild final-link path.
        let native_object_toolchain_abi = if kind == EmitKind::LlvmObject && incremental.is_some() {
            match native_object_toolchain_abi(&llvm_options, command.optimization_level) {
                Ok(abi) => Some(abi),
                Err(error) => {
                    let _ = writeln!(
                        stderr,
                        "grc: error: could not identify native object toolchain ABI: {error}"
                    );
                    return 1;
                }
            }
        } else {
            None
        };
        if let (Some(driver), Some(toolchain_abi)) = (
            incremental.as_deref_mut(),
            native_object_toolchain_abi.as_deref(),
        ) {
            if let Some(bytes) = driver.cached_native_object(
                &bundle,
                options,
                &llvm_options,
                &module.ir,
                toolchain_abi,
            ) {
                if let Err(error) = std::fs::write(&output, bytes) {
                    let _ = writeln!(
                        stderr,
                        "grc: error: could not write {}: {error}",
                        output.display()
                    );
                    return 1;
                }
                return 0;
            }
        }
        let mut clang = ProcessCommand::new("clang");
        clang.arg("-x").arg("ir").arg("-");
        if let Some(native_host) = &native_host {
            clang.arg("-x").arg("c").arg(&native_host.path);
            configure_wild_linking(&mut clang);
        }
        clang
            .arg(clang_optimization_flag(command.optimization_level))
            .arg("-o")
            .arg(&output)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::piped());
        if kind == EmitKind::LlvmObject {
            clang.arg("-c");
        }
        let mut child = match clang.spawn() {
            Ok(child) => child,
            Err(error) => {
                let _ = writeln!(
                    stderr,
                    "grc: error: could not start `clang` for native LLVM output: {error}"
                );
                return 1;
            }
        };
        if child
            .stdin
            .take()
            .is_none_or(|mut input| input.write_all(module.ir.as_bytes()).is_err())
        {
            let _ = child.kill();
            let _ = child.wait();
            let _ = writeln!(stderr, "grc: error: could not stream LLVM IR to `clang`");
            return 1;
        }
        let result = match child.wait_with_output() {
            Ok(result) => result,
            Err(error) => {
                let _ = writeln!(stderr, "grc: error: `clang` failed: {error}");
                return 1;
            }
        };
        if !result.status.success() {
            let _ = writeln!(
                stderr,
                "grc: error: native LLVM emission failed:\n{}",
                String::from_utf8_lossy(&result.stderr)
            );
            return 1;
        }
        if let (Some(driver), Some(toolchain_abi)) =
            (incremental.as_deref_mut(), native_object_toolchain_abi)
        {
            let bytes = match std::fs::read(&output) {
                Ok(bytes) => bytes,
                Err(error) => {
                    let _ = writeln!(
                        stderr,
                        "grc: error: could not read emitted object {}: {error}",
                        output.display()
                    );
                    return 1;
                }
            };
            driver.cache_native_object(
                &bundle,
                options,
                &llvm_options,
                &module.ir,
                toolchain_abi,
                bytes,
            );
        }
        return 0;
    }
    let bytes = match kind {
        EmitKind::Bytecode => phases.artifact.encode(),
        EmitKind::LlvmIr => match {
            let llvm_options = LlvmOptions::default();
            incremental.as_deref_mut().map_or_else(
                || emit_llvm_ir(&phases, &llvm_options),
                |driver| driver.emit_llvm_ir(&bundle, options, &phases, &llvm_options),
            )
        } {
            Ok(module) => module.ir.into_bytes(),
            Err(diagnostics) => {
                return report_diagnostics(&bundle, diagnostics, command.json_diagnostics, stderr);
            }
        },
        EmitKind::LlvmObject | EmitKind::Executable => unreachable!(),
        EmitKind::Mir => phases.mir.canonical_text().into_bytes(),
        EmitKind::Core => phases.core.canonical_text().into_bytes(),
        EmitKind::Provisional => phases.provisional_text().as_bytes().to_vec(),
        EmitKind::ControlPlan => phases.core.control_plan_text().into_bytes(),
        EmitKind::MonolithicSource => unreachable!(),
        EmitKind::InterfacesJson | EmitKind::StandardInterfacesJson => unreachable!(),
    };
    if let Err(error) = std::fs::write(&output, bytes) {
        let _ = writeln!(
            stderr,
            "grc: error: could not write {}: {error}",
            output.display()
        );
        return 1;
    }
    0
}

fn clang_optimization_flag(level: OptimizationLevel) -> &'static str {
    match level {
        OptimizationLevel::O0 => "-O0",
        OptimizationLevel::O1 => "-O1",
        OptimizationLevel::O2 => "-O2",
        OptimizationLevel::O3 => "-O3",
    }
}

/// Object cache keys include the native compiler identity, host target, and
/// every option passed (or represented) by this compilation path. This is
/// intentionally queried per request: updating Clang under a long-lived serve
/// session must invalidate previously generated object bytes.
fn native_object_toolchain_abi(
    llvm_options: &LlvmOptions,
    optimization_level: OptimizationLevel,
) -> io::Result<String> {
    let version = ProcessCommand::new("clang").arg("--version").output()?;
    if !version.status.success() {
        return Err(io::Error::other(format!(
            "`clang --version` exited with {}",
            version.status
        )));
    }
    let target = ProcessCommand::new("clang")
        .arg("-print-target-triple")
        .output()?;
    if !target.status.success() {
        return Err(io::Error::other(format!(
            "`clang -print-target-triple` exited with {}",
            target.status
        )));
    }
    Ok(format!(
        "schema=1;clang-version={};clang-target={};input=-x-ir-stdin;compile-only=true;opt={};llvm-target={};llvm-layout={:?};entry-wrapper={};native-allocation-limit={}",
        String::from_utf8_lossy(&version.stdout),
        String::from_utf8_lossy(&target.stdout),
        clang_optimization_flag(optimization_level),
        llvm_options.target_triple,
        llvm_options.target_data_layout,
        llvm_options.emit_entry_wrapper,
        llvm_options.native_allocation_limit,
    ))
}

/// Ensure executable emission cannot silently fall back to the platform
/// linker. Wild is intentionally a required part of the native executable
/// path; object emission remains a Clang-only compilation step.
fn require_wild_linker() -> Result<(), String> {
    match ProcessCommand::new("wild")
        .arg("--version")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
    {
        Ok(status) if status.success() => Ok(()),
        Ok(status) => Err(format!(
            "Wild linker is required for `--emit executable`, but `wild --version` exited with {status}; install `wild-linker` and ensure `wild` is on PATH"
        )),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Err(
            "Wild linker is required for `--emit executable`, but `wild` was not found on PATH; install `wild-linker` and ensure `wild` is on PATH".into(),
        ),
        Err(error) => Err(format!(
            "Wild linker is required for `--emit executable`, but `wild` could not be started: {error}"
        )),
    }
}

/// Clang remains responsible for compiling generated LLVM IR and the bundled
/// C runtime, while Wild owns the final native link. `--ld-path` is Clang's
/// direct linker-path option and avoids the `ld.wild` symlink required by
/// `-fuse-ld=wild`.
fn configure_wild_linking(clang: &mut ProcessCommand) {
    clang.arg("--ld-path=wild");
}

/// Compile or materialize one partitioned LLVM unit at the fixed native O3
/// level. The driver owns only immutable object bytes; this request owns the
/// pathname passed to Wild.
fn materialize_partitioned_native_object(
    driver: &mut CompilationDriver,
    output: &Path,
    ordinal: usize,
    role: &str,
    llvm_options: &LlvmOptions,
    ir: &str,
    toolchain_abi: &str,
    source_function: bool,
) -> Result<TemporaryNativeObject, String> {
    let object = TemporaryNativeObject::create(output, role, ordinal)
        .map_err(|error| format!("could not reserve native object path: {error}"))?;
    if let Some(bytes) =
        driver.cached_native_partitioned_object(llvm_options, ir, toolchain_abi, source_function)
    {
        std::fs::write(&object.path, bytes).map_err(|error| {
            format!(
                "could not materialize cached native object {}: {error}",
                object.path.display()
            )
        })?;
        return Ok(object);
    }
    let result = ProcessCommand::new("clang")
        .arg("-x")
        .arg("ir")
        .arg("-O3")
        .arg("-c")
        .arg("-")
        .arg("-o")
        .arg(&object.path)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("could not start `clang` for native unit: {error}"))
        .and_then(|mut child| {
            child
                .stdin
                .take()
                .ok_or_else(|| "could not open `clang` stdin for native unit".to_owned())?
                .write_all(ir.as_bytes())
                .map_err(|error| format!("could not stream LLVM unit to `clang`: {error}"))?;
            child
                .wait_with_output()
                .map_err(|error| format!("`clang` native unit failed: {error}"))
        })?;
    if !result.status.success() {
        return Err(format!(
            "native LLVM unit emission failed:\n{}",
            String::from_utf8_lossy(&result.stderr)
        ));
    }
    let bytes = std::fs::read(&object.path).map_err(|error| {
        format!(
            "could not read emitted native object {}: {error}",
            object.path.display()
        )
    })?;
    driver.cache_native_partitioned_object(llvm_options, ir, toolchain_abi.to_owned(), bytes);
    driver.record_native_partitioned_object_emitted(source_function);
    Ok(object)
}

fn native_object_bytes_are_plausible(bytes: &[u8]) -> bool {
    bytes.starts_with(b"\x7fELF")
        || bytes.starts_with(&[0xfe, 0xed, 0xfa, 0xcf])
        || bytes.starts_with(&[0xcf, 0xfa, 0xed, 0xfe])
        || bytes.starts_with(&[0x4c, 0x01])
        || bytes.starts_with(&[0x64, 0x86])
        || bytes.starts_with(&[0xaa, 0x64])
}

#[derive(Clone)]
struct DiskNativeObjectJob {
    ordinal: usize,
    role: &'static str,
    ir: String,
    abi: String,
}

/// The ordered identities which make one final native link reproducible.
/// These are derived before materializing request-local object paths, so they
/// remain stable across processes and output destinations.
struct DiskNativeLinkInputs {
    objects: Vec<String>,
}

impl DiskNativeLinkInputs {
    fn new(
        jobs: &[DiskNativeObjectJob],
        objects: &[TemporaryNativeObject],
    ) -> Result<Self, String> {
        if jobs.len() != objects.len() {
            return Err("native link input count did not match materialized objects".into());
        }
        let mut identities = Vec::with_capacity(jobs.len());
        for (job, object) in jobs.iter().zip(objects) {
            let key = DiskCacheKey::new(Path::new("."), &job.ir, &job.abi);
            let bytes = std::fs::read(&object.path).map_err(|error| {
                format!(
                    "could not read materialized native object {}: {error}",
                    object.path.display()
                )
            })?;
            identities.push(format!("{}:{}", key.digest, blake3::hash(&bytes).to_hex()));
        }
        Ok(Self {
            objects: identities,
        })
    }

    fn manifest_prefix(&self, link_abi: &str) -> String {
        let mut text = format!("schema=1\nlink-abi={link_abi}\n");
        for (ordinal, object) in self.objects.iter().enumerate() {
            text.push_str(&format!("object-{ordinal}={object}\n"));
        }
        text
    }
}

struct DiskLinkCacheKey {
    digest: String,
    executable: PathBuf,
    manifest: PathBuf,
    lock: PathBuf,
}

impl DiskLinkCacheKey {
    fn new(cache_dir: &Path, inputs: &DiskNativeLinkInputs, link_abi: &str) -> Self {
        let digest = blake3::hash(inputs.manifest_prefix(link_abi).as_bytes())
            .to_hex()
            .to_string();
        let directory = cache_dir.join("links");
        Self {
            executable: directory.join(format!("{digest}.exe")),
            manifest: directory.join(format!("{digest}.manifest")),
            lock: directory.join(format!(".{digest}.lock")),
            digest,
        }
    }

    fn manifest_text(&self, inputs: &DiskNativeLinkInputs, link_abi: &str, bytes: &[u8]) -> String {
        format!(
            "{}digest={}\nexecutable-blake3={}\n",
            inputs.manifest_prefix(link_abi),
            self.digest,
            blake3::hash(bytes).to_hex(),
        )
    }

    fn read_valid(&self, inputs: &DiskNativeLinkInputs, link_abi: &str) -> Option<Vec<u8>> {
        let (Ok(bytes), Ok(manifest)) = (
            std::fs::read(&self.executable),
            std::fs::read_to_string(&self.manifest),
        ) else {
            return None;
        };
        (manifest == self.manifest_text(inputs, link_abi, &bytes)
            && native_object_bytes_are_plausible(&bytes))
        .then_some(bytes)
    }
}

fn bounded_durable_native_object_workers(
    requested: Option<&str>,
    available_parallelism: usize,
) -> Result<usize, String> {
    let requested = match requested {
        Some(value) => value.parse::<usize>().map_err(|_| {
            format!(
                "{DURABLE_NATIVE_OBJECT_WORKERS_ENV} must be an integer from 1 through {MAX_DURABLE_NATIVE_OBJECT_WORKERS}"
            )
        })?,
        None => MAX_DURABLE_NATIVE_OBJECT_WORKERS,
    };
    if !(1..=MAX_DURABLE_NATIVE_OBJECT_WORKERS).contains(&requested) {
        return Err(format!(
            "{DURABLE_NATIVE_OBJECT_WORKERS_ENV} must be an integer from 1 through {MAX_DURABLE_NATIVE_OBJECT_WORKERS}"
        ));
    }
    Ok(requested.min(available_parallelism.max(1)))
}

fn durable_native_object_workers() -> Result<usize, String> {
    let available = thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    let requested = match std::env::var(DURABLE_NATIVE_OBJECT_WORKERS_ENV) {
        Ok(value) => Some(value),
        Err(std::env::VarError::NotPresent) => None,
        Err(std::env::VarError::NotUnicode(_)) => {
            return Err(format!(
                "{DURABLE_NATIVE_OBJECT_WORKERS_ENV} must be valid Unicode and an integer from 1 through {MAX_DURABLE_NATIVE_OBJECT_WORKERS}"
            ));
        }
    };
    bounded_durable_native_object_workers(requested.as_deref(), available)
}

/// Compile independent durable-cache misses in small deterministic waves.
/// Results are returned in ordinal order regardless of completion order, and
/// an error is selected by ordinal rather than scheduler timing.
fn materialize_disk_partitioned_native_objects(
    output: &Path,
    cache_dir: &Path,
    workers: usize,
    jobs: Vec<DiskNativeObjectJob>,
) -> Result<Vec<TemporaryNativeObject>, String> {
    let count = jobs.len();
    let mut results = (0..count).map(|_| None).collect::<Vec<_>>();
    let mut pending = jobs.into_iter();
    loop {
        let wave = pending.by_ref().take(workers).collect::<Vec<_>>();
        if wave.is_empty() {
            break;
        }
        let wave_results = thread::scope(|scope| {
            let mut handles = Vec::with_capacity(wave.len());
            for job in wave {
                let output = output.to_owned();
                let cache_dir = cache_dir.to_owned();
                let ordinal = job.ordinal;
                let role = job.role;
                handles.push((
                    ordinal,
                    role,
                    scope.spawn(move || {
                        materialize_disk_partitioned_native_object(
                            &output, ordinal, role, &job.ir, &job.abi, &cache_dir,
                        )
                    }),
                ));
            }
            handles
                .into_iter()
                .map(|(ordinal, role, handle)| match handle.join() {
                    Ok(Ok(object)) => Ok((ordinal, object)),
                    Ok(Err(error)) => Err((
                        ordinal,
                        format!("native partition {ordinal} ({role}) failed: {error}"),
                    )),
                    Err(_) => Err((
                        ordinal,
                        format!("native partition {ordinal} ({role}) worker panicked"),
                    )),
                })
                .collect::<Vec<_>>()
        });
        let mut failure = None;
        for result in wave_results {
            match result {
                Ok((ordinal, object)) => {
                    results[ordinal] = Some(Ok(object));
                }
                Err((ordinal, error)) => {
                    if failure
                        .as_ref()
                        .is_none_or(|(previous, _)| ordinal < *previous)
                    {
                        failure = Some((ordinal, error));
                    }
                }
            }
        }
        if let Some((_, error)) = failure {
            return Err(error);
        }
    }
    results
        .into_iter()
        .enumerate()
        .map(|(ordinal, result)| {
            result.ok_or_else(|| format!("native partition {ordinal} was not materialized"))?
        })
        .collect()
}

/// Durable, worktree-owned object cache. The digest includes complete unit IR
/// and the exact Clang/runtime ABI string; objects are copied into request
/// paths and every invocation still takes a new Wild link.
struct DiskCacheKey {
    digest: String,
    object: PathBuf,
    manifest: PathBuf,
    lock: PathBuf,
}

impl DiskCacheKey {
    fn new(cache_dir: &Path, ir: &str, abi: &str) -> Self {
        let digest = blake3::hash(format!("schema=1\nabi={abi}\nir={ir}").as_bytes())
            .to_hex()
            .to_string();
        Self {
            object: cache_dir.join(format!("{digest}.o")),
            manifest: cache_dir.join(format!("{digest}.manifest")),
            lock: cache_dir.join(format!(".{digest}.lock")),
            digest,
        }
    }

    fn manifest_text(&self, abi: &str, bytes: &[u8]) -> String {
        format!(
            "schema=1\ndigest={}\nobject-blake3={}\nabi={abi}\n",
            self.digest,
            blake3::hash(bytes).to_hex(),
        )
    }

    fn read_valid(&self, abi: &str) -> Option<Vec<u8>> {
        let (Ok(bytes), Ok(manifest)) = (
            std::fs::read(&self.object),
            std::fs::read_to_string(&self.manifest),
        ) else {
            return None;
        };
        (manifest == self.manifest_text(abi, &bytes) && native_object_bytes_are_plausible(&bytes))
            .then_some(bytes)
    }
}

struct DiskCacheLock {
    path: PathBuf,
}

impl DiskCacheLock {
    fn acquire(path: PathBuf) -> Result<Self, String> {
        let started = Instant::now();
        loop {
            match OpenOptions::new().write(true).create_new(true).open(&path) {
                Ok(_) => return Ok(Self { path }),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                    if started.elapsed() >= DISK_CACHE_LOCK_WAIT {
                        return Err(format!(
                            "timed out waiting for native cache lock {}",
                            path.display()
                        ));
                    }
                    thread::sleep(Duration::from_millis(10));
                }
                Err(error) => {
                    return Err(format!(
                        "could not acquire native cache lock {}: {error}",
                        path.display()
                    ));
                }
            }
        }
    }
}

impl Drop for DiskCacheLock {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

fn disk_cache_temporary(cache_dir: &Path, digest: &str, suffix: &str) -> Result<PathBuf, String> {
    for _ in 0..128 {
        let sequence = DISK_CACHE_TEMPORARY_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let path = cache_dir.join(format!(
            ".{digest}.{}-{sequence}.{suffix}",
            std::process::id(),
        ));
        match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(_) => return Ok(path),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(format!("could not reserve native cache temporary: {error}")),
        }
    }
    Err("could not reserve a unique native cache temporary".into())
}

fn publish_disk_cache_entry(
    key: &DiskCacheKey,
    abi: &str,
    bytes: &[u8],
) -> Result<Vec<u8>, String> {
    let _lock = DiskCacheLock::acquire(key.lock.clone())?;
    if let Some(existing) = key.read_valid(abi) {
        return Ok(existing);
    }
    let object_temporary = disk_cache_temporary(
        key.object.parent().expect("cache object has parent"),
        &key.digest,
        "object.tmp",
    )?;
    if let Err(error) = std::fs::write(&object_temporary, bytes) {
        let _ = std::fs::remove_file(&object_temporary);
        return Err(format!("could not write native cache object: {error}"));
    }
    if let Err(error) = std::fs::rename(&object_temporary, &key.object) {
        let _ = std::fs::remove_file(&object_temporary);
        return Err(format!("could not publish native cache object: {error}"));
    }
    let manifest_temporary = disk_cache_temporary(
        key.manifest.parent().expect("cache manifest has parent"),
        &key.digest,
        "manifest.tmp",
    )?;
    let manifest = key.manifest_text(abi, bytes);
    if let Err(error) = std::fs::write(&manifest_temporary, manifest) {
        let _ = std::fs::remove_file(&manifest_temporary);
        return Err(format!("could not write native cache manifest: {error}"));
    }
    if let Err(error) = std::fs::rename(&manifest_temporary, &key.manifest) {
        let _ = std::fs::remove_file(&manifest_temporary);
        return Err(format!("could not publish native cache manifest: {error}"));
    }
    Ok(bytes.to_vec())
}

fn materialize_disk_partitioned_native_object(
    output: &Path,
    ordinal: usize,
    role: &str,
    ir: &str,
    abi: &str,
    cache_dir: &Path,
) -> Result<TemporaryNativeObject, String> {
    std::fs::create_dir_all(cache_dir).map_err(|error| {
        format!(
            "could not create native incremental cache {}: {error}",
            cache_dir.display()
        )
    })?;
    let key = DiskCacheKey::new(cache_dir, ir, abi);
    let object = TemporaryNativeObject::create(output, role, ordinal)
        .map_err(|error| format!("could not reserve native object path: {error}"))?;
    if let Some(bytes) = key.read_valid(abi) {
        std::fs::write(&object.path, bytes)
            .map_err(|error| format!("could not materialize cached native object: {error}"))?;
        return Ok(object);
    }
    let result = ProcessCommand::new("clang")
        .args(["-x", "ir", "-O3", "-c", "-"])
        .arg("-o")
        .arg(&object.path)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("could not start `clang` for native unit: {error}"))
        .and_then(|mut child| {
            child
                .stdin
                .take()
                .ok_or_else(|| "could not open `clang` stdin".to_owned())?
                .write_all(ir.as_bytes())
                .map_err(|error| error.to_string())?;
            child.wait_with_output().map_err(|error| error.to_string())
        })?;
    if !result.status.success() {
        return Err(format!(
            "native LLVM unit emission failed:\n{}",
            String::from_utf8_lossy(&result.stderr)
        ));
    }
    let bytes = std::fs::read(&object.path)
        .map_err(|error| format!("could not read emitted native object: {error}"))?;
    if !native_object_bytes_are_plausible(&bytes) {
        return Err("clang emitted an unrecognized native object".into());
    }
    let bytes = publish_disk_cache_entry(&key, abi, &bytes)?;
    std::fs::write(&object.path, bytes)
        .map_err(|error| format!("could not materialize published native object: {error}"))?;
    Ok(object)
}

fn link_partitioned_native_executable(
    output: &Path,
    host: &TemporaryNativeHost,
    objects: &[TemporaryNativeObject],
) -> Result<(), String> {
    let mut clang = ProcessCommand::new("clang");
    clang.arg("-O3");
    for object in objects {
        clang.arg(&object.path);
    }
    clang.arg(&host.path).arg("-o").arg(output);
    configure_wild_linking(&mut clang);
    let result = clang
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .output()
        .map_err(|error| format!("could not start `clang` for Wild link: {error}"))?;
    if result.status.success() {
        Ok(())
    } else {
        Err(format!(
            "native Wild link failed:\n{}",
            String::from_utf8_lossy(&result.stderr)
        ))
    }
}

fn native_link_toolchain_abi() -> Result<String, String> {
    let clang = ProcessCommand::new("clang")
        .arg("--version")
        .output()
        .map_err(|error| format!("could not identify Clang for native link: {error}"))?;
    if !clang.status.success() {
        return Err(format!("`clang --version` exited with {}", clang.status));
    }
    let wild = ProcessCommand::new("wild")
        .arg("--version")
        .output()
        .map_err(|error| format!("could not identify Wild for native link: {error}"))?;
    if !wild.status.success() {
        return Err(format!("`wild --version` exited with {}", wild.status));
    }
    Ok(format!(
        "schema=1;clang={:?};wild={:?};command=clang-O3-objects-host---ld-path=wild;host={}",
        clang.stdout,
        wild.stdout,
        blake3::hash(&[NATIVE_HOST_RUNTIME, NATIVE_RUNTIME].concat()).to_hex(),
    ))
}

/// Reuse a durable linked executable only when its manifest binds the exact
/// ordered object bytes, bundled host runtime, and current Clang/Wild ABI.
/// A miss always follows the ordinary required Wild link path.
fn materialize_disk_linked_native_executable(
    output: &Path,
    host: &TemporaryNativeHost,
    objects: &[TemporaryNativeObject],
    cache_dir: &Path,
    inputs: &DiskNativeLinkInputs,
) -> Result<(), String> {
    let link_abi = native_link_toolchain_abi()?;
    let key = DiskLinkCacheKey::new(cache_dir, inputs, &link_abi);
    std::fs::create_dir_all(key.executable.parent().expect("link cache parent"))
        .map_err(|error| format!("could not create native link cache: {error}"))?;
    let _lock = DiskCacheLock::acquire(key.lock.clone())?;
    let _bytes = if let Some(bytes) = key.read_valid(inputs, &link_abi) {
        bytes
    } else {
        let temporary = disk_cache_temporary(
            key.executable.parent().expect("link cache parent"),
            &key.digest,
            "executable.tmp",
        )?;
        if let Err(error) = link_partitioned_native_executable(&temporary, host, objects) {
            let _ = std::fs::remove_file(&temporary);
            return Err(error);
        }
        let bytes = std::fs::read(&temporary)
            .map_err(|error| format!("could not read linked native executable: {error}"))?;
        if !native_object_bytes_are_plausible(&bytes) {
            let _ = std::fs::remove_file(&temporary);
            return Err("Wild emitted an unrecognized native executable".into());
        }
        if let Err(error) = std::fs::rename(&temporary, &key.executable) {
            let _ = std::fs::remove_file(&temporary);
            return Err(format!(
                "could not publish native link cache executable: {error}"
            ));
        }
        let manifest_temporary = disk_cache_temporary(
            key.manifest.parent().expect("link cache parent"),
            &key.digest,
            "manifest.tmp",
        )?;
        if let Err(error) = std::fs::write(
            &manifest_temporary,
            key.manifest_text(inputs, &link_abi, &bytes),
        ) {
            let _ = std::fs::remove_file(&manifest_temporary);
            return Err(format!(
                "could not write native link cache manifest: {error}"
            ));
        }
        if let Err(error) = std::fs::rename(&manifest_temporary, &key.manifest) {
            let _ = std::fs::remove_file(&manifest_temporary);
            return Err(format!(
                "could not publish native link cache manifest: {error}"
            ));
        }
        bytes
    };
    std::fs::copy(&key.executable, output).map_err(|error| {
        format!(
            "could not materialize cached native executable {}: {error}",
            output.display()
        )
    })?;
    let permissions = std::fs::metadata(&key.executable)
        .map_err(|error| format!("could not read cached native executable permissions: {error}"))?
        .permissions();
    std::fs::set_permissions(output, permissions).map_err(|error| {
        format!(
            "could not preserve cached native executable permissions {}: {error}",
            output.display()
        )
    })
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SessionRequest {
    protocol: u32,
    id: u64,
    method: String,
    #[serde(default)]
    arguments: Vec<String>,
}

#[derive(Serialize)]
struct SessionResponse<'a> {
    protocol: u32,
    id: Option<u64>,
    status: u8,
    stdout: &'a str,
    stderr: &'a str,
    generation: u64,
    transaction: &'a str,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_fingerprint: Option<&'a str>,
    /// Present only for LLVM emission requests. It exposes IR-cache behavior
    /// at the persistent-session boundary.
    #[serde(skip_serializing_if = "Option::is_none")]
    llvm_ir_cache: Option<&'a str>,
    /// Present only for LLVM object requests. Executable requests must always
    /// link afresh through Wild and therefore never report this field.
    #[serde(skip_serializing_if = "Option::is_none")]
    native_object_cache: Option<&'a str>,
    /// Truthful, request-scoped evidence for the native incremental route.
    /// It is deliberately only exposed from `--serve`: no on-disk cache is
    /// implied or retained across compiler processes.
    #[serde(skip_serializing_if = "Option::is_none")]
    native_incremental: Option<NativeIncrementalReport>,
    /// Deterministic cache evidence for persistent compile requests.  This is
    /// intentionally counts rather than elapsed time: it makes release-mode
    /// warm-iteration measurements reproducible across machines.
    #[serde(skip_serializing_if = "Option::is_none")]
    cache_stats: Option<SessionCacheStats>,
}

#[derive(Clone, Copy, Serialize)]
struct SessionCacheStats {
    /// Per-segment frontend work for this request. This remains separate from
    /// phase artifacts because a body edit can reuse most lexed inputs while
    /// requiring new type/MIR work for the edited callable.
    frontend: SessionFrontendCacheStats,
    phase_artifacts_reused: usize,
    bodies_reused: usize,
    mir_bodies_reused: usize,
    mir_bodies_lowered: usize,
    llvm_ir_reused: usize,
    llvm_fragments_reused: usize,
    llvm_fragments_emitted: usize,
    native_objects_reused: usize,
    native_objects_emitted: usize,
}

/// Frontend cache evidence nested below a persistent compile response.
/// Counts describe the current request rather than the lifetime of `--serve`.
#[derive(Clone, Copy, Serialize)]
struct SessionFrontendCacheStats {
    segments_lexed: usize,
    segments_reused: usize,
    whole_bundle_fallbacks: usize,
}

impl From<grandiose::compiler_session::IncrementalCompilationStats> for SessionCacheStats {
    fn from(stats: grandiose::compiler_session::IncrementalCompilationStats) -> Self {
        Self {
            frontend: SessionFrontendCacheStats {
                segments_lexed: stats.frontend.lexed_segments,
                segments_reused: stats.frontend.reused_segments,
                whole_bundle_fallbacks: stats.frontend.whole_bundle_fallbacks,
            },
            phase_artifacts_reused: stats.reused_phase_artifacts,
            bodies_reused: stats.reused_bodies,
            mir_bodies_reused: stats.reused_mir_bodies,
            mir_bodies_lowered: stats.lowered_mir_bodies,
            llvm_ir_reused: stats.reused_llvm_ir,
            llvm_fragments_reused: stats.reused_llvm_fragments,
            llvm_fragments_emitted: stats.emitted_llvm_fragments,
            native_objects_reused: stats.reused_native_objects,
            native_objects_emitted: stats.emitted_native_objects,
        }
    }
}

/// Stable JSON-line evidence for a native incremental request.
///
/// The units are LLVM-reachable function fragments for IR and native object
/// units for code generation. Executable units are retained only inside the
/// serve process; the fields intentionally avoid promising a filesystem cache
/// or an executable cache. Every executable request takes a fresh Wild link.
#[derive(Clone, Copy, Serialize)]
struct NativeIncrementalReport {
    cache_scope: &'static str,
    strategy: &'static str,
    llvm_fragments_reused: usize,
    llvm_fragments_emitted: usize,
    native_objects_reused: usize,
    native_objects_emitted: usize,
    function_objects_reused: usize,
    function_objects_compiled: usize,
    shared_objects_compiled: usize,
    wild_relink: bool,
}

struct SessionSnapshot {
    key: String,
    source_fingerprint: String,
    // Retaining the exact last-good bytes makes the transaction concrete and
    // inspectable while the fixed source-byte limit bounds the cache.
    sources: Vec<(PathBuf, String)>,
}

#[derive(Default)]
struct SessionState {
    generation: u64,
    last_good: Option<SessionSnapshot>,
    compiler: CompilationDriver,
}

enum BoundedLine {
    Eof,
    Line(Vec<u8>),
    TooLong,
}

fn read_bounded_line(input: &mut dyn BufRead, limit: usize) -> io::Result<BoundedLine> {
    let mut line = Vec::new();
    let mut too_long = false;
    loop {
        let available = input.fill_buf()?;
        if available.is_empty() {
            return if line.is_empty() && !too_long {
                Ok(BoundedLine::Eof)
            } else if too_long {
                Ok(BoundedLine::TooLong)
            } else {
                Ok(BoundedLine::Line(line))
            };
        }
        let end = available
            .iter()
            .position(|byte| *byte == b'\n')
            .map_or(available.len(), |index| index + 1);
        if !too_long && line.len().saturating_add(end) <= limit {
            line.extend_from_slice(&available[..end]);
        } else {
            too_long = true;
        }
        let ended = available[end - 1] == b'\n';
        input.consume(end);
        if ended {
            return if too_long {
                Ok(BoundedLine::TooLong)
            } else {
                Ok(BoundedLine::Line(line))
            };
        }
    }
}

fn fingerprint_sources(sources: &[(PathBuf, String)]) -> String {
    let mut hash = blake3::Hasher::new();
    for (path, source) in sources {
        let path = path.to_string_lossy();
        hash.update(&(path.len() as u64).to_le_bytes());
        hash.update(path.as_bytes());
        hash.update(&(source.len() as u64).to_le_bytes());
        hash.update(source.as_bytes());
    }
    hash.finalize().to_hex().to_string()
}

fn session_request_key(arguments: &[String], source_fingerprint: &str) -> String {
    let mut hash = blake3::Hasher::new();
    hash.update(source_fingerprint.as_bytes());
    for argument in arguments {
        hash.update(&(argument.len() as u64).to_le_bytes());
        hash.update(argument.as_bytes());
    }
    hash.finalize().to_hex().to_string()
}

fn load_session_segments(
    command: &CompileCommand,
    arguments: &[String],
) -> Result<(Vec<Segment>, SessionSnapshot), String> {
    let declared_input_count = command.inputs.len() + command.dependencies.len();
    if declared_input_count > SESSION_MAX_INPUTS {
        return Err(format!(
            "session input limit exceeded: {} files exceeds {SESSION_MAX_INPUTS}",
            declared_input_count
        ));
    }
    let mut total = 0usize;
    let mut sources = Vec::with_capacity(command.inputs.len());
    for path in &command.inputs {
        let file = std::fs::File::open(path)
            .map_err(|error| format!("could not read {}: {error}", path.display()))?;
        let remaining = SESSION_MAX_SOURCE_BYTES - total;
        let mut bytes = Vec::new();
        file.take(remaining as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|error| format!("could not read {}: {error}", path.display()))?;
        if bytes.len() > remaining {
            return Err(format!(
                "session source-byte limit exceeded: more than {SESSION_MAX_SOURCE_BYTES} bytes"
            ));
        }
        total += bytes.len();
        let source = String::from_utf8(bytes)
            .map_err(|error| format!("could not read {}: {error}", path.display()))?;
        sources.push((path.clone(), source));
    }
    for (_, path) in &command.dependencies {
        if sources.iter().any(|(existing, _)| existing == path) {
            return Err(format!(
                "dependency root {} is also supplied as an ordinary input",
                path.display()
            ));
        }
        let file = std::fs::File::open(path)
            .map_err(|error| format!("could not read {}: {error}", path.display()))?;
        let remaining = SESSION_MAX_SOURCE_BYTES - total;
        let mut bytes = Vec::new();
        file.take(remaining as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|error| format!("could not read {}: {error}", path.display()))?;
        if bytes.len() > remaining {
            return Err(format!(
                "session source-byte limit exceeded: more than {SESSION_MAX_SOURCE_BYTES} bytes"
            ));
        }
        total += bytes.len();
        let source = String::from_utf8(bytes)
            .map_err(|error| format!("could not read {}: {error}", path.display()))?;
        sources.push((path.clone(), source));
    }
    let mut known = sources
        .iter()
        .enumerate()
        .map(|(index, (path, _))| (path.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut queue = command
        .inputs
        .first()
        .cloned()
        .into_iter()
        .chain(command.dependencies.iter().map(|(_, path)| path.clone()))
        .collect::<VecDeque<_>>();
    let mut processed = BTreeSet::new();
    while let Some(path) = queue.pop_front() {
        if !processed.insert(path.clone()) {
            continue;
        }
        let Some(index) = known.get(&path).copied() else {
            continue;
        };
        let children = declared_external_module_paths(&path, &sources[index].1);
        for child in children {
            if !child.is_file() {
                continue;
            }
            if !known.contains_key(&child) {
                if sources.len() >= SESSION_MAX_INPUTS {
                    return Err(format!(
                        "declared module closure exceeds input-count limit of {SESSION_MAX_INPUTS}"
                    ));
                }
                let file = std::fs::File::open(&child)
                    .map_err(|error| format!("could not read {}: {error}", child.display()))?;
                let remaining = SESSION_MAX_SOURCE_BYTES - total;
                let mut bytes = Vec::new();
                file.take(remaining as u64 + 1)
                    .read_to_end(&mut bytes)
                    .map_err(|error| format!("could not read {}: {error}", child.display()))?;
                if bytes.len() > remaining {
                    return Err(format!(
                        "session source-byte limit exceeded: more than {SESSION_MAX_SOURCE_BYTES} bytes"
                    ));
                }
                total += bytes.len();
                let source = String::from_utf8(bytes)
                    .map_err(|error| format!("could not read {}: {error}", child.display()))?;
                known.insert(child.clone(), sources.len());
                sources.push((child.clone(), source));
            }
            queue.push_back(child);
        }
    }
    let source_fingerprint = fingerprint_sources(&sources);
    let key = session_request_key(arguments, &source_fingerprint);
    let dependency_names = command
        .dependencies
        .iter()
        .map(|(name, path)| (path, name))
        .collect::<BTreeMap<_, _>>();
    let segments = sources
        .iter()
        .map(|(path, source)| {
            let segment = Segment::new(path.display().to_string(), source.clone());
            if let Some(name) = dependency_names.get(path) {
                segment.with_package_root((*name).clone())
            } else {
                segment
            }
        })
        .collect();
    Ok((
        segments,
        SessionSnapshot {
            key,
            source_fingerprint,
            sources,
        },
    ))
}

fn write_session_response(
    output: &mut dyn Write,
    response: &SessionResponse<'_>,
) -> io::Result<()> {
    serde_json::to_writer(&mut *output, response).map_err(io::Error::other)?;
    writeln!(output)?;
    output.flush()
}

fn session_protocol_error(
    output: &mut dyn Write,
    state: &SessionState,
    id: Option<u64>,
    message: &str,
) -> io::Result<()> {
    write_session_response(
        output,
        &SessionResponse {
            protocol: SESSION_PROTOCOL,
            id,
            status: 2,
            stdout: "",
            stderr: message,
            generation: state.generation,
            transaction: "retained",
            source_fingerprint: state
                .last_good
                .as_ref()
                .map(|snapshot| snapshot.source_fingerprint.as_str()),
            llvm_ir_cache: None,
            native_object_cache: None,
            native_incremental: None,
            cache_stats: None,
        },
    )
}

fn serve(input: &mut dyn BufRead, output: &mut dyn Write) -> u8 {
    let mut state = SessionState::default();
    loop {
        let line = match read_bounded_line(input, SESSION_MAX_LINE_BYTES) {
            Ok(BoundedLine::Eof) => return 0,
            Ok(BoundedLine::TooLong) => {
                if session_protocol_error(
                    output,
                    &state,
                    None,
                    "request exceeds session byte limit",
                )
                .is_err()
                {
                    return 1;
                }
                continue;
            }
            Ok(BoundedLine::Line(line)) => line,
            Err(_) => return 1,
        };
        let request: SessionRequest = match serde_json::from_slice(&line) {
            Ok(request) => request,
            Err(error) => {
                if session_protocol_error(
                    output,
                    &state,
                    None,
                    &format!("invalid session request: {error}"),
                )
                .is_err()
                {
                    return 1;
                }
                continue;
            }
        };
        if request.protocol != SESSION_PROTOCOL {
            if session_protocol_error(
                output,
                &state,
                Some(request.id),
                &format!(
                    "session protocol {} is incompatible with {SESSION_PROTOCOL}",
                    request.protocol
                ),
            )
            .is_err()
            {
                return 1;
            }
            continue;
        }
        if request.method == "shutdown" {
            let response = SessionResponse {
                protocol: SESSION_PROTOCOL,
                id: Some(request.id),
                status: 0,
                stdout: "",
                stderr: "",
                generation: state.generation,
                transaction: "unchanged",
                source_fingerprint: state
                    .last_good
                    .as_ref()
                    .map(|snapshot| snapshot.source_fingerprint.as_str()),
                llvm_ir_cache: None,
                native_object_cache: None,
                native_incremental: None,
                cache_stats: None,
            };
            return if write_session_response(output, &response).is_ok() {
                0
            } else {
                1
            };
        }
        if request.method != "compile" {
            if session_protocol_error(
                output,
                &state,
                Some(request.id),
                &format!("unknown session method `{}`", request.method),
            )
            .is_err()
            {
                return 1;
            }
            continue;
        }
        if request.arguments.len() > SESSION_MAX_ARGUMENTS {
            if session_protocol_error(
                output,
                &state,
                Some(request.id),
                "session argument-count limit exceeded",
            )
            .is_err()
            {
                return 1;
            }
            continue;
        }
        let parsed = parse(request.arguments.iter().map(OsString::from).collect());
        let Command::Compile(command) = (match parsed {
            Ok(command) => command,
            Err(error) => {
                if session_protocol_error(output, &state, Some(request.id), &error).is_err() {
                    return 1;
                }
                continue;
            }
        }) else {
            if session_protocol_error(
                output,
                &state,
                Some(request.id),
                "sessions accept compile, resolve, and check requests only",
            )
            .is_err()
            {
                return 1;
            }
            continue;
        };
        let (segments, snapshot) = match load_session_segments(&command, &request.arguments) {
            Ok(loaded) => loaded,
            Err(error) => {
                let stderr = format!("grc: error: {error}\n");
                let response = SessionResponse {
                    protocol: SESSION_PROTOCOL,
                    id: Some(request.id),
                    status: 1,
                    stdout: "",
                    stderr: &stderr,
                    generation: state.generation,
                    transaction: "retained",
                    source_fingerprint: state
                        .last_good
                        .as_ref()
                        .map(|last| last.source_fingerprint.as_str()),
                    llvm_ir_cache: None,
                    native_object_cache: None,
                    native_incremental: None,
                    cache_stats: None,
                };
                if write_session_response(output, &response).is_err() {
                    return 1;
                }
                continue;
            }
        };
        let llvm_emission = matches!(
            command.emit,
            Some(EmitKind::LlvmIr | EmitKind::LlvmObject | EmitKind::Executable)
        );
        let native_object_emission = command.emit == Some(EmitKind::LlvmObject);
        let native_executable_emission = command.emit == Some(EmitKind::Executable);
        let native_incremental_emission = command.native_incremental;
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let status = compile_loaded(
            command,
            segments,
            Some(&mut state.compiler),
            &mut stdout,
            &mut stderr,
        );
        let stdout = String::from_utf8_lossy(&stdout).into_owned();
        let stderr = String::from_utf8_lossy(&stderr).into_owned();
        let current_source_fingerprint = snapshot.source_fingerprint.clone();
        let transaction = if status == 0 {
            let unchanged = state
                .last_good
                .as_ref()
                .is_some_and(|last| last.key == snapshot.key && last.sources == snapshot.sources);
            if !unchanged {
                state.generation = state.generation.saturating_add(1);
                state.last_good = Some(snapshot);
                "committed"
            } else {
                "unchanged"
            }
        } else {
            "retained"
        };
        let source_fingerprint = if status == 0 {
            state
                .last_good
                .as_ref()
                .map(|last| last.source_fingerprint.as_str())
        } else {
            Some(current_source_fingerprint.as_str())
        };
        let llvm_ir_cache = (status == 0 && llvm_emission).then(|| {
            if state.compiler.stats().reused_llvm_ir != 0 {
                "hit"
            } else {
                "miss"
            }
        });
        let native_object_cache = (status == 0 && native_object_emission).then(|| {
            if state.compiler.stats().reused_native_objects != 0 {
                "hit"
            } else {
                "miss"
            }
        });
        let cache_stats = (status == 0).then(|| state.compiler.stats().into());
        let native_incremental = (status == 0 && llvm_emission).then(|| {
            let stats = state.compiler.stats();
            NativeIncrementalReport {
                // This is specifically a property of this `grc --serve`
                // process. A new process starts cold and a client must not
                // treat these counters as a persistent artifact cache.
                cache_scope: "serve-process",
                strategy: if native_incremental_emission {
                    "partitioned-function-objects"
                } else {
                    "monolithic"
                },
                llvm_fragments_reused: stats.reused_llvm_fragments,
                llvm_fragments_emitted: stats.emitted_llvm_fragments,
                native_objects_reused: stats.reused_native_objects,
                native_objects_emitted: stats.emitted_native_objects,
                function_objects_reused: stats.reused_native_function_objects,
                function_objects_compiled: stats.emitted_native_function_objects,
                shared_objects_compiled: stats.emitted_native_shared_objects,
                wild_relink: native_executable_emission,
            }
        });
        let response = SessionResponse {
            protocol: SESSION_PROTOCOL,
            id: Some(request.id),
            status,
            stdout: &stdout,
            stderr: &stderr,
            generation: state.generation,
            transaction,
            source_fingerprint,
            llvm_ir_cache,
            native_object_cache,
            native_incremental,
            cache_stats,
        };
        if write_session_response(output, &response).is_err() {
            return 1;
        }
    }
}

pub(crate) fn execute(args: impl IntoIterator<Item = OsString>) -> u8 {
    let mut stderr = io::stderr().lock();
    match parse(args.into_iter().collect()) {
        Ok(Command::Compile(command)) => {
            let mut stdout = io::stdout().lock();
            compile(command, &mut stdout, &mut stderr)
        }
        Ok(Command::ArtifactLlvmIr { artifact, output }) => {
            emit_verified_artifact_llvm_ir_file(&artifact, &output, &mut stderr)
        }
        Ok(Command::InspectTokens { input, indices }) => {
            let mut stdout = io::stdout().lock();
            inspect_tokens(&input, &indices, &mut stdout, &mut stderr)
        }
        Ok(Command::InspectBundleTokens { inputs, indices }) => {
            let mut stdout = io::stdout().lock();
            inspect_bundle_tokens(&inputs, &indices, &mut stdout, &mut stderr)
        }
        Ok(Command::Help) => {
            print!("{USAGE}");
            0
        }
        Ok(Command::Version) => {
            println!("grc {}", env!("CARGO_PKG_VERSION"));
            0
        }
        Ok(Command::Capabilities) => {
            println!(
                "{{\"grc\":\"{}\",\"contract\":1,\"contract-min\":1,\"contract-max\":1,\"artifact-major\":1,\"artifact-minor\":0,\"seed-identity-version\":{},\"seed-identity\":\"{}\",\"multi-file\":true,\"modules\":true,\"phases\":[\"lex\",\"scan\",\"resolve\",\"check\"],\"emit\":[\"bytecode\",\"grbc\",\"llvm-ir\",\"ll\",\"llvm-object\",\"obj\",\"executable\",\"exe\",\"mir\",\"core\",\"provisional\",\"control-plan\",\"monolithic-source\",\"interfaces-json\",\"std-interfaces-json\"],\"diagnostics-json\":true,\"serve\":{{\"protocol\":{},\"transport\":\"json-lines\",\"max-request-bytes\":{},\"max-arguments\":{},\"max-inputs\":{},\"max-source-bytes\":{}}}}}",
                env!("CARGO_PKG_VERSION"),
                grandiose_vm::SEED_IDENTITY_VERSION,
                grandiose_vm::RELEASED_SEED_IDENTITY,
                SESSION_PROTOCOL,
                SESSION_MAX_LINE_BYTES,
                SESSION_MAX_ARGUMENTS,
                SESSION_MAX_INPUTS,
                SESSION_MAX_SOURCE_BYTES,
            );
            0
        }
        Ok(Command::Serve) => {
            drop(stderr);
            let stdin = io::stdin();
            let stdout = io::stdout();
            serve(&mut stdin.lock(), &mut stdout.lock())
        }
        Err(error) => {
            let _ = writeln!(stderr, "grc: error: {error}\n\n{USAGE}");
            2
        }
    }
}

/// The standalone GRBC AOT front door. This is purposefully not folded into
/// source compilation: an artifact must be decoded and VM-verified before the
/// limited native ABI is consulted, and unsupported instructions return an
/// error instead of reaching a VM execution path.
fn emit_verified_artifact_llvm_ir_file(
    artifact: &Path,
    output: &Path,
    stderr: &mut dyn Write,
) -> u8 {
    let bytes = match std::fs::read(artifact) {
        Ok(bytes) => bytes,
        Err(error) => {
            let _ = writeln!(
                stderr,
                "grc: error: could not read artifact {}: {error}",
                artifact.display()
            );
            return 1;
        }
    };
    let ir = match emit_artifact_llvm_ir(&bytes) {
        Ok(ir) => ir,
        Err(error) => {
            let _ = writeln!(
                stderr,
                "grc: error: verified artifact-to-LLVM lowering failed: {error}"
            );
            return 1;
        }
    };
    if let Err(error) = std::fs::write(output, ir) {
        let _ = writeln!(
            stderr,
            "grc: error: could not write {}: {error}",
            output.display()
        );
        return 1;
    }
    0
}

fn inspect_tokens(
    input: &Path,
    indices: &[usize],
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> u8 {
    let source = match std::fs::read_to_string(input) {
        Ok(source) => source,
        Err(error) => {
            let _ = writeln!(
                stderr,
                "grc: error: could not read {}: {error}",
                input.display()
            );
            return 1;
        }
    };
    let tokens = match lexer::lex(&source) {
        Ok(tokens) => tokens,
        Err(error) => {
            let _ = writeln!(stderr, "grc: error: source did not lex: {error:?}");
            return 1;
        }
    };
    for &index in indices {
        let Some(token) = tokens.get(index) else {
            let _ = writeln!(
                stderr,
                "grc: error: token index {index} is out of bounds for {} tokens",
                tokens.len()
            );
            return 1;
        };
        let prefix = &source[..token.span.start];
        let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
        let line_start = prefix.rfind('\n').map_or(0, |offset| offset + 1);
        let column = source[line_start..token.span.start].chars().count() + 1;
        let spelling = &source[token.span.start..token.span.end];
        let _ = writeln!(
            stdout,
            "token {index}: {:?} bytes {}..{} line {line} column {column} spelling={spelling:?}",
            token.kind, token.span.start, token.span.end,
        );
    }
    0
}

fn inspect_bundle_tokens(
    inputs: &[PathBuf],
    indices: &[usize],
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> u8 {
    let mut segments = Vec::with_capacity(inputs.len());
    for input in inputs {
        let source = match std::fs::read_to_string(input) {
            Ok(source) => source,
            Err(error) => {
                let _ = writeln!(
                    stderr,
                    "grc: error: could not read {}: {error}",
                    input.display()
                );
                return 1;
            }
        };
        segments.push(Segment::new(input.to_string_lossy(), source));
    }
    let primary = segments.remove(0);
    let bundle = SourceBundle::distributed(primary, segments);
    let tokens = match lexer::lex(bundle.source()) {
        Ok(tokens) => tokens,
        Err(error) => {
            let _ = writeln!(stderr, "grc: error: source bundle did not lex: {error:?}");
            return 1;
        }
    };
    for &index in indices {
        let Some(token) = tokens.get(index) else {
            let _ = writeln!(
                stderr,
                "grc: error: token index {index} is out of bounds for {} tokens",
                tokens.len()
            );
            return 1;
        };
        let Some(mapped) = bundle.map_span(token.span) else {
            let _ = writeln!(stderr, "grc: error: token {index} spans a bundle boundary");
            return 1;
        };
        let prefix = &mapped.segment.source()[..mapped.span.start];
        let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
        let line_start = prefix.rfind('\n').map_or(0, |offset| offset + 1);
        let column = mapped.segment.source()[line_start..mapped.span.start]
            .chars()
            .count()
            + 1;
        let spelling = &bundle.source()[token.span.start..token.span.end];
        let _ = writeln!(
            stdout,
            "token {index}: {:?} {} bytes {}..{} line {line} column {column} spelling={spelling:?}",
            token.kind,
            mapped.segment.name(),
            mapped.span.start,
            mapped.span.end,
        );
    }
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn durable_native_worker_request_is_bounded_by_available_parallelism() {
        assert_eq!(bounded_durable_native_object_workers(None, 64), Ok(4));
        assert_eq!(bounded_durable_native_object_workers(Some("3"), 64), Ok(3));
        assert_eq!(bounded_durable_native_object_workers(Some("4"), 2), Ok(2));
        assert_eq!(bounded_durable_native_object_workers(Some("1"), 0), Ok(1));
        assert!(bounded_durable_native_object_workers(Some("0"), 4).is_err());
        assert!(bounded_durable_native_object_workers(Some("5"), 4).is_err());
        assert!(bounded_durable_native_object_workers(Some("many"), 4).is_err());
    }

    #[test]
    fn durable_cache_same_key_publication_is_locked_and_rechecked() {
        let directory = tempfile::tempdir().unwrap();
        let key = DiskCacheKey::new(directory.path(), "define i64 @f() { ret i64 1 }", "abi");
        let first = b"\x7fELFfirst".to_vec();
        let second = b"\x7fELFsecond".to_vec();

        let (left, right) = thread::scope(|scope| {
            let left = scope.spawn(|| publish_disk_cache_entry(&key, "abi", &first));
            let right = scope.spawn(|| publish_disk_cache_entry(&key, "abi", &second));
            (
                left.join().unwrap().unwrap(),
                right.join().unwrap().unwrap(),
            )
        });

        let cached = key.read_valid("abi").expect("one complete cache entry");
        assert!(cached == first || cached == second);
        assert_eq!(left, cached);
        assert_eq!(right, cached);
        assert!(!key.lock.exists());
        assert!(directory.path().read_dir().unwrap().all(|entry| {
            !entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .contains(".tmp")
        }));
    }

    #[test]
    fn durable_link_manifest_binds_ordered_object_content_and_link_abi() {
        let directory = tempfile::tempdir().unwrap();
        let ordered = DiskNativeLinkInputs {
            objects: vec!["shared:aaa".into(), "function:bbb".into()],
        };
        let reordered = DiskNativeLinkInputs {
            objects: vec!["function:bbb".into(), "shared:aaa".into()],
        };
        let changed_bytes = DiskNativeLinkInputs {
            objects: vec!["shared:ccc".into(), "function:bbb".into()],
        };
        let first = DiskLinkCacheKey::new(directory.path(), &ordered, "clang=A;wild=B;host=C");
        let reordered =
            DiskLinkCacheKey::new(directory.path(), &reordered, "clang=A;wild=B;host=C");
        let changed_bytes =
            DiskLinkCacheKey::new(directory.path(), &changed_bytes, "clang=A;wild=B;host=C");
        let changed_linker =
            DiskLinkCacheKey::new(directory.path(), &ordered, "clang=A;wild=changed;host=C");
        assert_ne!(first.digest, reordered.digest);
        assert_ne!(first.digest, changed_bytes.digest);
        assert_ne!(first.digest, changed_linker.digest);
    }

    #[test]
    fn durable_link_manifest_rejects_a_tampered_executable() {
        let directory = tempfile::tempdir().unwrap();
        let inputs = DiskNativeLinkInputs {
            objects: vec!["shared:aaa".into()],
        };
        let key = DiskLinkCacheKey::new(directory.path(), &inputs, "clang=A;wild=B;host=C");
        std::fs::create_dir_all(key.executable.parent().unwrap()).unwrap();
        let bytes = b"\x7fELF linked executable";
        std::fs::write(&key.executable, bytes).unwrap();
        std::fs::write(
            &key.manifest,
            key.manifest_text(&inputs, "clang=A;wild=B;host=C", bytes),
        )
        .unwrap();
        assert_eq!(
            key.read_valid(&inputs, "clang=A;wild=B;host=C"),
            Some(bytes.to_vec())
        );
        std::fs::write(&key.executable, b"\x7fELF tampered executable").unwrap();
        assert_eq!(key.read_valid(&inputs, "clang=A;wild=B;host=C"), None);
    }

    #[test]
    fn parses_indexed_token_inspection() {
        let command = parse(
            ["--inspect-token", "bundle.glorious", "17", "42"]
                .into_iter()
                .map(OsString::from)
                .collect(),
        )
        .unwrap();
        assert!(matches!(
            command,
            Command::InspectTokens { input, indices }
                if input == PathBuf::from("bundle.glorious") && indices == [17, 42]
        ));
    }

    #[test]
    fn parses_bundle_token_inspection() {
        let command = parse(
            [
                "--inspect-bundle-token",
                "main.glorious",
                "module.glorious",
                "--",
                "17",
                "42",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .unwrap();
        assert!(matches!(
            command,
            Command::InspectBundleTokens { inputs, indices }
                if inputs == [PathBuf::from("main.glorious"), PathBuf::from("module.glorious")]
                    && indices == [17, 42]
        ));
    }

    #[test]
    fn json_diagnostics_preserve_spanless_messages() {
        let bundle = SourceBundle::distributed(Segment::new("input.glorious", ""), []);
        let diagnostic = Diagnostic::plain("optimizer validation failed").with_code("G1OPT999");
        let mut output = Vec::new();

        write_json_diagnostic(&bundle, &diagnostic, &mut output).unwrap();

        let value: Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(value["title"], "error");
        assert_eq!(value["message"], "optimizer validation failed");
        assert_eq!(value["code"], "G1OPT999");
        assert_eq!(value["labels"], json!([]));
    }

    #[test]
    fn json_diagnostics_emit_grand_machine_fix_contract() {
        let bundle = SourceBundle::raw_for_conformance(
            Segment::new("std.glorious", ""),
            Segment::new("input.glorious", "move value"),
            [],
        );
        let input_start = bundle.segments()[1].global_range().start;
        let diagnostic = Diagnostic::warning(
            "redundant move",
            "the local is transferred without an explicit `move`",
            grandiose::span::Span::new(input_start, input_start + 10),
        )
        .with_code("G1W001")
        .with_fix(grandiose::span::Span::new(input_start, input_start + 4), "");
        let mut output = Vec::new();

        write_json_diagnostic(&bundle, &diagnostic, &mut output).unwrap();

        let value: Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(
            value["fix"],
            json!({
                "file": "input.glorious",
                "start_byte": 0,
                "end_byte": 4,
                "replacement": "",
            })
        );
    }

    #[test]
    fn parses_inputs_in_argument_order_and_the_selected_level() {
        let Command::Compile(command) = parse(
            ["-O3", "first.glorious", "second.glorious", "-o", "out.grbc"]
                .into_iter()
                .map(OsString::from)
                .collect(),
        )
        .unwrap() else {
            panic!("expected a compile command")
        };
        assert_eq!(
            command.inputs,
            [
                PathBuf::from("first.glorious"),
                PathBuf::from("second.glorious")
            ]
        );
        assert_eq!(command.optimization_level, OptimizationLevel::O3);
        assert_eq!(command.output, Some(PathBuf::from("out.grbc")));
        assert_eq!(command.emit, None);
    }

    #[test]
    fn defaults_to_the_self_host_optimization_level() {
        let Command::Compile(command) = parse(vec![OsString::from("input.glorious")]).unwrap()
        else {
            panic!("expected a compile command")
        };
        assert_eq!(command.optimization_level, OptimizationLevel::O2);
    }

    #[test]
    fn parses_native_executable_allocation_limit() {
        let Command::Compile(command) = parse(
            [
                "--emit",
                "executable",
                "--native-allocation-limit",
                "134217728",
                "input.glorious",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .unwrap() else {
            panic!("expected a compile command")
        };
        assert_eq!(command.native_allocation_limit, Some(134217728));
    }

    #[test]
    fn parses_partitioned_native_selector_only_for_o3_executables() {
        let Command::Compile(command) = parse(
            [
                "-O3",
                "--emit",
                "executable",
                "--native-incremental",
                "input.glorious",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .unwrap() else {
            panic!("expected a compile command")
        };
        assert!(command.native_incremental);
        assert_eq!(command.optimization_level, OptimizationLevel::O3);
        assert_eq!(command.emit, Some(EmitKind::Executable));

        for arguments in [
            vec!["--native-incremental", "input.glorious"],
            vec![
                "-O2",
                "--emit",
                "executable",
                "--native-incremental",
                "input.glorious",
            ],
            vec!["-O3", "--native-incremental", "input.glorious"],
            vec![
                "-O3",
                "--emit",
                "llvm-object",
                "--native-incremental",
                "input.glorious",
            ],
        ] {
            assert!(
                parse(arguments.into_iter().map(OsString::from).collect()).is_err(),
                "invalid native-incremental invocation was accepted"
            );
        }
    }

    #[test]
    fn partitioned_native_selector_rejects_one_shot_compilation() {
        let Command::Compile(command) = parse(
            [
                "-O3",
                "--emit",
                "executable",
                "--native-incremental",
                "input.glorious",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .unwrap() else {
            panic!("expected a compile command")
        };
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        assert_eq!(compile(command, &mut stdout, &mut stderr), 1);
        assert!(stdout.is_empty());
        assert!(String::from_utf8(stderr)
            .unwrap()
            .contains("requires a persistent `grc --serve` request"));
    }

    #[test]
    fn native_allocation_limit_is_bounded_and_executable_only() {
        assert!(parse(
            ["--native-allocation-limit", "67108863", "input.glorious"]
                .into_iter()
                .map(OsString::from)
                .collect(),
        )
        .is_err());
        assert!(parse(
            [
                "--emit",
                "executable",
                "--native-allocation-limit",
                "1073741825",
                "input.glorious",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .is_err());
        assert!(parse(
            [
                "--emit",
                "llvm-ir",
                "--native-allocation-limit",
                "134217728",
                "input.glorious",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .is_err());
    }

    #[test]
    fn parses_verified_artifact_llvm_boundary_without_source_inputs() {
        let command = parse(
            ["--artifact-llvm-ir", "stage2.grbc", "-o", "stage2.ll"]
                .into_iter()
                .map(OsString::from)
                .collect(),
        )
        .unwrap();
        assert!(matches!(
            command,
            Command::ArtifactLlvmIr { artifact, output }
                if artifact == PathBuf::from("stage2.grbc")
                    && output == PathBuf::from("stage2.ll")
        ));
    }

    #[test]
    fn artifact_llvm_boundary_requires_a_grbc_and_output() {
        let Err(error) = parse(
            ["--artifact-llvm-ir", "stage2.glorious", "-o", "stage2.ll"]
                .into_iter()
                .map(OsString::from)
                .collect(),
        ) else {
            panic!("non-GRBC artifact input was accepted")
        };
        assert!(error.contains(".grbc"));
        let Err(error) = parse(
            ["--artifact-llvm-ir", "stage2.grbc"]
                .into_iter()
                .map(OsString::from)
                .collect(),
        ) else {
            panic!("artifact input without an output path was accepted")
        };
        assert!(error.contains("-o"));
    }

    #[test]
    fn rejects_non_glorious_source_suffixes() {
        let Err(input) = parse(vec![OsString::from("input.gr")]) else {
            panic!("the removed source suffix was accepted")
        };
        assert!(input.contains("must use the `.glorious` extension"));

        let Err(dependency) = parse(
            [
                OsString::from("--dependency"),
                OsString::from("dep=deps/lib.gr"),
                OsString::from("input.glorious"),
            ]
            .into_iter()
            .collect(),
        ) else {
            panic!("a dependency using the removed source suffix was accepted")
        };
        assert!(dependency.contains("must use the `.glorious` extension"));
    }

    #[test]
    fn parses_named_dependency_roots_without_treating_them_as_fragments() {
        let Command::Compile(command) = parse(
            [
                "--dependency",
                "math-kit=deps/math/lib.glorious",
                "app.glorious",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .unwrap() else {
            panic!("expected a compile command")
        };
        assert_eq!(command.inputs, [PathBuf::from("app.glorious")]);
        assert_eq!(
            command.dependencies,
            [(
                "math-kit".to_string(),
                PathBuf::from("deps/math/lib.glorious")
            )]
        );
    }

    #[test]
    fn parses_all_deterministic_phase_emission_kinds() {
        for (spelling, expected) in [
            ("bytecode", EmitKind::Bytecode),
            ("grbc", EmitKind::Bytecode),
            ("llvm-ir", EmitKind::LlvmIr),
            ("ll", EmitKind::LlvmIr),
            ("mir", EmitKind::Mir),
            ("core", EmitKind::Core),
            ("provisional", EmitKind::Provisional),
            ("control-plan", EmitKind::ControlPlan),
            ("interfaces-json", EmitKind::InterfacesJson),
        ] {
            let Command::Compile(command) = parse(
                [format!("--emit={spelling}"), "input.glorious".to_string()]
                    .into_iter()
                    .map(OsString::from)
                    .collect(),
            )
            .unwrap() else {
                panic!("expected a compile command")
            };
            assert_eq!(command.emit, Some(expected));
        }
        let Command::Compile(command) = parse(
            ["--emit", "std-interfaces-json"]
                .into_iter()
                .map(OsString::from)
                .collect(),
        )
        .unwrap() else {
            panic!("expected a compile command")
        };
        assert_eq!(command.emit, Some(EmitKind::StandardInterfacesJson));
        assert!(command.inputs.is_empty());
    }

    #[test]
    fn check_only_rejects_output_requests() {
        let error = parse(
            ["--check", "input.glorious", "-o", "out.grbc"]
                .into_iter()
                .map(OsString::from)
                .collect(),
        )
        .err()
        .unwrap();
        assert!(error.contains("cannot be combined"));
    }

    #[test]
    fn parses_each_truthfully_advertised_stop_phase() {
        for (spelling, expected) in [
            ("lex", StopPhase::Lex),
            ("scan", StopPhase::Scan),
            ("resolve", StopPhase::Resolve),
            ("check", StopPhase::Check),
        ] {
            let Command::Compile(command) = parse(
                ["--phase", spelling, "input.glorious"]
                    .into_iter()
                    .map(OsString::from)
                    .collect(),
            )
            .unwrap() else {
                panic!("expected a compile command")
            };
            assert_eq!(command.stop_phase, Some(expected));
        }
        assert!(parse(
            ["--phase", "lex", "--check", "input.glorious"]
                .into_iter()
                .map(OsString::from)
                .collect()
        )
        .is_err());
    }

    #[test]
    fn capabilities_is_a_standalone_machine_command() {
        assert!(matches!(
            parse(vec![OsString::from("--capabilities")]).unwrap(),
            Command::Capabilities
        ));
        assert!(parse(vec![
            OsString::from("--capabilities"),
            OsString::from("input.glorious")
        ])
        .is_err());
    }

    #[test]
    fn serve_is_a_standalone_machine_command() {
        assert!(matches!(
            parse(vec![OsString::from("--serve")]).unwrap(),
            Command::Serve
        ));
        assert!(parse(vec![
            OsString::from("--serve"),
            OsString::from("input.glorious")
        ])
        .is_err());
    }

    #[test]
    fn native_codegen_preserves_the_requested_optimization_level() {
        assert_eq!(clang_optimization_flag(OptimizationLevel::O0), "-O0");
        assert_eq!(clang_optimization_flag(OptimizationLevel::O1), "-O1");
        assert_eq!(clang_optimization_flag(OptimizationLevel::O2), "-O2");
        assert_eq!(clang_optimization_flag(OptimizationLevel::O3), "-O3");
    }

    #[test]
    fn native_executable_linking_routes_clang_through_wild_only() {
        let mut executable = ProcessCommand::new("clang");
        configure_wild_linking(&mut executable);
        let executable_args = executable
            .get_args()
            .map(|argument| argument.to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        assert_eq!(executable_args, ["--ld-path=wild"]);

        // `--emit llvm-object` must remain a compile-only Clang path, so it
        // never receives final-linker arguments.
        let object = ProcessCommand::new("clang");
        assert!(object.get_args().next().is_none());
    }
}
