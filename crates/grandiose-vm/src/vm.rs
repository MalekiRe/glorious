use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt, fs,
    rc::Rc,
    time::Instant,
};

use crate::{
    bytecode::{
        Artifact, BYTES, Constant, F32, F64, HandlerClause, I8, I16, I32, I64, I128, ISIZE, Import,
        Instruction, Primitive, TEXT, Type, TypeId, U8, U16, U32, U64, U128, UNIT, USIZE,
    },
    value::{
        AggregateValue, ArenaObject, ArrayValue, CallableValue, ControlHandle, HandlerValue,
        ReclamationScope, ReferenceTarget, ResumptionValue, RuntimeFrame, RuntimeLabel, SlotStore,
        Value, reclamation_diagnostic_counts,
    },
    verify::{ExecutionImage, ImageConstant, VerifiedArtifact, VerifyError, verify},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostFault {
    pub message: String,
}

impl HostFault {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for HostFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl Error for HostFault {}

/// Typed, ownership-transferring generation-1 host surface.
pub trait Host {
    fn process_args(&self) -> Result<Vec<String>, HostFault>;
    fn fs_read(&self, path: String) -> Result<Vec<u8>, HostFault>;
    fn fs_write(&self, path: String, contents: Vec<u8>) -> Result<(), HostFault>;
    fn diagnostic_write(&self, message: String) -> Result<(), HostFault>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostLinkError {
    DeniedCapability(String),
    UnknownImport { capability: String, symbol: String },
    SignatureMismatch { capability: String, symbol: String },
    MissingMayTrap { capability: String, symbol: String },
}

impl fmt::Display for HostLinkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DeniedCapability(capability) => {
                write!(f, "host capability `{capability}` was not granted")
            }
            Self::UnknownImport { capability, symbol } => {
                write!(f, "unknown host import `{capability}`/`{symbol}`")
            }
            Self::SignatureMismatch { capability, symbol } => {
                write!(
                    f,
                    "wrong signature for host import `{capability}`/`{symbol}`"
                )
            }
            Self::MissingMayTrap { capability, symbol } => write!(
                f,
                "host import `{capability}`/`{symbol}` must declare MAY_TRAP"
            ),
        }
    }
}

impl Error for HostLinkError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeError {
    Verification(VerifyError),
    InvalidFunction(u32),
    WrongArgumentCount { expected: usize, actual: usize },
    WrongArgumentType { argument: usize, expected: TypeId },
    EmptyRegister(u32),
    TypeConfusion,
    ArithmeticOverflow,
    DivisionByZero,
    InvalidShiftCount,
    InvalidCharacter,
    InvalidUtf8,
    IndexOutOfBounds,
    EmptyArraySlot,
    ArraySlotAlreadyInitialized,
    ArrayNotDrained,
    AllocationOverflow,
    AllocationLimit,
    ReachedUnreachable,
    UnhandledEffect { protocol: u32, operation: u32 },
    HostLink(HostLinkError),
    HostFault(HostFault),
    Aborted(Option<String>),
}

/// Normative generation-1 runtime outcome category. Detailed [`RuntimeError`]
/// variants remain available for diagnostics without changing the portable
/// category observed by hosts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeFaultCategory {
    Verification,
    UnhandledEffect,
    PrimitiveTrap,
    HostFault,
    ExplicitAbort,
    MemoryLimit,
    Internal,
}

impl RuntimeError {
    pub const fn category(&self) -> RuntimeFaultCategory {
        match self {
            Self::Verification(_) => RuntimeFaultCategory::Verification,
            Self::UnhandledEffect { .. } => RuntimeFaultCategory::UnhandledEffect,
            Self::ArithmeticOverflow
            | Self::DivisionByZero
            | Self::InvalidShiftCount
            | Self::InvalidCharacter
            | Self::InvalidUtf8
            | Self::IndexOutOfBounds
            | Self::EmptyArraySlot
            | Self::ArraySlotAlreadyInitialized
            | Self::ArrayNotDrained
            | Self::AllocationOverflow => RuntimeFaultCategory::PrimitiveTrap,
            Self::AllocationLimit => RuntimeFaultCategory::MemoryLimit,
            Self::HostFault(_) | Self::HostLink(_) => RuntimeFaultCategory::HostFault,
            Self::Aborted(_) => RuntimeFaultCategory::ExplicitAbort,
            Self::InvalidFunction(_)
            | Self::WrongArgumentCount { .. }
            | Self::WrongArgumentType { .. }
            | Self::EmptyRegister(_)
            | Self::TypeConfusion
            | Self::ReachedUnreachable => RuntimeFaultCategory::Internal,
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Verification(e) => write!(f, "bytecode verification failed: {e}"),
            Self::InvalidFunction(x) => write!(f, "invalid entry function {x}"),
            Self::WrongArgumentCount { expected, actual } => {
                write!(f, "expected {expected} arguments, got {actual}")
            }
            Self::WrongArgumentType { argument, expected } => write!(
                f,
                "argument {argument} does not have bytecode type {expected}"
            ),
            Self::EmptyRegister(r) => write!(f, "attempted to read empty register r{r}"),
            Self::TypeConfusion => {
                write!(f, "verified program encountered a runtime type mismatch")
            }
            Self::ArithmeticOverflow => write!(f, "checked arithmetic overflow"),
            Self::DivisionByZero => write!(f, "division by zero"),
            Self::InvalidShiftCount => write!(f, "invalid integer shift count"),
            Self::InvalidCharacter => write!(f, "invalid Unicode scalar value"),
            Self::InvalidUtf8 => write!(f, "invalid UTF-8"),
            Self::IndexOutOfBounds => write!(f, "index or slice is out of bounds"),
            Self::EmptyArraySlot => write!(f, "array slot is empty"),
            Self::ArraySlotAlreadyInitialized => write!(f, "array slot is already initialized"),
            Self::ArrayNotDrained => write!(f, "array still contains initialized slots"),
            Self::AllocationOverflow => write!(f, "array capacity overflow"),
            Self::AllocationLimit => write!(f, "runtime allocation limit exceeded"),
            Self::ReachedUnreachable => write!(f, "execution reached an unreachable instruction"),
            Self::UnhandledEffect {
                protocol,
                operation,
            } => write!(f, "unhandled effect {protocol}/{operation}"),
            Self::HostLink(error) => write!(f, "host import linking failed: {error}"),
            Self::HostFault(error) => write!(f, "host fault: {error}"),
            Self::Aborted(Some(message)) => write!(f, "aborted: {message}"),
            Self::Aborted(None) => write!(f, "aborted"),
        }
    }
}
impl Error for RuntimeError {}
impl From<VerifyError> for RuntimeError {
    fn from(x: VerifyError) -> Self {
        Self::Verification(x)
    }
}

pub struct Vm {
    artifact: VerifiedArtifact,
    host: Option<Box<dyn Host>>,
    imports: Result<Vec<ResolvedImport>, HostLinkError>,
    slots: SlotStore,
    last_location: Cell<Option<(u32, u32)>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ResolvedImport {
    ProcessArgs,
    FsRead,
    FsWrite,
    DiagnosticWrite,
}

type Frame = RuntimeFrame;

#[derive(Clone, Copy)]
enum CapturePruning {
    Multishot,
    Cancellation,
}

const DEFAULT_MEMORY_PROFILE_STEPS: u64 = 1_000_000;

struct VmProgressTrace {
    interval: u64,
    countdown: u64,
    steps: u64,
    started: Instant,
}

/// Low-overhead sampled attribution for long-running bytecode workloads.
///
/// Sampling avoids materially perturbing the interpreter while still making
/// billion-instruction compiler runs attributable to concrete bytecode
/// functions. Reports use stable function indices because verified execution
/// deliberately discards descriptor names after loading.
struct VmHotFunctions {
    sample_interval: u64,
    sample_countdown: u64,
    report_interval: u64,
    report_countdown: u64,
    steps: u64,
    samples: Vec<u64>,
}

impl VmHotFunctions {
    fn from_env(function_count: usize) -> Option<Self> {
        let function_count = function_count;
        let sample_interval = std::env::var("G1_VM_HOT_FUNCTION_SAMPLE_STEPS")
            .ok()?
            .parse::<u64>()
            .ok()
            .filter(|steps| *steps > 0)?;
        let report_interval = std::env::var("G1_VM_HOT_FUNCTION_REPORT_STEPS")
            .ok()
            .and_then(|value| value.parse::<u64>().ok())
            .filter(|steps| *steps > 0)
            .unwrap_or(100_000_000);
        Some(Self {
            sample_interval,
            sample_countdown: 0,
            report_interval,
            report_countdown: report_interval,
            steps: 0,
            samples: vec![0; function_count],
        })
    }

    fn observe(&mut self, function: u32, a: &ExecutionImage) {
        self.steps = self.steps.saturating_add(1);
        if self.sample_countdown == 0 {
            self.sample_countdown = self.sample_interval.saturating_sub(1);
            if let Some(count) = self.samples.get_mut(function as usize) {
                *count = count.saturating_add(1);
            }
        } else {
            self.sample_countdown -= 1;
        }
        if self.report_countdown > 1 {
            self.report_countdown -= 1;
            return;
        }
        self.report_countdown = self.report_interval;
        let mut ranked = self
            .samples
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, count)| *count != 0)
            .collect::<Vec<_>>();
        ranked.sort_unstable_by_key(|(function, count)| (std::cmp::Reverse(*count), *function));
        let total = ranked.iter().map(|(_, count)| *count).sum::<u64>().max(1);
        let hot = ranked
            .into_iter()
            .take(16)
            .map(|(function, count)| {
                let name = a
                    .functions
                    .get(function)
                    .map(|function| function.name.as_str())
                    .unwrap_or("<unknown>");
                format!(
                    "f{function}={name}={:.2}%",
                    count as f64 * 100.0 / total as f64
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        eprintln!("g1-vm-hot-functions steps={} samples={} hot=[{}]", self.steps, total, hot);
    }
}

impl VmProgressTrace {
    fn from_env() -> Option<Self> {
        let interval = std::env::var("G1_VM_PROGRESS_STEPS")
            .ok()?
            .parse::<u64>()
            .ok()
            .filter(|steps| *steps > 0)?;
        Some(Self {
            interval,
            countdown: 0,
            steps: 0,
            started: Instant::now(),
        })
    }

    fn observe(&mut self, function: u32, name: &str, pc: u32, depth: usize) {
        self.steps = self.steps.saturating_add(1);
        if self.countdown > 0 {
            self.countdown -= 1;
            return;
        }
        self.countdown = self.interval.saturating_sub(1);
        let elapsed = self.started.elapsed().as_secs_f64();
        let rate = if elapsed == 0.0 {
            0.0
        } else {
            self.steps as f64 / elapsed
        };
        eprintln!(
            "g1-vm-progress steps={} elapsed={elapsed:.3}s rate={rate:.0}/s function={function} name={name:?} pc={pc} depth={depth}",
            self.steps
        );
    }
}

struct VmMemoryProfile {
    sample_countdown: u64,
    sample_steps: u64,
    steps: u64,
    report_increment_kib: u64,
    next_report_rss_kib: Option<u64>,
}

/// Opt-in per-instruction-class execution counter used to profile hot VM
/// dispatch paths (`G1_VM_INSTR_PROFILE=1`). Disabled runs take one
/// never-taken branch per instruction and no allocations.
struct InstructionProfile {
    counts: Vec<u64>,
    steps: u64,
}

impl InstructionProfile {
    fn from_env() -> Option<Self> {
        std::env::var_os("G1_VM_INSTR_PROFILE")
            .is_some()
            .then(|| Self {
                counts: vec![0; 49],
                steps: 0,
            })
    }

    fn observe(&mut self, instruction: &Instruction) {
        self.steps = self.steps.saturating_add(1);
        self.counts[instruction_class(instruction)] += 1;
    }

    fn report(&self) {
        let total = self.counts.iter().sum::<u64>().max(1);
        let mut ranked = self
            .counts
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, count)| *count != 0)
            .collect::<Vec<_>>();
        ranked.sort_unstable_by_key(|(class, count)| (std::cmp::Reverse(*count), *class));
        eprintln!(
            "g1-vm-instructions total_reflected={} sum={} hot=[{}]",
            self.steps,
            total,
            ranked
                .into_iter()
                .take(20)
                .map(|(class, count)| format!(
                    "{}={:.2}%({})",
                    INSTRUCTION_CLASS_NAMES[class],
                    count as f64 * 100.0 / total as f64,
                    count
                ))
                .collect::<Vec<_>>()
                .join(",")
        );
    }
}

const INSTRUCTION_CLASS_NAMES: [&str; 49] = [
    "Nop", "Const", "Move", "Copy", "BorrowShared", "BorrowUnique",
    "ReborrowShared", "ReborrowUnique", "DerefCopy", "DerefReborrowShared",
    "DerefReborrowUnique", "DerefMove", "DerefStore", "EndBorrow", "Construct",
    "ProjectMove", "ProjectCopy", "ProjectBorrowShared", "ProjectBorrowUnique",
    "EnumTag", "Drop", "Deconstruct", "Primitive", "Jump", "Switch", "Call",
    "TailCall", "CallSelf", "TailCallSelf", "CallKnownReceiver",
    "TailCallKnownReceiver", "MakeCallable", "MakeHandler", "MakeHandlerShared",
    "MakeBindingPack", "CallIndirect", "TailCallIndirect", "Handle", "Perform",
    "Resume", "TailResume", "Cancel", "HostCall", "Abort", "LabelPush",
    "LabelPop", "Leave", "Return", "Unreachable",
];

fn instruction_class(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::Nop => 0,
        Instruction::Const { .. } => 1,
        Instruction::Move { .. } => 2,
        Instruction::Copy { .. } => 3,
        Instruction::BorrowShared { .. } => 4,
        Instruction::BorrowUnique { .. } => 5,
        Instruction::ReborrowShared { .. } => 6,
        Instruction::ReborrowUnique { .. } => 7,
        Instruction::DerefCopy { .. } => 8,
        Instruction::DerefReborrowShared { .. } => 9,
        Instruction::DerefReborrowUnique { .. } => 10,
        Instruction::DerefMove { .. } => 11,
        Instruction::DerefStore { .. } => 12,
        Instruction::EndBorrow { .. } => 13,
        Instruction::Construct { .. } => 14,
        Instruction::ProjectMove { .. } => 15,
        Instruction::ProjectCopy { .. } => 16,
        Instruction::ProjectBorrowShared { .. } => 17,
        Instruction::ProjectBorrowUnique { .. } => 18,
        Instruction::EnumTag { .. } => 19,
        Instruction::Drop { .. } => 20,
        Instruction::Deconstruct { .. } => 21,
        Instruction::Primitive { .. } => 22,
        Instruction::Jump { .. } => 23,
        Instruction::Switch { .. } => 24,
        Instruction::Call { .. } => 25,
        Instruction::TailCall { .. } => 26,
        Instruction::CallSelf { .. } => 27,
        Instruction::TailCallSelf { .. } => 28,
        Instruction::CallKnownReceiver { .. } => 29,
        Instruction::TailCallKnownReceiver { .. } => 30,
        Instruction::MakeCallable { .. } => 31,
        Instruction::MakeHandler { .. } => 32,
        Instruction::MakeHandlerShared { .. } => 33,
        Instruction::MakeBindingPack { .. } => 34,
        Instruction::CallIndirect { .. } => 35,
        Instruction::TailCallIndirect { .. } => 36,
        Instruction::Handle { .. } => 37,
        Instruction::Perform { .. } => 38,
        Instruction::Resume { .. } => 39,
        Instruction::TailResume { .. } => 40,
        Instruction::Cancel { .. } => 41,
        Instruction::HostCall { .. } => 42,
        Instruction::Abort { .. } => 43,
        Instruction::LabelPush { .. } => 44,
        Instruction::LabelPop { .. } => 45,
        Instruction::Leave { .. } => 46,
        Instruction::Return { .. } => 47,
        Instruction::Unreachable => 48,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ProcessMemory {
    virtual_kib: u64,
    rss_kib: u64,
}

#[derive(Default)]
struct FrameCounts {
    active: usize,
    deferred: usize,
    live_registers: usize,
    register_slots: usize,
    guards: usize,
    labels: usize,
}

/// Opt-in, allocation-light VM breakpoint used to diagnose generated compiler
/// artifacts. `G1_VM_BREAKPOINT=FUNCTION:PC` selects a location and
/// `G1_VM_BREAK_U64=REGISTER:VALUE` can restrict it to one scalar argument.
struct VmBreakpoint {
    function: u32,
    pc: u32,
    u64_filter: Option<(usize, u64)>,
}

impl VmBreakpoint {
    fn from_env() -> Option<Self> {
        let (function, pc) = parse_u32_pair(&std::env::var("G1_VM_BREAKPOINT").ok()?)?;
        let u64_filter = std::env::var("G1_VM_BREAK_U64")
            .ok()
            .and_then(|value| parse_usize_u64_pair(&value));
        Some(Self {
            function,
            pc,
            u64_filter,
        })
    }

    fn matches(&self, frame: &Frame) -> bool {
        self.function == frame.function
            && self.pc == frame.pc
            && self.u64_filter.is_none_or(|(register, expected)| {
                matches!(
                    frame.registers.get(register).and_then(Option::as_ref),
                    Some(Value::U64(actual)) if *actual == expected
                )
            })
    }

    fn report(&self, stack: &[Frame], image: &ExecutionImage) {
        eprintln!(
            "g1-vm-breakpoint function={} pc={} depth={}",
            self.function,
            self.pc,
            stack.len()
        );
        for (depth, frame) in stack.iter().enumerate() {
            let name = image
                .functions
                .get(frame.function as usize)
                .map_or("<invalid>", |function| function.name.as_str());
            eprintln!(
                "  frame depth={depth} function={} name={name:?} pc={}",
                frame.function, frame.pc
            );
        }
        if let Some(frame) = stack.last() {
            for (register, value) in frame.registers.iter().enumerate() {
                match value.as_ref() {
                    Some(Value::I64(value)) => {
                        eprintln!("  register r{register}=i64:{value}")
                    }
                    Some(Value::I128(value)) => {
                        eprintln!("  register r{register}=i128:{value}")
                    }
                    Some(Value::U64(value)) => {
                        eprintln!("  register r{register}=u64:{value}")
                    }
                    Some(Value::U128(value)) => {
                        eprintln!("  register r{register}=u128:{value}")
                    }
                    Some(Value::F32(value)) => {
                        eprintln!("  register r{register}=f32:{value}")
                    }
                    Some(Value::F64(value)) => {
                        eprintln!("  register r{register}=f64:{value}")
                    }
                    _ => {}
                }
            }
        }
    }
}

fn parse_u32_pair(value: &str) -> Option<(u32, u32)> {
    let (left, right) = value.split_once(':')?;
    Some((left.parse().ok()?, right.parse().ok()?))
}

fn parse_usize_u64_pair(value: &str) -> Option<(usize, u64)> {
    let (left, right) = value.split_once(':')?;
    Some((left.parse().ok()?, right.parse().ok()?))
}

impl VmMemoryProfile {
    fn from_env() -> Option<Self> {
        let report_increment_mib = std::env::var("G1_VM_MEMORY_PROFILE_MIB")
            .ok()?
            .parse::<u64>()
            .ok()
            .filter(|increment| *increment > 0)?;
        let sample_steps = std::env::var("G1_VM_MEMORY_PROFILE_STEPS")
            .ok()
            .and_then(|value| value.parse::<u64>().ok())
            .filter(|steps| *steps > 0)
            .unwrap_or(DEFAULT_MEMORY_PROFILE_STEPS);
        Some(Self {
            sample_countdown: 0,
            sample_steps,
            steps: 0,
            report_increment_kib: report_increment_mib.saturating_mul(1024),
            next_report_rss_kib: None,
        })
    }

    fn observe(&mut self, stack: &[Frame], slots: &SlotStore, image: &ExecutionImage) {
        self.steps = self.steps.saturating_add(1);
        if self.sample_countdown > 0 {
            self.sample_countdown -= 1;
            return;
        }
        self.sample_countdown = self.sample_steps.saturating_sub(1);
        let Some(memory) = process_memory() else {
            return;
        };
        if self
            .next_report_rss_kib
            .is_some_and(|threshold| memory.rss_kib < threshold)
        {
            return;
        }

        let Some(frame) = stack.last() else {
            return;
        };
        let mut counts = FrameCounts::default();
        let mut suspended_sites = BTreeMap::<(u32, u32), usize>::new();
        for active in stack {
            counts.active += 1;
            count_frame(active, &mut counts);
            *suspended_sites
                .entry((active.function, active.pc))
                .or_default() += 1;
        }
        let mut suspended_sites = suspended_sites.into_iter().collect::<Vec<_>>();
        suspended_sites.sort_by_key(|(site, count)| (std::cmp::Reverse(*count), *site));
        let suspended_sites = suspended_sites
            .into_iter()
            .take(8)
            .map(|((function, return_pc), count)| format!("f{function}:pc{return_pc}={count}"))
            .collect::<Vec<_>>()
            .join(",");
        let (occupied_place_slots, retained_place_slots) = slots.diagnostic_counts();
        let (tracked_reclamation_nodes, live_reclamation_nodes) = reclamation_diagnostic_counts();
        let name = image
            .functions
            .get(frame.function as usize)
            .map_or("<invalid>", |function| function.name.as_str());
        eprintln!(
            "g1-vm-memory steps={} rss_mib={:.1} virtual_mib={:.1} function={} name={:?} pc={} active_frames={} deferred_frames={} live_registers={} register_slots={} guards={} labels={} occupied_place_slots={} retained_place_slots={} tracked_reclamation_nodes={} live_reclamation_nodes={} suspended_sites=[{}]",
            self.steps,
            memory.rss_kib as f64 / 1024.0,
            memory.virtual_kib as f64 / 1024.0,
            frame.function,
            name,
            frame.pc,
            counts.active,
            counts.deferred,
            counts.live_registers,
            counts.register_slots,
            counts.guards,
            counts.labels,
            occupied_place_slots,
            retained_place_slots,
            tracked_reclamation_nodes,
            live_reclamation_nodes,
            suspended_sites,
        );
        self.next_report_rss_kib = Some(memory.rss_kib.saturating_add(self.report_increment_kib));
    }
}

fn count_frame(frame: &Frame, counts: &mut FrameCounts) {
    counts.live_registers += frame
        .registers
        .iter()
        .filter(|value| value.is_some())
        .count();
    counts.register_slots += frame.registers.len();
    counts.guards += frame.guards.len();
    counts.labels += frame.labels.len();
    for deferred in &frame.deferred_frames {
        counts.deferred += 1;
        count_frame(deferred, counts);
    }
}

fn process_memory() -> Option<ProcessMemory> {
    parse_process_status(&fs::read_to_string("/proc/self/status").ok()?)
}

fn parse_process_status(status: &str) -> Option<ProcessMemory> {
    fn kib(status: &str, field: &str) -> Option<u64> {
        let line = status.lines().find(|line| line.starts_with(field))?;
        line.split_ascii_whitespace().nth(1)?.parse().ok()
    }
    Some(ProcessMemory {
        virtual_kib: kib(status, "VmSize:")?,
        rss_kib: kib(status, "VmRSS:")?,
    })
}

impl Vm {
    pub fn new(artifact: VerifiedArtifact) -> Self {
        let imports = if artifact.image().imports.is_empty() {
            Ok(vec![])
        } else {
            let first = artifact
                .image()
                .import_id(0)
                .expect("nonempty import table has a first checked ID");
            Err(HostLinkError::DeniedCapability(
                artifact.image().import_capability(first).to_owned(),
            ))
        };
        Self {
            artifact,
            host: None,
            imports,
            slots: SlotStore::default(),
            last_location: Cell::new(None),
        }
    }
    pub fn from_artifact(artifact: Artifact) -> Result<Self, VerifyError> {
        #[cfg(test)]
        let artifact = if artifact.cleanups.is_empty() && !artifact.functions.is_empty() {
            crate::verify::with_generated_cleanup_plans(artifact)?
        } else {
            artifact
        };
        Ok(Self::new(verify(artifact)?))
    }
    pub fn artifact(&self) -> &Artifact {
        self.artifact.artifact()
    }

    pub fn with_host<H, I, S>(
        artifact: VerifiedArtifact,
        grants: I,
        host: H,
    ) -> Result<Self, HostLinkError>
    where
        H: Host + 'static,
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let grants = grants
            .into_iter()
            .map(|grant| grant.as_ref().to_owned())
            .collect::<BTreeSet<_>>();
        let imports = link_imports(artifact.image(), &grants)?;
        Ok(Self {
            artifact,
            host: Some(Box::new(host)),
            imports: Ok(imports),
            slots: SlotStore::default(),
            last_location: Cell::new(None),
        })
    }

    pub fn run(&self, function: u32, args: Vec<Value>) -> Result<Value, RuntimeError> {
        let scope = ReclamationScope::begin();
        scope.track_values(&args);
        let trace_errors = std::env::var_os("G1_VM_ERROR_TRACE").is_some();
        if trace_errors {
            self.last_location.set(None);
        }
        let result = self.run_inner(function, args);
        if trace_errors
            && let Err(error) = &result
            && let Some((function, pc)) = self.last_location.get()
        {
            let instruction = self.artifact.function(function).and_then(|function| {
                let checked = function.checked_pc(pc)?;
                Some((
                    function.descriptor().name.as_str(),
                    function.instruction(checked),
                ))
            });
            match instruction {
                Some((name, instruction)) => eprintln!(
                    "g1-vm-error error={error:?} function={function} name={name:?} pc={pc} instruction={instruction:?}"
                ),
                None => eprintln!(
                    "g1-vm-error error={error:?} function={function} pc={pc} instruction=<unavailable>"
                ),
            }
        }
        scope.finish();
        result
    }

    fn run_inner(&self, function: u32, args: Vec<Value>) -> Result<Value, RuntimeError> {
        let resolved_imports = self
            .imports
            .as_ref()
            .map_err(|error| RuntimeError::HostLink(error.clone()))?;
        let a = self.artifact.image();
        let mut stack = vec![make_frame(a, function, args, Value::Unit, None)?];
        let mut memory_profile = VmMemoryProfile::from_env();
        let mut progress_trace = VmProgressTrace::from_env();
        let mut hot_functions = VmHotFunctions::from_env(a.functions.len());
        let breakpoint = VmBreakpoint::from_env();
        let traced_function = std::env::var("G1_VM_FUNCTION").ok();
        let trace_errors = std::env::var_os("G1_VM_ERROR_TRACE").is_some();
        let mut instruction_profile = InstructionProfile::from_env();
        let instruction_profile_enabled = instruction_profile.is_some();
        // Cache the current function's descriptor and lazily-decoded
        // instruction slice so per-step dispatch does not re-resolve the
        // function or re-check bounds on every instruction. Refreshed only
        // when a call/return changes the active frame's function.
        let artifact_ref = &self.artifact;
        let mut cached_function: Option<(u32, &crate::bytecode::Function, &[Instruction])> = None;
        if instruction_profile_enabled {
            eprintln!(
                "g1-vm-tables drop_glue={} types={} cleanups={} functions={}",
                a.drop_glue.len(),
                a.types.len(),
                a.cleanups.len(),
                a.functions.len()
            );
        }
        loop {
            if let Some(profile) = &mut memory_profile {
                profile.observe(&stack, &self.slots, a);
            }
            let stack_depth = stack.len();
            if breakpoint.as_ref().is_some_and(|breakpoint| {
                stack
                    .last()
                    .is_some_and(|frame| breakpoint.matches(frame))
            }) {
                breakpoint.as_ref().unwrap().report(&stack, a);
            }
            let frame = stack.last_mut().expect("execution stack cannot be empty");
            if let Some(profile) = &mut hot_functions {
                profile.observe(frame.function, a);
            }
            let (fun, decoded) = match cached_function {
                Some((cached_id, fun, decoded)) if cached_id == frame.function => (fun, decoded),
                _ => {
                    let verified_fun = artifact_ref
                        .function(frame.function)
                        .ok_or(RuntimeError::InvalidFunction(frame.function))?;
                    let fun = verified_fun.descriptor();
                    let decoded = verified_fun.decoded_instructions();
                    cached_function = Some((frame.function, fun, decoded));
                    (fun, decoded)
                }
            };
            if frame.pc >= fun.code_len {
                return Err(RuntimeError::TypeConfusion);
            }
            // SAFETY: `frame.pc < fun.code_len == decoded.len()` was checked
            // above, and `decoded` is this function's immutable, verifier-built
            // instruction slice indexed by its function-local pc.
            let ins =
                unsafe { decoded.get_unchecked(frame.pc as usize) };
            if instruction_profile_enabled {
                instruction_profile.as_mut().unwrap().observe(ins);
            }
            if let Some(trace) = &mut progress_trace {
                trace.observe(frame.function, &fun.name, frame.pc, stack_depth);
            }
            if trace_errors {
                self.last_location.set(Some((frame.function, frame.pc)));
            }
            if traced_function.as_deref() == Some(fun.name.as_str()) {
                eprintln!(
                    "g1-vm function {} `{}` pc {}: {ins:?}",
                    frame.function, fun.name, frame.pc
                );
            }
            match ins {
                Instruction::Nop => frame.pc += 1,
                Instruction::Const { dst, constant } => {
                    let (dst, constant) = (*dst, *constant);
                    let constant = a
                        .checked_constant(constant)
                        .ok_or(RuntimeError::TypeConfusion)?;
                    put(frame, dst, constant_value(constant)?)?;
                    frame.pc += 1;
                }
                Instruction::Move { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    // MOVE relocates storage identity as well as its value.
                    // A register materialized as `Place` may still be the
                    // target of references transported by the same verified
                    // MIR edge bundle. Unwrapping and reclaiming that slot
                    // here would leave those references dangling at runtime.
                    // Destructive consumers continue to use `take`, which
                    // unwraps the place once its borrow lifetime has ended.
                    let v = frame.registers[src as usize]
                        .take()
                        .ok_or(RuntimeError::EmptyRegister(src))?;
                    put(frame, dst, v)?;
                    frame.pc += 1;
                }
                Instruction::Copy { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let v = copy_register(a, frame, src, fun.register_types[src as usize])?;
                    put(frame, dst, v)?;
                    frame.pc += 1;
                }
                Instruction::BorrowShared { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let target = whole_place(&self.slots, frame, src)?;
                    let referent_type = fun.register_types[src as usize];
                    put(
                        frame,
                        dst,
                        Value::Reference {
                            referent_type,
                            unique: false,
                            target,
                        },
                    )?;
                    frame.pc += 1;
                }
                Instruction::BorrowUnique { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let target = whole_place(&self.slots, frame, src)?;
                    let referent_type = fun.register_types[src as usize];
                    put(
                        frame,
                        dst,
                        Value::Reference {
                            referent_type,
                            unique: true,
                            target,
                        },
                    )?;
                    frame.pc += 1;
                }
                Instruction::EndBorrow { reference } => {
                    let reference = *reference;
                    let Value::Reference { .. } = take(frame, reference)? else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    frame.pc += 1;
                }
                Instruction::DerefCopy { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let (referent_type, target) = match get(frame, src)? {
                        Value::Reference {
                            referent_type,
                            target,
                            ..
                        } => (referent_type, target),
                        _ => return Err(RuntimeError::TypeConfusion),
                    };
                    let value = copy_reference_target(a, referent_type, &target)?;
                    put(frame, dst, value)?;
                    frame.pc += 1;
                }
                Instruction::DerefReborrowShared { dst, src }
                | Instruction::DerefReborrowUnique { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let requested_unique = matches!(ins, Instruction::DerefReborrowUnique { .. });
                    let (outer_unique, outer_target) = match get(frame, src)? {
                        Value::Reference { unique, target, .. } => (unique, target),
                        _ => return Err(RuntimeError::TypeConfusion),
                    };
                    let Value::Reference {
                        referent_type,
                        unique: inner_unique,
                        target,
                        ..
                    } = observe_reference_target(&outer_target)?
                    else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    if requested_unique && (!outer_unique || !inner_unique) {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    put(
                        frame,
                        dst,
                        Value::Reference {
                            referent_type,
                            unique: requested_unique,
                            target,
                        },
                    )?;
                    frame.pc += 1;
                }
                Instruction::DerefMove { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let target = match get(frame, src)? {
                        Value::Reference {
                            unique: true,
                            target,
                            ..
                        } => target,
                        _ => return Err(RuntimeError::TypeConfusion),
                    };
                    let value = take_reference_target(&target)?;
                    put(frame, dst, value)?;
                    frame.pc += 1;
                }
                Instruction::DerefStore { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let target = match get(frame, dst)? {
                        Value::Reference {
                            unique: true,
                            target,
                            ..
                        } => target,
                        _ => return Err(RuntimeError::TypeConfusion),
                    };
                    let value = take(frame, src)?;
                    store_reference_target(&target, value)?;
                    frame.pc += 1;
                }
                Instruction::Construct {
                    dst,
                    ty,
                    variant,
                    fields,
                } => {
                    let (dst, ty, variant) = (*dst, *ty, *variant);
                    let values = fields
                        .iter()
                        .map(|r| take(frame, *r))
                        .collect::<Result<Vec<_>, _>>()?;
                    put(
                        frame,
                        dst,
                        Value::aggregate_with_variant(ty, variant, values),
                    )?;
                    frame.pc += 1;
                }
                Instruction::ProjectMove { dst, src, field } => {
                    let (dst, src, field) = (*dst, *src, *field);
                    let value = get(frame, src)?;
                    let aggregate = aggregate_place(&value, true)?;
                    let field = runtime_field_index(a, &aggregate.borrow(), field)?;
                    let value = aggregate
                        .borrow_mut()
                        .fields
                        .get_mut(field)
                        .and_then(Option::take)
                        .ok_or(RuntimeError::TypeConfusion)?;
                    put(frame, dst, value)?;
                    frame.pc += 1;
                }
                Instruction::ProjectCopy { dst, src, field } => {
                    let (dst, src, field) = (*dst, *src, *field);
                    let value = get(frame, src)?;
                    let aggregate = aggregate_place(&value, false)?;
                    let field = runtime_field_index(a, &aggregate.borrow(), field)?;
                    let field_value = aggregate
                        .borrow()
                        .fields
                        .get(field)
                        .and_then(Option::as_ref)
                        .ok_or(RuntimeError::TypeConfusion)?
                        .clone();
                    let value = copy_value(a, fun.register_types[dst as usize], &field_value)?;
                    put(frame, dst, value)?;
                    frame.pc += 1;
                }
                Instruction::ReborrowShared { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let (referent_type, target) = match get(frame, src)? {
                        Value::Reference {
                            referent_type,
                            target,
                            ..
                        } => (referent_type, target),
                        _ => return Err(RuntimeError::TypeConfusion),
                    };
                    put(
                        frame,
                        dst,
                        Value::Reference {
                            referent_type,
                            unique: false,
                            target,
                        },
                    )?;
                    frame.pc += 1;
                }
                Instruction::ReborrowUnique { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let (referent_type, target) = match get(frame, src)? {
                        Value::Reference {
                            referent_type,
                            unique: true,
                            target,
                        } => (referent_type, target),
                        _ => return Err(RuntimeError::TypeConfusion),
                    };
                    put(
                        frame,
                        dst,
                        Value::Reference {
                            referent_type,
                            unique: true,
                            target,
                        },
                    )?;
                    frame.pc += 1;
                }
                Instruction::ProjectBorrowShared { dst, src, field }
                | Instruction::ProjectBorrowUnique { dst, src, field } => {
                    let (dst, src, field) = (*dst, *src, *field);
                    let unique = matches!(ins, Instruction::ProjectBorrowUnique { .. });
                    let value = get(frame, src)?;
                    let aggregate = aggregate_place(&value, unique)?;
                    let field = runtime_field_index(a, &aggregate.borrow(), field)?;
                    if aggregate
                        .borrow()
                        .fields
                        .get(field)
                        .ok_or(RuntimeError::TypeConfusion)?
                        .is_none()
                    {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    let referent_type = match a
                        .checked_type(fun.register_types[dst as usize])
                        .ok_or(RuntimeError::TypeConfusion)?
                        .representation()
                    {
                        Type::RefShared { referent } if !unique => *referent,
                        Type::RefUnique { referent } if unique => *referent,
                        _ => return Err(RuntimeError::TypeConfusion),
                    };
                    // A callable environment may store a reference handle as
                    // a field. Borrowing that field with a destination whose
                    // referent is the stored handle's referent is a per-call
                    // reborrow of the captured target, not a borrow of the
                    // handle slot itself. The verifier admits this flattened
                    // form only for shared reborrows, or for a unique reborrow
                    // through an originally unique captured handle.
                    let flattened = {
                        let aggregate = aggregate.borrow();
                        match aggregate.fields.get(field).and_then(Option::as_ref) {
                            Some(Value::Reference {
                                referent_type: captured_referent,
                                unique: captured_unique,
                                target,
                            }) if *captured_referent == referent_type
                                && (!unique || *captured_unique) =>
                            {
                                Some(target.clone())
                            }
                            _ => None,
                        }
                    };
                    put(
                        frame,
                        dst,
                        Value::Reference {
                            referent_type,
                            unique,
                            target: flattened
                                .unwrap_or(ReferenceTarget::AggregateField { aggregate, field }),
                        },
                    )?;
                    frame.pc += 1;
                }
                Instruction::EnumTag { dst, src } => {
                    let (dst, src) = (*dst, *src);
                    let raw = match get(frame, src)? {
                        Value::Aggregate(aggregate) => aggregate
                            .borrow()
                            .variant
                            .ok_or(RuntimeError::TypeConfusion)?,
                        Value::Reference { target, .. } => reference_target_enum_tag(&target)?,
                        _ => return Err(RuntimeError::TypeConfusion),
                    };
                    // The stored aggregate tag is the variant's position; the
                    // emitted runtime tag is the explicit discriminant when the
                    // variant declares one, else its index.
                    let tag = enum_variant_tag(a, fun.register_types[src as usize], raw)?;
                    put(frame, dst, Value::U64(u64::from(tag)))?;
                    frame.pc += 1;
                }
                Instruction::Drop { register } => {
                    let register = *register;
                    let value = match frame.registers[register as usize].take() {
                        Some(Value::Place(slot)) => slot
                            .take_and_reclaim_if_initialized()
                            .map_err(|_| RuntimeError::EmptyRegister(register))?,
                        Some(value) => Some(value),
                        None => None,
                    };
                    if let Some(value) = value {
                        let expected = fun.register_types[register as usize];
                        self.destroy_typed(expected, value)?;
                    }
                    frame.pc += 1;
                }
                Instruction::Deconstruct { src } => {
                    let src = *src;
                    let shell = take(frame, src)?;
                    if trace_errors {
                        match &shell {
                            Value::Aggregate(aggregate) => {
                                let aggregate = aggregate.borrow();
                                let occupied = aggregate
                                    .fields
                                    .iter()
                                    .enumerate()
                                    .filter_map(|(field, value)| value.is_some().then_some(field))
                                    .collect::<Vec<_>>();
                                if !occupied.is_empty() {
                                    eprintln!(
                                        "g1-vm-deconstruct-mismatch register={src} declared_type={} runtime_type={} variant={:?} occupied_fields={occupied:?}",
                                        fun.register_types[src as usize],
                                        aggregate.ty,
                                        aggregate.variant,
                                    );
                                }
                            }
                            value => eprintln!(
                                "g1-vm-deconstruct-mismatch register={src} declared_type={} runtime_kind={}",
                                fun.register_types[src as usize],
                                runtime_value_kind(value),
                            ),
                        }
                    }
                    release_aggregate_shell(shell)?;
                    frame.pc += 1;
                }
                Instruction::Primitive { dst, op, args } => {
                    let (dst, op) = (*dst, *op);
                    let arg_types = args
                        .iter()
                        .map(|register| fun.register_types[*register as usize])
                        .collect::<Vec<_>>();
                    let values = args
                        .iter()
                        .map(|r| take(frame, *r))
                        .collect::<Result<Vec<_>, _>>()?;
                    let v = primitive_typed(
                        a,
                        fun.register_types[dst as usize],
                        op,
                        &arg_types,
                        &values,
                    )?;
                    put(frame, dst, v)?;
                    frame.pc += 1;
                }
                Instruction::Jump { target } => frame.pc = *target,
                Instruction::Switch {
                    discr,
                    cases,
                    otherwise,
                } => {
                    let (discr, otherwise) = (*discr, *otherwise);
                    let value = get(frame, discr)?;
                    let mut target = otherwise;
                    for (constant, case_target) in cases {
                        let constant = a
                            .checked_constant(*constant)
                            .ok_or(RuntimeError::TypeConfusion)?;
                        if constant_eq(&value, constant) {
                            target = *case_target;
                            break;
                        }
                    }
                    frame.pc = target;
                }
                Instruction::Call {
                    dst,
                    function,
                    args,
                } => {
                    let (dst, function) = (*dst, *function);
                    let values = args
                        .iter()
                        .map(|r| take(frame, *r))
                        .collect::<Result<Vec<_>, _>>()?;
                    frame.pc += 1;
                    stack.push(make_verified_frame(a, function, values, Value::Unit, dst)?);
                }
                Instruction::TailCall { function, args } => {
                    let function = *function;
                    let values = args
                        .iter()
                        .map(|r| take(frame, *r))
                        .collect::<Result<Vec<_>, _>>()?;
                    let return_dst = frame.return_dst;
                    let mut replacement =
                        make_verified_frame(a, function, values, Value::Unit, return_dst)?;
                    replacement.delimiter = frame.delimiter.take();
                    replacement.guards.append(&mut frame.guards);
                    replacement
                        .deferred_frames
                        .append(&mut frame.deferred_frames);
                    self.destroy_frame_registers(frame)?;
                    *frame = replacement;
                }
                Instruction::CallSelf { dst, args } => {
                    let dst = *dst;
                    if !matches!(fun.receiver_mode, Some(0 | 1)) {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    let values = args
                        .iter()
                        .map(|r| take(frame, *r))
                        .collect::<Result<Vec<_>, _>>()?;
                    let receiver = get(frame, 0)?.clone();
                    let function = frame.function;
                    frame.pc += 1;
                    stack.push(make_verified_frame(a, function, values, receiver, dst)?);
                }
                Instruction::TailCallSelf { args } => {
                    if fun.receiver_mode.is_none() {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    let values = args
                        .iter()
                        .map(|r| take(frame, *r))
                        .collect::<Result<Vec<_>, _>>()?;
                    let receiver = take(frame, 0)?;
                    let function = frame.function;
                    let return_dst = frame.return_dst;
                    let mut replacement =
                        make_verified_frame(a, function, values, receiver, return_dst)?;
                    replacement.delimiter = frame.delimiter.take();
                    replacement.guards.append(&mut frame.guards);
                    replacement
                        .deferred_frames
                        .append(&mut frame.deferred_frames);
                    self.destroy_frame_registers(frame)?;
                    *frame = replacement;
                }
                Instruction::CallKnownReceiver {
                    dst,
                    function,
                    receiver,
                    args,
                } => {
                    let (dst, function, receiver) = (*dst, *function, *receiver);
                    let callee = a
                        .functions
                        .get(function as usize)
                        .ok_or(RuntimeError::TypeConfusion)?;
                    if callee.receiver_mode != Some(0) {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    let receiver = get(frame, receiver)?.clone();
                    let values = args
                        .iter()
                        .map(|r| take(frame, *r))
                        .collect::<Result<Vec<_>, _>>()?;
                    frame.pc += 1;
                    stack.push(make_verified_frame(a, function, values, receiver, dst)?);
                }
                Instruction::TailCallKnownReceiver {
                    function,
                    receiver,
                    args,
                } => {
                    let (function, receiver) = (*function, *receiver);
                    let callee = a
                        .functions
                        .get(function as usize)
                        .ok_or(RuntimeError::TypeConfusion)?;
                    if callee.receiver_mode != Some(0) {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    let receiver = get(frame, receiver)?.clone();
                    let values = args
                        .iter()
                        .map(|r| take(frame, *r))
                        .collect::<Result<Vec<_>, _>>()?;
                    let return_dst = frame.return_dst;
                    let mut replacement =
                        make_verified_frame(a, function, values, receiver, return_dst)?;
                    replacement.delimiter = frame.delimiter.take();
                    replacement.guards.append(&mut frame.guards);
                    replacement
                        .deferred_frames
                        .append(&mut frame.deferred_frames);
                    self.destroy_frame_registers(frame)?;
                    *frame = replacement;
                }
                Instruction::MakeCallable {
                    dst,
                    callable_type,
                    function,
                    captures,
                } => {
                    let (dst, callable_type, function) = (*dst, *callable_type, *function);
                    if fun.register_types[dst as usize] != callable_type {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    let Type::Callable { capture_type, .. } = a
                        .checked_type(callable_type)
                        .ok_or(RuntimeError::TypeConfusion)?
                        .representation()
                    else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    let values = captures
                        .iter()
                        .map(|register| take(frame, *register))
                        .collect::<Result<Vec<_>, _>>()?;
                    let capture = if *capture_type == crate::bytecode::UNIT {
                        if !values.is_empty() {
                            return Err(RuntimeError::TypeConfusion);
                        }
                        Value::Unit
                    } else {
                        Value::aggregate(*capture_type, values)
                    };
                    put(
                        frame,
                        dst,
                        Value::Callable(ControlHandle::new(CallableValue {
                            callable_type,
                            function,
                            capture: ArenaObject::new_tracked(Some(capture)),
                        })),
                    )?;
                    frame.pc += 1;
                }
                Instruction::MakeHandler {
                    dst,
                    handler_def,
                    clauses,
                } => {
                    let (dst, handler_def) = (*dst, *handler_def);
                    let handler_type = fun.register_types[dst as usize];
                    let values = clauses
                        .iter()
                        .map(|register| take(frame, *register).map(Some))
                        .collect::<Result<Vec<_>, _>>()?;
                    let definition = a
                        .checked_handler_def(handler_def)
                        .ok_or(RuntimeError::TypeConfusion)?;
                    for (value, clause) in values.iter().zip(&definition.clauses) {
                        let Some(Value::Callable(callable)) = value else {
                            return Err(RuntimeError::TypeConfusion);
                        };
                        let receiver_mode = a
                            .functions
                            .get(callable.function() as usize)
                            .and_then(|function| function.receiver_mode)
                            .ok_or(RuntimeError::TypeConfusion)?;
                        if clause_requires_reusable_receiver(a, clause) && receiver_mode == 2 {
                            return Err(RuntimeError::TypeConfusion);
                        }
                    }
                    put(
                        frame,
                        dst,
                        Value::Handler(ControlHandle::new(HandlerValue {
                            handler_type,
                            handler_def,
                            clauses: values,
                        })),
                    )?;
                    frame.pc += 1;
                }
                Instruction::MakeHandlerShared {
                    dst,
                    handler_def,
                    functions,
                    captures,
                } => {
                    let (dst, handler_def) = (*dst, *handler_def);
                    let handler_type = fun.register_types[dst as usize];
                    let Type::Handler {
                        capture_type: clause_tuple,
                        ..
                    } = a
                        .checked_type(handler_type)
                        .ok_or(RuntimeError::TypeConfusion)?
                        .representation()
                    else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    let clause_types = runtime_field_types(a, *clause_tuple, None)?;
                    if clause_types.len() != functions.len() || functions.is_empty() {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    // The stored environment type comes from the clause
                    // callable descriptors: a mixed handler's first clause
                    // may receive the environment through a borrowed view,
                    // so its receiver register holds a reference type, not
                    // the environment itself.
                    let Type::Callable {
                        capture_type: environment_type,
                        ..
                    } = a
                        .checked_type(clause_types[0])
                        .ok_or(RuntimeError::TypeConfusion)?
                        .representation()
                    else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    let environment_type = *environment_type;
                    let values = captures
                        .iter()
                        .map(|register| take(frame, *register))
                        .collect::<Result<Vec<_>, _>>()?;
                    let environment = if environment_type == crate::bytecode::UNIT {
                        if !values.is_empty() {
                            return Err(RuntimeError::TypeConfusion);
                        }
                        Value::Unit
                    } else {
                        Value::aggregate(environment_type, values)
                    };
                    let shared = ArenaObject::new_tracked(Some(environment));
                    let clauses = functions
                        .iter()
                        .copied()
                        .zip(clause_types)
                        .map(|(function, callable_type)| {
                            Some(Value::Callable(ControlHandle::new(CallableValue {
                                callable_type,
                                function,
                                capture: shared.clone(),
                            })))
                        })
                        .collect();
                    put(
                        frame,
                        dst,
                        Value::Handler(ControlHandle::new(HandlerValue {
                            handler_type,
                            handler_def,
                            clauses,
                        })),
                    )?;
                    frame.pc += 1;
                }
                Instruction::MakeBindingPack {
                    dst,
                    binding_type,
                    payloads,
                } => {
                    let (dst, binding_type) = (*dst, *binding_type);
                    let values = payloads
                        .iter()
                        .map(|register| take(frame, *register))
                        .collect::<Result<Vec<_>, _>>()?;
                    put(frame, dst, Value::aggregate(binding_type, values))?;
                    frame.pc += 1;
                }
                Instruction::CallIndirect {
                    dst,
                    callable,
                    receiver_mode,
                    args,
                } => {
                    let (dst, callable, receiver_mode) = (*dst, *callable, *receiver_mode);
                    let (function, receiver, guard) =
                        callable_receiver(a, frame, callable, receiver_mode)?;
                    let values = args
                        .iter()
                        .map(|register| take(frame, *register))
                        .collect::<Result<Vec<_>, _>>()?;
                    frame.pc += 1;
                    let mut callee = make_verified_frame(a, function, values, receiver, dst)?;
                    if let Some(guard) = guard {
                        callee.guards.push(guard);
                    }
                    stack.push(callee);
                }
                Instruction::TailCallIndirect {
                    callable,
                    receiver_mode,
                    args,
                } => {
                    let (callable, receiver_mode) = (*callable, *receiver_mode);
                    let (function, receiver, guard) =
                        callable_receiver(a, frame, callable, receiver_mode)?;
                    let values = args
                        .iter()
                        .map(|register| take(frame, *register))
                        .collect::<Result<Vec<_>, _>>()?;
                    let return_dst = frame.return_dst;
                    let mut replacement =
                        make_verified_frame(a, function, values, receiver, return_dst)?;
                    if let Some(guard) = guard {
                        replacement.guards.push(guard);
                    }
                    replacement.delimiter = frame.delimiter.take();
                    replacement.guards.append(&mut frame.guards);
                    replacement
                        .deferred_frames
                        .append(&mut frame.deferred_frames);
                    self.destroy_frame_registers(frame)?;
                    *frame = replacement;
                }
                Instruction::Handle {
                    dst,
                    handler,
                    body,
                    args,
                } => {
                    let (dst, handler, body) = (*dst, *handler, *body);
                    let handler = take(frame, handler)?;
                    let body = take(frame, body)?;
                    let (function, receiver) = owned_callable_receiver(a, body, 2)?;
                    let values = args
                        .iter()
                        .map(|register| take(frame, *register))
                        .collect::<Result<Vec<_>, _>>()?;
                    frame.pc += 1;
                    let mut body_frame =
                        make_verified_frame(a, function, values, receiver, Some(dst))?;
                    body_frame.delimiter = Some(handler);
                    stack.push(body_frame);
                }
                Instruction::Perform {
                    dst: None,
                    protocol,
                    operation,
                    payloads,
                } => {
                    let (protocol, operation) = (*protocol, *operation);
                    let values = payloads
                        .iter()
                        .map(|register| take(frame, *register))
                        .collect::<Result<Vec<_>, _>>()?;
                    let selected = select_handler_clause(a, &mut stack, protocol, operation)?;
                    let delimiter = selected.delimiter;
                    let return_dst = stack[delimiter].return_dst;
                    let deferred_frames = stack.split_off(delimiter);
                    let (function, receiver) =
                        owned_callable_receiver(a, selected.callable, selected.receiver_mode)?;
                    let mut clause =
                        make_verified_frame(a, function, values, receiver, return_dst)?;
                    clause.guards.push(selected.handler_guard);
                    clause.deferred_frames = deferred_frames;
                    stack.push(clause);
                }
                Instruction::Perform {
                    dst: Some(_perform_dst),
                    protocol,
                    operation,
                    payloads,
                } => {
                    let (protocol, operation) = (*protocol, *operation);
                    let mut values = payloads
                        .iter()
                        .map(|register| take(frame, *register))
                        .collect::<Result<Vec<_>, _>>()?;
                    frame.pc += 1;
                    let selected = select_handler_clause(a, &mut stack, protocol, operation)?;
                    let delimiter = selected.delimiter;
                    let return_dst = stack[delimiter].return_dst;
                    let mut frames = stack.split_off(delimiter);
                    let resumption_type = selected
                        .resumption_type
                        .ok_or(RuntimeError::TypeConfusion)?;
                    let Type::Resumption {
                        lower_uses,
                        upper_uses,
                        ..
                    } = a
                        .checked_type(resumption_type)
                        .ok_or(RuntimeError::TypeConfusion)?
                        .representation()
                    else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    if upper_uses.is_none_or(|upper| upper > 1) {
                        for captured in &mut frames {
                            self.prune_frame_for_continuation(captured, CapturePruning::Multishot)?;
                        }
                        let mut validation = SnapshotValidationContext::default();
                        for captured in &frames {
                            validation.validate_frame(a, captured)?;
                        }
                    } else if *lower_uses == 0 {
                        for captured in &mut frames {
                            self.prune_frame_for_continuation(
                                captured,
                                CapturePruning::Cancellation,
                            )?;
                        }
                    }
                    values.push(Value::Resumption(ControlHandle::new(Some(
                        ResumptionValue {
                            resumption_type,
                            frames,
                        },
                    ))));
                    let (function, receiver) =
                        owned_callable_receiver(a, selected.callable, selected.receiver_mode)?;
                    let mut clause =
                        make_verified_frame(a, function, values, receiver, return_dst)?;
                    clause.guards.push(selected.handler_guard);
                    stack.push(clause);
                }
                Instruction::Resume {
                    dst,
                    resumption,
                    receiver_mode,
                    value,
                } => {
                    let (dst, resumption, receiver_mode, value) =
                        (*dst, *resumption, *receiver_mode, *value);
                    let expected_resumption_type = fun.register_types[resumption as usize];
                    let Type::Resumption { upper_uses, .. } = a
                        .checked_type(expected_resumption_type)
                        .ok_or(RuntimeError::TypeConfusion)?
                        .representation()
                    else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    let reusable = upper_uses.is_none_or(|upper| upper > 1);
                    if !matches!(receiver_mode, 0..=2)
                        || (receiver_mode < 2 && !reusable)
                        || (receiver_mode == 2 && *upper_uses == Some(0))
                    {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    let resumption_value = if receiver_mode == 2 {
                        take(frame, resumption)?
                    } else {
                        get(frame, resumption)?.clone()
                    };
                    let Value::Resumption(resumption) = resumption_value else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    let value = take(frame, value)?;
                    let mut captured = if receiver_mode == 2 {
                        resumption
                            .try_borrow_mut()
                            .map_err(|_| RuntimeError::TypeConfusion)?
                            .take()
                            .ok_or(RuntimeError::TypeConfusion)?
                    } else {
                        let stored = resumption
                            .try_borrow()
                            .map_err(|_| RuntimeError::TypeConfusion)?;
                        clone_resumption_snapshot(
                            a,
                            stored.as_ref().ok_or(RuntimeError::TypeConfusion)?,
                        )?
                    };
                    if captured.resumption_type != expected_resumption_type {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    frame.pc += 1;
                    captured.frames[0].return_dst = Some(dst);
                    let last = captured
                        .frames
                        .last_mut()
                        .ok_or(RuntimeError::TypeConfusion)?;
                    let function = self
                        .artifact
                        .function(last.function)
                        .ok_or(RuntimeError::InvalidFunction(last.function))?;
                    let perform_pc = function
                        .checked_pc(last.pc.checked_sub(1).ok_or(RuntimeError::TypeConfusion)?)
                        .ok_or(RuntimeError::TypeConfusion)?;
                    let Instruction::Perform {
                        dst: Some(perform_dst),
                        ..
                    } = function.instruction(perform_pc)
                    else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    put(last, *perform_dst, value)?;
                    stack.extend(captured.frames);
                }
                Instruction::TailResume {
                    resumption,
                    receiver_mode,
                    value,
                } => {
                    let (resumption, receiver_mode, value) = (*resumption, *receiver_mode, *value);
                    let expected_resumption_type = fun.register_types[resumption as usize];
                    let Type::Resumption { upper_uses, .. } = a
                        .checked_type(expected_resumption_type)
                        .ok_or(RuntimeError::TypeConfusion)?
                        .representation()
                    else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    let reusable = upper_uses.is_none_or(|upper| upper > 1);
                    if !matches!(receiver_mode, 0..=2)
                        || (receiver_mode < 2 && !reusable)
                        || (receiver_mode == 2 && *upper_uses == Some(0))
                    {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    let resumption_value = if receiver_mode == 2 {
                        take(frame, resumption)?
                    } else {
                        get(frame, resumption)?.clone()
                    };
                    let Value::Resumption(resumption) = resumption_value else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    let value = take(frame, value)?;
                    let mut captured = if receiver_mode == 2 {
                        resumption
                            .try_borrow_mut()
                            .map_err(|_| RuntimeError::TypeConfusion)?
                            .take()
                            .ok_or(RuntimeError::TypeConfusion)?
                    } else {
                        let stored = resumption
                            .try_borrow()
                            .map_err(|_| RuntimeError::TypeConfusion)?;
                        clone_resumption_snapshot(
                            a,
                            stored.as_ref().ok_or(RuntimeError::TypeConfusion)?,
                        )?
                    };
                    if captured.resumption_type != expected_resumption_type {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    let return_dst = frame.return_dst;
                    captured
                        .frames
                        .first_mut()
                        .ok_or(RuntimeError::TypeConfusion)?
                        .return_dst = return_dst;
                    let last = captured
                        .frames
                        .last_mut()
                        .ok_or(RuntimeError::TypeConfusion)?;
                    let function = self
                        .artifact
                        .function(last.function)
                        .ok_or(RuntimeError::InvalidFunction(last.function))?;
                    let perform_pc = function
                        .checked_pc(last.pc.checked_sub(1).ok_or(RuntimeError::TypeConfusion)?)
                        .ok_or(RuntimeError::TypeConfusion)?;
                    let Instruction::Perform {
                        dst: Some(perform_dst),
                        ..
                    } = function.instruction(perform_pc)
                    else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    put(last, *perform_dst, value)?;
                    transfer_tail_resume_deferred_frames(frame, last);

                    let mut resumed = captured.frames.into_iter();
                    let replacement = resumed.next().ok_or(RuntimeError::TypeConfusion)?;
                    let abandoned = std::mem::replace(frame, replacement);
                    self.destroy_frame(abandoned)?;
                    stack.extend(resumed);
                }
                Instruction::Cancel { dst, resumption } => {
                    let (dst, resumption) = (*dst, *resumption);
                    let Value::Resumption(resumption) = take(frame, resumption)? else {
                        return Err(RuntimeError::TypeConfusion);
                    };
                    let captured = resumption
                        .borrow_mut()
                        .take()
                        .ok_or(RuntimeError::TypeConfusion)?;
                    for captured_frame in captured.frames.into_iter().rev() {
                        self.destroy_frame(captured_frame)?;
                    }
                    put(frame, dst, Value::Unit)?;
                    frame.pc += 1;
                }
                Instruction::HostCall { dst, import, args } => {
                    let (dst, import) = (*dst, *import);
                    let arguments = args
                        .iter()
                        .map(|register| take(frame, *register))
                        .collect::<Result<Vec<_>, _>>()?;
                    let host = self.host.as_deref().ok_or_else(|| {
                        let capability = a
                            .import_id(import)
                            .map(|import| a.import_capability(import).to_owned())
                            .unwrap_or_else(|| "<invalid import>".into());
                        RuntimeError::HostLink(HostLinkError::DeniedCapability(capability))
                    })?;
                    let import_id = a.import_id(import).ok_or(RuntimeError::TypeConfusion)?;
                    let resolved = *resolved_imports
                        .get(import_id.index())
                        .ok_or(RuntimeError::TypeConfusion)?;
                    let value = invoke_host(host, resolved, arguments)?;
                    if let Some(dst) = dst {
                        if !value_matches(a, &value, fun.register_types[dst as usize]) {
                            return Err(RuntimeError::TypeConfusion);
                        }
                        put(frame, dst, value)?;
                    } else if !matches!(value, Value::Unit) {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    frame.pc += 1;
                }
                Instruction::Return { src } => {
                    let src = *src;
                    let value = match src {
                        Some(src) => take(frame, src)?,
                        None => Value::Unit,
                    };
                    let dst = frame.return_dst;
                    if let Some(handler) = frame.delimiter.take() {
                        self.destroy_runtime_typed(handler)?;
                    }
                    for guard in frame.guards.drain(..).rev() {
                        self.destroy_runtime_typed(guard)?;
                    }
                    for deferred in frame.deferred_frames.drain(..).rev() {
                        self.destroy_frame(deferred)?;
                    }
                    stack.pop();
                    match stack.last_mut() {
                        Some(caller) => {
                            if let Some(dst) = dst {
                                put(caller, dst, value)?;
                            } else if !matches!(value, Value::Unit) {
                                return Err(RuntimeError::TypeConfusion);
                            }
                        }
                        None => {
                            if let Some(profile) = &instruction_profile {
                                profile.report();
                            }
                            return Ok(value);
                        }
                    }
                }
                Instruction::LabelPush {
                    slot,
                    result_register,
                    target,
                } => {
                    let (slot, result_register, target) = (*slot, *result_register, *target);
                    frame
                        .labels
                        .try_reserve(1)
                        .map_err(|_| RuntimeError::AllocationLimit)?;
                    frame.labels.push(RuntimeLabel {
                        slot,
                        result_register,
                        target,
                    });
                    frame.pc += 1;
                }
                Instruction::LabelPop { slot } => {
                    let slot = *slot;
                    if frame.labels.last().map(|entry| entry.slot) != Some(slot) {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    frame.labels.pop();
                    frame.pc += 1;
                }
                Instruction::Leave { slot, value } => {
                    let (slot, value) = (*slot, *value);
                    let index = frame
                        .labels
                        .iter()
                        .rposition(|entry| entry.slot == slot)
                        .ok_or(RuntimeError::TypeConfusion)?;
                    let label = frame.labels[index].clone();
                    let protected = take(frame, value)?;
                    let source = cleanup_registers(&self.artifact, frame.function, frame.pc)?;
                    let destination =
                        cleanup_registers(&self.artifact, frame.function, label.target)?;
                    if source.len() < destination.len()
                        || source[source.len() - destination.len()..] != *destination
                    {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    for &register in &source[..source.len() - destination.len()] {
                        if let Some(value) = frame.registers[register as usize].take() {
                            self.destroy_typed(fun.register_types[register as usize], value)?;
                        }
                    }
                    frame.labels.truncate(index);
                    put(frame, label.result_register, protected)?;
                    frame.pc = label.target;
                }
                Instruction::Unreachable => {
                    if std::env::var_os("G1_VM_STATE_TRACE").is_some() {
                        eprintln!(
                            "g1-vm reached unreachable in function {} `{}` at pc {}",
                            frame.function, fun.name, frame.pc
                        );
                    }
                    return Err(RuntimeError::ReachedUnreachable);
                }
                Instruction::Abort { message } => {
                    let message = a
                        .abort_message((fun.code_start + frame.pc) as usize)
                        .map(str::to_owned)
                        .or(message.clone());
                    if trace_errors {
                        eprintln!("g1-vm-error stack-begin depth={}", stack.len());
                        for (depth, traced) in stack.iter().rev().enumerate() {
                            let traced_instruction = self
                                .artifact
                                .function(traced.function)
                                .and_then(|function| {
                                    let checked = function.checked_pc(traced.pc)?;
                                    Some((
                                        function.descriptor().name.as_str(),
                                        function.instruction(checked),
                                    ))
                                });
                            match traced_instruction {
                                Some((name, instruction)) => eprintln!(
                                    "g1-vm-error frame={depth} function={} name={name:?} pc={} instruction={instruction:?}",
                                    traced.function, traced.pc
                                ),
                                None => eprintln!(
                                    "g1-vm-error frame={depth} function={} pc={} instruction=<unavailable>",
                                    traced.function, traced.pc
                                ),
                            }
                            if let Some(caller_pc) = traced.pc.checked_sub(1)
                                && let Some(function) = self.artifact.function(traced.function)
                                && let Some(checked) = function.checked_pc(caller_pc)
                            {
                                eprintln!(
                                    "g1-vm-error frame={depth} previous_pc={caller_pc} previous_instruction={:?}",
                                    function.instruction(checked)
                                );
                            }
                        }
                        eprintln!("g1-vm-error stack-end");
                    }
                    return Err(RuntimeError::Aborted(message));
                }
            }
        }
    }
}

fn transfer_tail_resume_deferred_frames(current: &mut Frame, resumed_innermost: &mut Frame) {
    resumed_innermost
        .deferred_frames
        .append(&mut current.deferred_frames);
}

fn link_imports(
    artifact: &ExecutionImage,
    grants: &BTreeSet<String>,
) -> Result<Vec<ResolvedImport>, HostLinkError> {
    artifact
        .imports
        .iter()
        .enumerate()
        .map(|(index, import)| {
            let id = artifact
                .import_id(index as u32)
                .expect("enumerated import ID is checked");
            let capability = artifact.import_capability(id);
            if !grants.contains(capability) {
                return Err(HostLinkError::DeniedCapability(capability.to_owned()));
            }
            resolve_standard_import(artifact, id, import)
        })
        .collect()
}

fn resolve_standard_import(
    artifact: &ExecutionImage,
    id: crate::verify::ImageImportId,
    import: &Import,
) -> Result<ResolvedImport, HostLinkError> {
    let capability = artifact.import_capability(id);
    let symbol = artifact.import_symbol(id);
    let resolved = match (capability, symbol) {
        ("process.args", "get") => ResolvedImport::ProcessArgs,
        ("fs.read", "read") => ResolvedImport::FsRead,
        ("fs.write", "write") => ResolvedImport::FsWrite,
        ("diagnostic", "write") => ResolvedImport::DiagnosticWrite,
        _ => {
            return Err(HostLinkError::UnknownImport {
                capability: capability.to_owned(),
                symbol: symbol.to_owned(),
            });
        }
    };
    if !import.may_trap {
        return Err(HostLinkError::MissingMayTrap {
            capability: capability.to_owned(),
            symbol: symbol.to_owned(),
        });
    }
    let signature = &import.signature;
    let no_effects = signature.outward_protocols.is_empty();
    let valid = match resolved {
        ResolvedImport::ProcessArgs => {
            signature.params.is_empty()
                && matches!(artifact.checked_type(signature.result).map(Type::representation), Some(Type::Array { element }) if *element == TEXT)
        }
        ResolvedImport::FsRead => signature.params == [TEXT] && signature.result == BYTES,
        ResolvedImport::FsWrite => signature.params == [TEXT, BYTES] && signature.result == UNIT,
        ResolvedImport::DiagnosticWrite => signature.params == [TEXT] && signature.result == UNIT,
    } && no_effects;
    if !valid {
        return Err(HostLinkError::SignatureMismatch {
            capability: capability.to_owned(),
            symbol: symbol.to_owned(),
        });
    }
    Ok(resolved)
}

fn invoke_host(
    host: &dyn Host,
    import: ResolvedImport,
    args: Vec<Value>,
) -> Result<Value, RuntimeError> {
    let fault = RuntimeError::HostFault;
    match import {
        ResolvedImport::ProcessArgs => {
            if !args.is_empty() {
                return Err(RuntimeError::TypeConfusion);
            }
            Ok(Value::array(
                TEXT,
                host.process_args()
                    .map_err(fault)?
                    .into_iter()
                    .map(|value| Value::Text(value.into())),
            ))
        }
        ResolvedImport::FsRead => {
            let [Value::Text(path)] = args.as_slice() else {
                return Err(RuntimeError::TypeConfusion);
            };
            let path = String::from_utf8(clone_output(path.as_bytes())?)
                .map_err(|_| RuntimeError::TypeConfusion)?;
            Ok(Value::Bytes(host.fs_read(path).map_err(fault)?.into()))
        }
        ResolvedImport::FsWrite => {
            let [Value::Text(path), Value::Bytes(contents)] = args.as_slice() else {
                return Err(RuntimeError::TypeConfusion);
            };
            let path = String::from_utf8(clone_output(path.as_bytes())?)
                .map_err(|_| RuntimeError::TypeConfusion)?;
            let contents = clone_output(contents)?;
            host.fs_write(path, contents).map_err(fault)?;
            Ok(Value::Unit)
        }
        ResolvedImport::DiagnosticWrite => {
            let [Value::Text(message)] = args.as_slice() else {
                return Err(RuntimeError::TypeConfusion);
            };
            let message = String::from_utf8(clone_output(message.as_bytes())?)
                .map_err(|_| RuntimeError::TypeConfusion)?;
            host.diagnostic_write(message).map_err(fault)?;
            Ok(Value::Unit)
        }
    }
}

fn make_frame(
    a: &ExecutionImage,
    function: u32,
    args: Vec<Value>,
    receiver: Value,
    return_dst: Option<u32>,
) -> Result<Frame, RuntimeError> {
    let f = a
        .functions
        .get(function as usize)
        .ok_or(RuntimeError::InvalidFunction(function))?;
    if args.len() != f.params.len() {
        return Err(RuntimeError::WrongArgumentCount {
            expected: f.params.len(),
            actual: args.len(),
        });
    }
    for (i, (v, &ty)) in args.iter().zip(&f.params).enumerate() {
        if !value_matches(a, v, ty) {
            return Err(RuntimeError::WrongArgumentType {
                argument: i,
                expected: ty,
            });
        }
    }
    if !value_matches(a, &receiver, f.register_types[0]) {
        return Err(RuntimeError::TypeConfusion);
    }
    Ok(frame_from_verified_values(
        f, function, args, receiver, return_dst,
    ))
}

/// Construct a frame from values already produced by verified bytecode.
///
/// Public VM entry and host results are checked at their trust boundaries.
/// Re-walking complete arrays and aggregates at every internal call would
/// redundantly re-prove the verifier's call signature and can turn recursive
/// accumulation into quadratic execution.
fn make_verified_frame(
    a: &ExecutionImage,
    function: u32,
    args: Vec<Value>,
    receiver: Value,
    return_dst: Option<u32>,
) -> Result<Frame, RuntimeError> {
    let f = a
        .functions
        .get(function as usize)
        .ok_or(RuntimeError::InvalidFunction(function))?;
    if args.len() != f.params.len() {
        return Err(RuntimeError::WrongArgumentCount {
            expected: f.params.len(),
            actual: args.len(),
        });
    }
    Ok(frame_from_verified_values(
        f, function, args, receiver, return_dst,
    ))
}

fn frame_from_verified_values(
    f: &crate::bytecode::Function,
    function: u32,
    args: Vec<Value>,
    receiver: Value,
    return_dst: Option<u32>,
) -> Frame {
    let mut registers = vec![None; f.register_types.len()];
    registers[0] = Some(receiver);
    for (i, v) in args.into_iter().enumerate() {
        registers[i + 1] = Some(v)
    }
    Frame {
        function,
        pc: 0,
        registers,
        return_dst,
        delimiter: None,
        guards: Vec::new(),
        deferred_frames: Vec::new(),
        // `label_slot_count` is an artifact namespace bound, not the number
        // of simultaneously live labels. In particular, it is a compact u32
        // scalar and can be much larger than the artifact itself. Allocate
        // lazily at `LabelPush` so hostile-but-valid metadata cannot turn a
        // tiny function into a process-scale speculative reservation.
        labels: Vec::new(),
    }
}

fn cleanup_registers(
    artifact: &VerifiedArtifact,
    function: u32,
    pc: u32,
) -> Result<&[u32], RuntimeError> {
    let function = artifact
        .function(function)
        .ok_or(RuntimeError::InvalidFunction(function))?;
    let pc = function.checked_pc(pc).ok_or(RuntimeError::TypeConfusion)?;
    Ok(function.cleanup_registers(pc))
}

impl Vm {
    fn prune_frame_for_continuation(
        &self,
        frame: &mut Frame,
        pruning: CapturePruning,
    ) -> Result<(), RuntimeError> {
        let function = self
            .artifact
            .function(frame.function)
            .ok_or(RuntimeError::InvalidFunction(frame.function))?;
        let pc = function
            .checked_pc(frame.pc)
            .ok_or(RuntimeError::TypeConfusion)?;
        let retained = match pruning {
            CapturePruning::Multishot => function.multishot_registers(pc),
            CapturePruning::Cancellation => function.cancellation_registers(pc),
        }
        .collect::<BTreeSet<_>>();
        // Cancellation is an early frame exit, so excluded values must obey
        // the verifier's borrow-aware cleanup order. Register order is not an
        // ownership order: a projected owner can have a lower register than
        // the reference which must be ended before it.
        for register in function.cleanup_registers(pc).iter().copied() {
            if retained.contains(&register) {
                continue;
            }
            if let Some(value) = frame.registers[register as usize].take() {
                self.destroy_typed(
                    function.descriptor().register_types[register as usize],
                    value,
                )?;
            }
        }
        // Cleanup metadata orders ownership-bearing values. Empty/copy-only
        // temporaries can remain outside that plan; discard any such excluded
        // residue only after every ordered loan and owner has been released.
        for (register, value) in frame.registers.iter_mut().enumerate() {
            if !retained.contains(&(register as u32))
                && let Some(value) = value.take()
            {
                self.destroy_typed(function.descriptor().register_types[register], value)?;
            }
        }
        Ok(())
    }

    fn destroy_frame(&self, mut frame: Frame) -> Result<(), RuntimeError> {
        self.destroy_frame_registers(&mut frame)?;
        if let Some(handler) = frame.delimiter.take() {
            self.destroy_runtime_typed(handler)?;
        }
        for guard in frame.guards.drain(..).rev() {
            self.destroy_runtime_typed(guard)?;
        }
        for deferred in frame.deferred_frames.drain(..).rev() {
            self.destroy_frame(deferred)?;
        }
        Ok(())
    }

    fn destroy_frame_registers(&self, frame: &mut Frame) -> Result<(), RuntimeError> {
        let function = self
            .artifact
            .function(frame.function)
            .ok_or(RuntimeError::InvalidFunction(frame.function))?;
        let pc = frame
            .pc
            .min(function.descriptor().code_len.saturating_sub(1));
        for &register in cleanup_registers(&self.artifact, frame.function, pc)? {
            if frame.registers[register as usize].is_some() {
                let value = take(frame, register)?;
                self.destroy_typed(
                    function.descriptor().register_types[register as usize],
                    value,
                )?;
            }
        }
        Ok(())
    }

    fn destroy_runtime_typed(&self, value: Value) -> Result<(), RuntimeError> {
        let ty = match &value {
            Value::Aggregate(aggregate) => aggregate.borrow().ty,
            Value::Callable(callable) => callable.callable_type(),
            Value::Handler(handler) => handler.borrow().handler_type,
            Value::Resumption(resumption) => resumption
                .borrow()
                .as_ref()
                .map(|resumption| resumption.resumption_type)
                .ok_or(RuntimeError::TypeConfusion)?,
            Value::Array(array) => {
                let element = array.borrow().element_type;
                self.artifact
                    .image()
                    .types
                    .iter()
                    .position(
                        |ty| matches!(ty, Type::Array { element: actual } if *actual == element),
                    )
                    .ok_or(RuntimeError::TypeConfusion)? as TypeId
            }
            _ => return Err(RuntimeError::TypeConfusion),
        };
        self.destroy_typed(ty, value)
    }

    fn destroy_typed(&self, ty: TypeId, value: Value) -> Result<(), RuntimeError> {
        let value = match value {
            Value::Place(slot) => slot
                .take_and_reclaim()
                .map_err(|_| RuntimeError::TypeConfusion)?,
            value => value,
        };
        let a = self.artifact.image();
        if let Some(glue) = a.drop_glue.iter().find(|glue| glue.ty == ty) {
            let slot = self
                .slots
                .insert(Some(value))
                .map_err(|_| RuntimeError::TypeConfusion)?;
            let reference = Value::Reference {
                referent_type: ty,
                unique: true,
                target: ReferenceTarget::DropSlot(slot.clone()),
            };
            let result = self.run(glue.function, vec![reference])?;
            if !matches!(result, Value::Unit) {
                return Err(RuntimeError::TypeConfusion);
            }
            let value = slot
                .take_and_reclaim()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            return self.destroy_structural(ty, value);
        }
        self.destroy_structural(ty, value)
    }

    /// Destroy children without consulting glue for `ty` again.  Recursive
    /// children still receive their own declared-type glue exactly once.
    fn destroy_structural(&self, ty: TypeId, value: Value) -> Result<(), RuntimeError> {
        let a = self.artifact.image();
        match value {
            Value::Aggregate(aggregate) => {
                let mut aggregate = aggregate
                    .try_unwrap()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                if aggregate.ty != ty {
                    return Err(RuntimeError::TypeConfusion);
                }
                let layout_type = match a.checked_type(ty).map(Type::representation) {
                    Some(Type::BindingPack { payload_type, .. }) => *payload_type,
                    _ => ty,
                };
                let field_types = runtime_field_types(a, layout_type, aggregate.variant)?;
                if field_types.len() != aggregate.fields.len() {
                    return Err(RuntimeError::TypeConfusion);
                }
                for (field_type, field) in field_types
                    .into_iter()
                    .zip(aggregate.fields.drain(..))
                    .rev()
                {
                    if let Some(field) = field {
                        self.destroy_typed(field_type, field)?;
                    }
                }
            }
            Value::Array(array) => {
                let Type::Array { element } = a
                    .types
                    .get(ty as usize)
                    .map(Type::representation)
                    .ok_or(RuntimeError::TypeConfusion)?
                else {
                    return Err(RuntimeError::TypeConfusion);
                };
                let mut array = array
                    .try_unwrap()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                if array.element_type != *element {
                    return Err(RuntimeError::TypeConfusion);
                }
                while let Some(slot) = array.slots.pop() {
                    if let Some(value) = slot {
                        self.destroy_typed(*element, value)?;
                    }
                }
            }
            Value::Callable(callable) => {
                let Type::Callable { capture_type, .. } = a
                    .types
                    .get(ty as usize)
                    .map(Type::representation)
                    .ok_or(RuntimeError::TypeConfusion)?
                else {
                    return Err(RuntimeError::TypeConfusion);
                };
                let Ok(callable) = callable.try_unwrap() else {
                    return Ok(());
                };
                let Ok(capture) = callable.capture.try_unwrap() else {
                    // Handler operation alternatives may share one sealed
                    // incoming environment. The last alias owns destruction.
                    return Ok(());
                };
                if let Some(capture) = capture {
                    self.destroy_typed(*capture_type, capture)?;
                }
            }
            Value::Handler(handler) => {
                let Ok(handler) = handler.try_unwrap() else {
                    // Delimiter frames and active clause frames may
                    // temporarily share the runtime handler. The last owner
                    // performs the structural destruction.
                    return Ok(());
                };
                let mut handler = handler;
                if handler.handler_type != ty {
                    return Err(RuntimeError::TypeConfusion);
                }
                while let Some(clause) = handler.clauses.pop() {
                    if let Some(clause) = clause {
                        self.destroy_runtime_typed(clause)?;
                    }
                }
            }
            Value::Resumption(resumption) => {
                if let Some(resumption) = resumption
                    .try_unwrap()
                    .map_err(|_| RuntimeError::TypeConfusion)?
                {
                    if resumption.resumption_type != ty {
                        return Err(RuntimeError::TypeConfusion);
                    }
                    for frame in resumption.frames.into_iter().rev() {
                        self.destroy_frame(frame)?;
                    }
                }
            }
            Value::Unit
            | Value::I64(_)
            | Value::I128(_)
            | Value::U64(_)
            | Value::U128(_)
            | Value::F32(_)
            | Value::F64(_)
            | Value::Text(_)
            | Value::Bytes(_)
            | Value::Reference { .. } => {}
            Value::Place(_) => unreachable!("places are unwrapped before destruction"),
        }
        Ok(())
    }
}
#[inline(always)]
fn take(f: &mut Frame, r: u32) -> Result<Value, RuntimeError> {
    let value = f.registers[r as usize]
        .take()
        .ok_or(RuntimeError::EmptyRegister(r))?;
    match value {
        Value::Place(slot) => slot
            .take_and_reclaim()
            .map_err(|_| RuntimeError::EmptyRegister(r)),
        value => Ok(value),
    }
}

fn runtime_value_kind(value: &Value) -> &'static str {
    match value {
        Value::Unit => "unit",
        Value::I64(_) => "i64",
        Value::I128(_) => "i128",
        Value::U64(_) => "u64",
        Value::U128(_) => "u128",
        Value::F32(_) => "f32",
        Value::F64(_) => "f64",
        Value::Text(_) => "text",
        Value::Bytes(_) => "bytes",
        Value::Place(_) => "place",
        Value::Array(_) => "array",
        Value::Reference { .. } => "reference",
        Value::Aggregate(_) => "aggregate",
        Value::Callable(_) => "callable",
        Value::Handler(_) => "handler",
        Value::Resumption(_) => "resumption",
    }
}
#[inline(always)]
fn get(f: &Frame, r: u32) -> Result<Value, RuntimeError> {
    let value = f.registers[r as usize]
        .as_ref()
        .ok_or(RuntimeError::EmptyRegister(r))?;
    match value {
        Value::Place(slot) => slot.get().map_err(|_| RuntimeError::EmptyRegister(r)),
        value => Ok(value.clone()),
    }
}
#[inline(always)]
fn put(f: &mut Frame, r: u32, v: Value) -> Result<(), RuntimeError> {
    if f.registers[r as usize].replace(v).is_some() {
        Err(RuntimeError::TypeConfusion)
    } else {
        Ok(())
    }
}

fn whole_place(slots: &SlotStore, f: &mut Frame, r: u32) -> Result<ReferenceTarget, RuntimeError> {
    let current = f.registers[r as usize]
        .take()
        .ok_or(RuntimeError::EmptyRegister(r))?;
    let slot = match current {
        Value::Place(slot) => slot,
        value => slots
            .insert(Some(value))
            .map_err(|_| RuntimeError::TypeConfusion)?,
    };
    f.registers[r as usize] = Some(Value::Place(slot.clone()));
    Ok(ReferenceTarget::WholePlace(slot))
}

fn copy_reference_target(
    artifact: &ExecutionImage,
    referent_type: TypeId,
    target: &ReferenceTarget,
) -> Result<Value, RuntimeError> {
    let value = match target {
        ReferenceTarget::DropSlot(slot) | ReferenceTarget::WholePlace(slot) => {
            slot.get().map_err(|_| RuntimeError::TypeConfusion)?
        }
        ReferenceTarget::CallableCapture(slot) => slot
            .try_borrow()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .as_ref()
            .cloned()
            .ok_or(RuntimeError::TypeConfusion)?,
        ReferenceTarget::Array(array) => Value::Array(array.clone()),
        ReferenceTarget::ArrayElement { array, index } => array
            .try_borrow()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .slots
            .get(*index)
            .and_then(Option::as_ref)
            .cloned()
            .ok_or(RuntimeError::TypeConfusion)?,
        ReferenceTarget::Aggregate(aggregate) => Value::Aggregate(aggregate.clone()),
        ReferenceTarget::AggregateField { aggregate, field } => aggregate
            .try_borrow()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .fields
            .get(*field)
            .and_then(Option::as_ref)
            .cloned()
            .ok_or(RuntimeError::TypeConfusion)?,
    };
    copy_value(artifact, referent_type, &value)
}

/// Observe a reference value stored behind another reference without applying
/// ordinary value-copy rules. The verifier has already established a child
/// loan and suspended the parent capability, so cloning this runtime handle
/// does not create a second source-level owner of a unique reference.
fn observe_reference_target(target: &ReferenceTarget) -> Result<Value, RuntimeError> {
    let value = match target {
        ReferenceTarget::DropSlot(slot) | ReferenceTarget::WholePlace(slot) => {
            slot.get().map_err(|_| RuntimeError::TypeConfusion)?
        }
        ReferenceTarget::CallableCapture(slot) => slot
            .try_borrow()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .as_ref()
            .cloned()
            .ok_or(RuntimeError::TypeConfusion)?,
        ReferenceTarget::ArrayElement { array, index } => array
            .try_borrow()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .slots
            .get(*index)
            .and_then(Option::as_ref)
            .cloned()
            .ok_or(RuntimeError::TypeConfusion)?,
        ReferenceTarget::AggregateField { aggregate, field } => aggregate
            .try_borrow()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .fields
            .get(*field)
            .and_then(Option::as_ref)
            .cloned()
            .ok_or(RuntimeError::TypeConfusion)?,
        ReferenceTarget::Array(_) | ReferenceTarget::Aggregate(_) => {
            return Err(RuntimeError::TypeConfusion);
        }
    };
    if matches!(value, Value::Reference { .. }) {
        Ok(value)
    } else {
        Err(RuntimeError::TypeConfusion)
    }
}

/// The emitted runtime tag (discriminant) for the enum variant at
/// `variant_index` in the enum type `ty` (which may be a reference wrapper).
/// An explicit `EnumVariant.tag` overrides the index-derived tag; unwrapping a
/// reference keeps the referent enum's discriminant set authoritative.
fn enum_variant_tag(
    a: &ExecutionImage,
    ty: TypeId,
    variant_index: u32,
) -> Result<u32, RuntimeError> {
    fn resolve(t: &Type, variant_index: u32) -> Result<u32, RuntimeError> {
        let Type::Enum { variants, .. } = t else {
            return Err(RuntimeError::TypeConfusion);
        };
        variants
            .get(variant_index as usize)
            .map(|variant| variant.discriminant(variant_index))
            .ok_or(RuntimeError::TypeConfusion)
    }
    match a.checked_type(ty).map(Type::representation) {
        Some(Type::RefShared { referent }) | Some(Type::RefUnique { referent }) => {
            let referent = a
                .checked_type(*referent)
                .map(Type::representation)
                .ok_or(RuntimeError::TypeConfusion)?;
            resolve(referent, variant_index)
        }
        Some(other) => resolve(other, variant_index),
        None => Err(RuntimeError::TypeConfusion),
    }
}

fn reference_target_enum_tag(target: &ReferenceTarget) -> Result<u32, RuntimeError> {
    fn value_tag(value: &Value) -> Result<u32, RuntimeError> {
        let Value::Aggregate(aggregate) = value else {
            return Err(RuntimeError::TypeConfusion);
        };
        let tag = aggregate
            .try_borrow()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .variant
            .ok_or(RuntimeError::TypeConfusion)?;
        Ok(tag)
    }

    match target {
        ReferenceTarget::DropSlot(slot) | ReferenceTarget::WholePlace(slot) => {
            value_tag(&slot.get().map_err(|_| RuntimeError::TypeConfusion)?)
        }
        ReferenceTarget::CallableCapture(slot) => {
            let value = slot.try_borrow().map_err(|_| RuntimeError::TypeConfusion)?;
            value_tag(value.as_ref().ok_or(RuntimeError::TypeConfusion)?)
        }
        ReferenceTarget::Aggregate(aggregate) => {
            let tag = aggregate
                .try_borrow()
                .map_err(|_| RuntimeError::TypeConfusion)?
                .variant
                .ok_or(RuntimeError::TypeConfusion)?;
            Ok(tag)
        }
        ReferenceTarget::AggregateField { aggregate, field } => {
            let aggregate = aggregate
                .try_borrow()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            value_tag(
                aggregate
                    .fields
                    .get(*field)
                    .and_then(Option::as_ref)
                    .ok_or(RuntimeError::TypeConfusion)?,
            )
        }
        ReferenceTarget::ArrayElement { array, index } => {
            let array = array
                .try_borrow()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            value_tag(
                array
                    .slots
                    .get(*index)
                    .and_then(Option::as_ref)
                    .ok_or(RuntimeError::TypeConfusion)?,
            )
        }
        ReferenceTarget::Array(_) => Err(RuntimeError::TypeConfusion),
    }
}

fn take_reference_target(target: &ReferenceTarget) -> Result<Value, RuntimeError> {
    match target {
        ReferenceTarget::DropSlot(slot) | ReferenceTarget::WholePlace(slot) => {
            slot.take().map_err(|_| RuntimeError::TypeConfusion)
        }
        ReferenceTarget::CallableCapture(slot) => slot
            .try_borrow_mut()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .take()
            .ok_or(RuntimeError::TypeConfusion),
        ReferenceTarget::Array(array) => {
            let mut array = array
                .try_borrow_mut()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            let element_type = array.element_type;
            let value = std::mem::replace(
                &mut *array,
                crate::value::ArrayValue {
                    element_type,
                    slots: Vec::new(),
                    logical_capacity: 0,
                },
            );
            Ok(Value::Array(ArenaObject::new_tracked(value)))
        }
        ReferenceTarget::ArrayElement { array, index } => array
            .try_borrow_mut()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .slots
            .get_mut(*index)
            .and_then(Option::take)
            .ok_or(RuntimeError::TypeConfusion),
        ReferenceTarget::Aggregate(aggregate) => {
            let mut aggregate = aggregate
                .try_borrow_mut()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            let ty = aggregate.ty;
            let variant = aggregate.variant;
            let value = std::mem::replace(
                &mut *aggregate,
                crate::value::AggregateValue {
                    ty,
                    variant,
                    fields: Vec::new(),
                },
            );
            Ok(Value::Aggregate(ArenaObject::new_tracked(value)))
        }
        ReferenceTarget::AggregateField { aggregate, field } => aggregate
            .try_borrow_mut()
            .map_err(|_| RuntimeError::TypeConfusion)?
            .fields
            .get_mut(*field)
            .and_then(Option::take)
            .ok_or(RuntimeError::TypeConfusion),
    }
}

fn store_reference_target(target: &ReferenceTarget, value: Value) -> Result<(), RuntimeError> {
    match target {
        ReferenceTarget::DropSlot(slot) | ReferenceTarget::WholePlace(slot) => {
            slot.put(value).map_err(|_| RuntimeError::TypeConfusion)?;
        }
        ReferenceTarget::CallableCapture(slot) => {
            let mut slot = slot
                .try_borrow_mut()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            if slot.is_some() {
                return Err(RuntimeError::TypeConfusion);
            }
            *slot = Some(value);
        }
        ReferenceTarget::Array(array) => {
            let Value::Array(value) = value else {
                return Err(RuntimeError::TypeConfusion);
            };
            let value = value
                .try_unwrap()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            let mut target = array
                .try_borrow_mut()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            if !target.slots.is_empty() || target.logical_capacity != 0 {
                return Err(RuntimeError::TypeConfusion);
            }
            *target = value;
        }
        ReferenceTarget::ArrayElement { array, index } => {
            let mut array = array
                .try_borrow_mut()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            let slot = array
                .slots
                .get_mut(*index)
                .ok_or(RuntimeError::TypeConfusion)?;
            if slot.is_some() {
                return Err(RuntimeError::TypeConfusion);
            }
            *slot = Some(value);
        }
        ReferenceTarget::Aggregate(aggregate) => {
            let Value::Aggregate(value) = value else {
                return Err(RuntimeError::TypeConfusion);
            };
            let value = value
                .try_unwrap()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            let mut target = aggregate
                .try_borrow_mut()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            if !target.fields.is_empty() {
                return Err(RuntimeError::TypeConfusion);
            }
            *target = value;
        }
        ReferenceTarget::AggregateField { aggregate, field } => {
            let mut aggregate = aggregate
                .try_borrow_mut()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            let slot = aggregate
                .fields
                .get_mut(*field)
                .ok_or(RuntimeError::TypeConfusion)?;
            if slot.is_some() {
                return Err(RuntimeError::TypeConfusion);
            }
            *slot = Some(value);
        }
    }
    Ok(())
}

struct SelectedHandlerClause {
    delimiter: usize,
    callable: Value,
    receiver_mode: u32,
    handler_guard: Value,
    resumption_type: Option<TypeId>,
}

fn clause_requires_reusable_receiver(a: &ExecutionImage, clause: &HandlerClause) -> bool {
    let Some(resumption_type) = clause.resumption_type else {
        return false;
    };
    !matches!(
        a.checked_type(resumption_type).map(Type::representation),
        Some(Type::Resumption {
            upper_uses: Some(0),
            ..
        })
    )
}

fn select_handler_clause(
    a: &ExecutionImage,
    stack: &mut [Frame],
    protocol: u32,
    operation: u32,
) -> Result<SelectedHandlerClause, RuntimeError> {
    let protocol_descriptor = a
        .checked_protocol(protocol)
        .ok_or(RuntimeError::TypeConfusion)?;
    if operation as usize >= protocol_descriptor.operations.len() {
        return Err(RuntimeError::TypeConfusion);
    }
    for delimiter in (0..stack.len()).rev() {
        let Some(Value::Handler(handler)) = &stack[delimiter].delimiter else {
            continue;
        };
        let handler_guard = Value::Handler(handler.clone());
        let mut handler = handler.borrow_mut();
        let definition = a
            .checked_handler_def(handler.handler_def)
            .ok_or(RuntimeError::TypeConfusion)?;
        let Some(clause_index) = definition
            .clauses
            .iter()
            .position(|clause| clause.protocol == protocol && clause.operation == operation)
        else {
            // Partial handlers deliberately pass unhandled operations to the
            // next outward delimiter.
            continue;
        };
        let clause_definition = &definition.clauses[clause_index];
        let callable = handler.clauses[clause_index]
            .as_ref()
            .ok_or(RuntimeError::TypeConfusion)?;
        let Value::Callable(callable_value) = callable else {
            return Err(RuntimeError::TypeConfusion);
        };
        let receiver_mode = a
            .functions
            .get(callable_value.function() as usize)
            .and_then(|function| function.receiver_mode)
            .ok_or(RuntimeError::TypeConfusion)?;
        if clause_requires_reusable_receiver(a, clause_definition) && receiver_mode == 2 {
            return Err(RuntimeError::TypeConfusion);
        }
        let callable = if receiver_mode == 2 {
            handler.clauses[clause_index]
                .take()
                .ok_or(RuntimeError::TypeConfusion)?
        } else {
            callable.clone()
        };
        return Ok(SelectedHandlerClause {
            delimiter,
            callable,
            receiver_mode,
            handler_guard,
            resumption_type: clause_definition.resumption_type,
        });
    }
    Err(RuntimeError::UnhandledEffect {
        protocol,
        operation,
    })
}

fn callable_receiver(
    a: &ExecutionImage,
    frame: &mut Frame,
    register: u32,
    receiver_mode: u32,
) -> Result<(u32, Value, Option<Value>), RuntimeError> {
    let callable = if receiver_mode == 2 {
        let Value::Callable(callable) = take(frame, register)? else {
            return Err(RuntimeError::TypeConfusion);
        };
        callable
    } else {
        let Value::Callable(callable) = get(frame, register)? else {
            return Err(RuntimeError::TypeConfusion);
        };
        callable.clone()
    };
    indirect_callable_receiver(a, callable, receiver_mode)
}

fn indirect_callable_receiver(
    a: &ExecutionImage,
    callable: ControlHandle<CallableValue>,
    requested_mode: u32,
) -> Result<(u32, Value, Option<Value>), RuntimeError> {
    let function = callable.function();
    let target = a
        .functions
        .get(function as usize)
        .ok_or(RuntimeError::InvalidFunction(function))?;
    let canonical_mode = target.receiver_mode.ok_or(RuntimeError::TypeConfusion)?;
    let Some(Type::Callable {
        capture_type,
        receiver_mode: described_mode,
        ..
    }) = a
        .types
        .get(callable.callable_type() as usize)
        .map(Type::representation)
    else {
        return Err(RuntimeError::TypeConfusion);
    };
    if *described_mode != canonical_mode || requested_mode > 2 || requested_mode < canonical_mode {
        return Err(RuntimeError::TypeConfusion);
    }
    let capture = callable.capture();
    let receiver = match canonical_mode {
        0 | 1 => Value::Reference {
            referent_type: *capture_type,
            unique: canonical_mode == 1,
            target: ReferenceTarget::CallableCapture(capture),
        },
        2 => capture
            .borrow_mut()
            .take()
            .ok_or(RuntimeError::TypeConfusion)?,
        _ => return Err(RuntimeError::TypeConfusion),
    };
    let guard = (requested_mode == 2 && canonical_mode < 2).then_some(Value::Callable(callable));
    Ok((function, receiver, guard))
}

fn owned_callable_receiver(
    a: &ExecutionImage,
    callable: Value,
    receiver_mode: u32,
) -> Result<(u32, Value), RuntimeError> {
    let Value::Callable(callable) = callable else {
        return Err(RuntimeError::TypeConfusion);
    };
    let function = callable.function();
    let target = a
        .functions
        .get(function as usize)
        .ok_or(RuntimeError::InvalidFunction(function))?;
    if target.receiver_mode != Some(receiver_mode) {
        return Err(RuntimeError::TypeConfusion);
    }
    let Some(Type::Callable {
        capture_type,
        receiver_mode: described_mode,
        ..
    }) = a
        .types
        .get(callable.callable_type() as usize)
        .map(Type::representation)
    else {
        return Err(RuntimeError::TypeConfusion);
    };
    if *described_mode != receiver_mode {
        return Err(RuntimeError::TypeConfusion);
    }
    let capture = callable.capture();
    let receiver = match receiver_mode {
        0 | 1 => Value::Reference {
            referent_type: *capture_type,
            unique: receiver_mode == 1,
            target: ReferenceTarget::CallableCapture(capture),
        },
        2 => capture
            .borrow_mut()
            .take()
            .ok_or(RuntimeError::TypeConfusion)?,
        _ => return Err(RuntimeError::TypeConfusion),
    };
    Ok((function, receiver))
}

/// Copy a register's value into an owned register value in exactly one deep
/// pass. The prior generic path cloned the register value (via `get`) and then
/// deep-copied that clone again (via `copy_value`), allocating the payload twice
/// for `Text`/`Bytes`/aggregate values. Reading the register in place and
/// running `copy_value` once is observationally identical: both produce the same
/// owned deep copy, and the discarded intermediate clone was never observable.
#[inline(always)]
fn copy_register(a: &ExecutionImage, f: &Frame, r: u32, ty: TypeId) -> Result<Value, RuntimeError> {
    let value = f.registers[r as usize]
        .as_ref()
        .ok_or(RuntimeError::EmptyRegister(r))?;
    match value {
        Value::Place(slot) => {
            let stored = slot.get().map_err(|_| RuntimeError::EmptyRegister(r))?;
            copy_value(a, ty, &stored)
        }
        value => copy_value(a, ty, value),
    }
}

fn copy_value(a: &ExecutionImage, ty: TypeId, value: &Value) -> Result<Value, RuntimeError> {
    let ty_descriptor = a.checked_type(ty).ok_or(RuntimeError::TypeConfusion)?;
    match (value, ty_descriptor.representation()) {
        (Value::Unit, Type::Unit) => Ok(Value::Unit),
        (Value::I64(value), _) => Ok(Value::I64(*value)),
        (Value::I128(value), Type::I128) => Ok(Value::I128(*value)),
        (Value::U64(value), _) => Ok(Value::U64(*value)),
        (Value::U128(value), Type::U128) => Ok(Value::U128(*value)),
        (Value::F32(value), Type::F32) => Ok(Value::F32(*value)),
        (Value::F64(value), _) => Ok(Value::F64(*value)),
        (Value::Text(value), Type::Text) => Ok(Value::Text(value.clone())),
        (Value::Bytes(value), Type::Bytes) => Ok(Value::Bytes(value.clone())),
        (Value::Reference { .. }, Type::RefShared { .. }) => Ok(value.clone()),
        (
            Value::Aggregate(aggregate),
            Type::Tuple { .. } | Type::Struct { .. } | Type::Enum { .. } | Type::BindingPack { .. },
        ) => {
            let aggregate = aggregate.borrow();
            let layout_type = match ty_descriptor.representation() {
                Type::BindingPack { payload_type, .. } => *payload_type,
                _ => ty,
            };
            let field_types = runtime_field_types(a, layout_type, aggregate.variant)?;
            let mut fields = Vec::new();
            reserve_output(&mut fields, aggregate.fields.len())?;
            for (field, field_type) in aggregate.fields.iter().zip(field_types) {
                fields.push(copy_value(
                    a,
                    field_type,
                    field.as_ref().ok_or(RuntimeError::TypeConfusion)?,
                )?);
            }
            Ok(Value::aggregate_with_variant(ty, aggregate.variant, fields))
        }
        (Value::Callable(callable), Type::Callable { capture_type, .. }) => {
            let callable_type = callable.callable_type();
            let function = callable.function();
            let capture_handle = callable.capture();
            let capture = capture_handle.borrow();
            let capture = copy_value(
                a,
                *capture_type,
                capture.as_ref().ok_or(RuntimeError::TypeConfusion)?,
            )?;
            Ok(Value::Callable(ControlHandle::new(CallableValue {
                callable_type,
                function,
                capture: ArenaObject::new_tracked(Some(capture)),
            })))
        }
        (Value::Resumption(resumption), Type::Resumption { copy: true, .. }) => {
            let stored = resumption.borrow();
            Ok(Value::Resumption(ControlHandle::new(Some(
                clone_resumption_snapshot(a, stored.as_ref().ok_or(RuntimeError::TypeConfusion)?)?,
            ))))
        }
        _ => Err(RuntimeError::TypeConfusion),
    }
}

#[derive(Default)]
struct SnapshotValidationContext {
    visited: BTreeSet<(u8, u128)>,
}

impl SnapshotValidationContext {
    fn validate_frame(
        &mut self,
        a: &ExecutionImage,
        frame: &RuntimeFrame,
    ) -> Result<(), RuntimeError> {
        let function = a
            .functions
            .get(frame.function as usize)
            .ok_or(RuntimeError::InvalidFunction(frame.function))?;
        if frame.registers.len() != function.register_types.len() {
            return Err(RuntimeError::TypeConfusion);
        }
        for (slot, &ty) in frame.registers.iter().zip(&function.register_types) {
            if let Some(value) = slot {
                self.validate_value(a, ty, value, true)?;
            }
        }
        if let Some(value) = &frame.delimiter {
            self.validate_runtime_value(a, value, false)?;
        }
        for value in &frame.guards {
            self.validate_runtime_value(a, value, false)?;
        }
        for deferred in &frame.deferred_frames {
            self.validate_frame(a, deferred)?;
        }
        Ok(())
    }

    fn validate_runtime_value(
        &mut self,
        a: &ExecutionImage,
        value: &Value,
        callable_must_be_copy: bool,
    ) -> Result<(), RuntimeError> {
        self.validate_value(
            a,
            runtime_value_type(a, value)?,
            value,
            callable_must_be_copy,
        )
    }

    fn validate_value(
        &mut self,
        a: &ExecutionImage,
        ty: TypeId,
        value: &Value,
        callable_must_be_copy: bool,
    ) -> Result<(), RuntimeError> {
        if let Value::Place(slot) = value {
            if self.visited.insert((0, slot.identity())) {
                self.validate_value(
                    a,
                    ty,
                    &slot.get().map_err(|_| RuntimeError::TypeConfusion)?,
                    callable_must_be_copy,
                )?;
            }
            return Ok(());
        }
        let descriptor = a.checked_type(ty).ok_or(RuntimeError::TypeConfusion)?;
        match (value, descriptor.representation()) {
            (Value::Unit, Type::Unit)
            | (Value::I64(_), Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::Isize)
            | (Value::I128(_), Type::I128)
            | (
                Value::U64(_),
                Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::Usize | Type::Char,
            )
            | (Value::U128(_), Type::U128)
            | (Value::F32(_), Type::F32)
            | (Value::F64(_), Type::F64)
            | (Value::Text(_), Type::Text)
            | (Value::Bytes(_), Type::Bytes) => Ok(()),
            (Value::Reference { unique: false, .. }, Type::RefShared { .. })
                if value_matches(a, value, ty) =>
            {
                Ok(())
            }
            (Value::Reference { .. }, Type::RefUnique { .. }) => Err(RuntimeError::TypeConfusion),
            (Value::Array(array), Type::Array { element }) => {
                if !self.visited.insert((1, array.identity())) {
                    return Ok(());
                }
                let array = array
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                if array.element_type != *element {
                    return Err(RuntimeError::TypeConfusion);
                }
                for value in array.slots.iter().flatten() {
                    self.validate_value(a, *element, value, true)?;
                }
                Ok(())
            }
            (
                Value::Aggregate(aggregate),
                Type::Tuple { .. }
                | Type::Struct { .. }
                | Type::Enum { .. }
                | Type::BindingPack { .. },
            ) => {
                if matches!(
                    descriptor.representation(),
                    Type::BindingPack { copy: false, .. }
                ) {
                    return Err(RuntimeError::TypeConfusion);
                }
                if !self.visited.insert((2, aggregate.identity())) {
                    return Ok(());
                }
                let aggregate = aggregate
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                if aggregate.ty != ty {
                    return Err(RuntimeError::TypeConfusion);
                }
                let layout = match descriptor.representation() {
                    Type::BindingPack { payload_type, .. } => *payload_type,
                    _ => ty,
                };
                let fields = runtime_field_types(a, layout, aggregate.variant)?;
                if fields.len() != aggregate.fields.len() {
                    return Err(RuntimeError::TypeConfusion);
                }
                for (slot, field_ty) in aggregate.fields.iter().zip(fields) {
                    if let Some(value) = slot {
                        self.validate_value(a, field_ty, value, true)?;
                    }
                }
                Ok(())
            }
            (
                Value::Callable(callable),
                Type::Callable {
                    capture_type, copy, ..
                },
            ) => {
                if callable.callable_type() != ty || (callable_must_be_copy && !copy) {
                    return Err(RuntimeError::TypeConfusion);
                }
                let capture = callable.capture();
                if self.visited.insert((3, capture.identity())) {
                    let capture = capture
                        .try_borrow()
                        .map_err(|_| RuntimeError::TypeConfusion)?;
                    self.validate_value(
                        a,
                        *capture_type,
                        capture.as_ref().ok_or(RuntimeError::TypeConfusion)?,
                        true,
                    )?;
                }
                Ok(())
            }
            (Value::Handler(handler), Type::Handler { handler_def, .. }) => {
                if !self.visited.insert((4, handler.identity())) {
                    return Ok(());
                }
                let handler = handler
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                if handler.handler_type != ty || handler.handler_def != *handler_def {
                    return Err(RuntimeError::TypeConfusion);
                }
                for clause in handler.clauses.iter().flatten() {
                    self.validate_runtime_value(a, clause, false)?;
                }
                Ok(())
            }
            (Value::Resumption(resumption), Type::Resumption { copy: true, .. }) => {
                if !self.visited.insert((5, resumption.identity())) {
                    return Ok(());
                }
                let resumption = resumption
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                let resumption = resumption.as_ref().ok_or(RuntimeError::TypeConfusion)?;
                if resumption.resumption_type != ty {
                    return Err(RuntimeError::TypeConfusion);
                }
                for frame in &resumption.frames {
                    self.validate_frame(a, frame)?;
                }
                Ok(())
            }
            _ => Err(RuntimeError::TypeConfusion),
        }
    }
}

#[derive(Default)]
struct SnapshotCloneContext {
    places: BTreeMap<u128, crate::value::SlotHandle>,
    arrays: BTreeMap<u128, ArenaObject<ArrayValue>>,
    aggregates: BTreeMap<u128, ArenaObject<AggregateValue>>,
    captures: BTreeMap<u128, ArenaObject<Option<Value>>>,
    callables: BTreeMap<u128, ControlHandle<CallableValue>>,
    handlers: BTreeMap<u128, ControlHandle<HandlerValue>>,
    resumptions: BTreeMap<u128, ControlHandle<Option<ResumptionValue>>>,
    populated: BTreeSet<(u8, u128)>,
}

impl SnapshotCloneContext {
    fn pre_register_runtime(
        &mut self,
        a: &ExecutionImage,
        value: &Value,
    ) -> Result<(), RuntimeError> {
        let ty = runtime_value_type(a, value)?;
        self.pre_register(a, ty, value)
    }

    fn pre_register(
        &mut self,
        a: &ExecutionImage,
        ty: TypeId,
        value: &Value,
    ) -> Result<(), RuntimeError> {
        if let Value::Place(slot) = value {
            let key = slot.identity();
            if self
                .places
                .insert(
                    key,
                    slot.empty_peer().map_err(|_| RuntimeError::TypeConfusion)?,
                )
                .is_none()
            {
                self.pre_register(a, ty, &slot.get().map_err(|_| RuntimeError::TypeConfusion)?)?;
            }
            return Ok(());
        }
        let ty_descriptor = a.checked_type(ty).ok_or(RuntimeError::TypeConfusion)?;
        match (value, ty_descriptor.representation()) {
            (Value::Array(array), Type::Array { element }) => {
                let key = array.identity();
                if self.arrays.contains_key(&key) {
                    return Ok(());
                }
                let source = array
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                self.arrays.insert(
                    key,
                    ArenaObject::new_tracked(ArrayValue {
                        element_type: source.element_type,
                        slots: vec![],
                        logical_capacity: source.logical_capacity,
                    }),
                );
                for value in source.slots.iter().flatten() {
                    self.pre_register(a, *element, value)?;
                }
            }
            (
                Value::Aggregate(aggregate),
                Type::Tuple { .. }
                | Type::Struct { .. }
                | Type::Enum { .. }
                | Type::BindingPack { .. },
            ) => {
                let key = aggregate.identity();
                if self.aggregates.contains_key(&key) {
                    return Ok(());
                }
                let source = aggregate
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                self.aggregates.insert(
                    key,
                    ArenaObject::new_tracked(AggregateValue {
                        ty,
                        variant: source.variant,
                        fields: vec![],
                    }),
                );
                let layout = match ty_descriptor.representation() {
                    Type::BindingPack { payload_type, .. } => *payload_type,
                    _ => ty,
                };
                for (value, field_ty) in
                    source
                        .fields
                        .iter()
                        .zip(runtime_field_types(a, layout, source.variant)?)
                {
                    if let Some(value) = value {
                        self.pre_register(a, field_ty, value)?;
                    }
                }
            }
            (Value::Callable(callable), Type::Callable { capture_type, .. }) => {
                let capture = callable.capture();
                let key = capture.identity();
                let cloned_capture = self
                    .captures
                    .entry(key)
                    .or_insert_with(|| ArenaObject::new_tracked(None))
                    .clone();
                self.callables
                    .entry(callable.identity())
                    .or_insert_with(|| {
                        ControlHandle::new(CallableValue {
                            callable_type: callable.callable_type(),
                            function: callable.function(),
                            capture: cloned_capture,
                        })
                    });
                if self.populated.insert((6, key))
                    && let Some(value) = capture
                        .try_borrow()
                        .map_err(|_| RuntimeError::TypeConfusion)?
                        .as_ref()
                {
                    self.pre_register(a, *capture_type, value)?;
                }
            }
            (Value::Handler(handler), Type::Handler { .. }) => {
                let key = handler.identity();
                if self.handlers.contains_key(&key) {
                    return Ok(());
                }
                let source = handler
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                self.handlers.insert(
                    key,
                    ControlHandle::new(HandlerValue {
                        handler_type: source.handler_type,
                        handler_def: source.handler_def,
                        clauses: vec![],
                    }),
                );
                for value in source.clauses.iter().flatten() {
                    self.pre_register_runtime(a, value)?;
                }
            }
            (Value::Resumption(resumption), Type::Resumption { copy: true, .. }) => {
                let key = resumption.identity();
                if self
                    .resumptions
                    .insert(key, ControlHandle::new(None))
                    .is_none()
                    && let Some(value) = resumption
                        .try_borrow()
                        .map_err(|_| RuntimeError::TypeConfusion)?
                        .as_ref()
                {
                    self.pre_register_resumption(a, value)?;
                }
            }
            (Value::Reference { unique: false, .. }, Type::RefShared { .. })
            | (Value::Unit, Type::Unit)
            | (Value::I64(_), _)
            | (Value::I128(_), Type::I128)
            | (Value::U64(_), _)
            | (Value::U128(_), Type::U128)
            | (Value::F32(_), Type::F32)
            | (Value::F64(_), Type::F64)
            | (Value::Text(_), Type::Text)
            | (Value::Bytes(_), Type::Bytes) => {}
            _ => return Err(RuntimeError::TypeConfusion),
        }
        Ok(())
    }

    fn pre_register_resumption(
        &mut self,
        a: &ExecutionImage,
        source: &ResumptionValue,
    ) -> Result<(), RuntimeError> {
        for frame in &source.frames {
            self.pre_register_frame(a, frame)?;
        }
        Ok(())
    }

    fn pre_register_frame(
        &mut self,
        a: &ExecutionImage,
        frame: &RuntimeFrame,
    ) -> Result<(), RuntimeError> {
        let function = &a.functions[frame.function as usize];
        for (slot, &ty) in frame.registers.iter().zip(&function.register_types) {
            if let Some(value) = slot {
                self.pre_register(a, ty, value)?;
            }
        }
        if let Some(value) = &frame.delimiter {
            self.pre_register_runtime(a, value)?;
        }
        for value in &frame.guards {
            self.pre_register_runtime(a, value)?;
        }
        for deferred in &frame.deferred_frames {
            self.pre_register_frame(a, deferred)?;
        }
        Ok(())
    }
}

/// Clone the complete VM-owned continuation graph. Owned nodes are registered
/// before any values are copied, so shared references can be remapped to the
/// corresponding node in each replay. Targets outside the captured graph stay
/// shared with their external owner. Unique references are never cloneable.
fn clone_resumption_snapshot(
    a: &ExecutionImage,
    source: &ResumptionValue,
) -> Result<ResumptionValue, RuntimeError> {
    let mut context = SnapshotCloneContext::default();
    context.pre_register_resumption(a, source)?;
    clone_resumption_snapshot_with(a, source, &mut context)
}

fn clone_resumption_snapshot_with(
    a: &ExecutionImage,
    source: &ResumptionValue,
    context: &mut SnapshotCloneContext,
) -> Result<ResumptionValue, RuntimeError> {
    let frames = source
        .frames
        .iter()
        .map(|frame| clone_runtime_frame_snapshot(a, frame, context))
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    Ok(ResumptionValue {
        resumption_type: source.resumption_type,
        frames,
    })
}

fn clone_runtime_frame_snapshot(
    a: &ExecutionImage,
    frame: &RuntimeFrame,
    context: &mut SnapshotCloneContext,
) -> Result<RuntimeFrame, RuntimeError> {
    let function = &a.functions[frame.function as usize];
    let registers = frame
        .registers
        .iter()
        .zip(&function.register_types)
        .map(|(slot, &ty)| {
            slot.as_ref()
                .map(|value| snapshot_clone_value(a, ty, value, context))
                .transpose()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let delimiter = frame
        .delimiter
        .as_ref()
        .map(|value| snapshot_clone_runtime_value(a, value, context))
        .transpose()?;
    let guards = frame
        .guards
        .iter()
        .map(|value| snapshot_clone_runtime_value(a, value, context))
        .collect::<Result<Vec<_>, _>>()?;
    let deferred_frames = frame
        .deferred_frames
        .iter()
        .map(|deferred| clone_runtime_frame_snapshot(a, deferred, context))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(RuntimeFrame {
        function: frame.function,
        pc: frame.pc,
        registers,
        return_dst: frame.return_dst,
        delimiter,
        guards,
        deferred_frames,
        labels: frame.labels.clone(),
    })
}

fn runtime_value_type(a: &ExecutionImage, value: &Value) -> Result<TypeId, RuntimeError> {
    Ok(match value {
        Value::Array(array) => {
            let element = array.borrow().element_type;
            a.types
                .iter()
                .position(|ty| matches!(ty, Type::Array { element: actual } if *actual == element))
                .ok_or(RuntimeError::TypeConfusion)? as TypeId
        }
        Value::Aggregate(aggregate) => aggregate.borrow().ty,
        Value::Callable(callable) => callable.callable_type(),
        Value::Handler(handler) => handler.borrow().handler_type,
        Value::Resumption(resumption) => resumption
            .borrow()
            .as_ref()
            .map(|value| value.resumption_type)
            .ok_or(RuntimeError::TypeConfusion)?,
        _ => return Err(RuntimeError::TypeConfusion),
    })
}

fn snapshot_clone_runtime_value(
    a: &ExecutionImage,
    value: &Value,
    context: &mut SnapshotCloneContext,
) -> Result<Value, RuntimeError> {
    snapshot_clone_value(a, runtime_value_type(a, value)?, value, context)
}

fn snapshot_clone_value(
    a: &ExecutionImage,
    ty: TypeId,
    value: &Value,
    context: &mut SnapshotCloneContext,
) -> Result<Value, RuntimeError> {
    if let Value::Place(slot) = value {
        let key = slot.identity();
        let cloned = context
            .places
            .get(&key)
            .cloned()
            .ok_or(RuntimeError::TypeConfusion)?;
        if context.populated.insert((0, key)) {
            let value = snapshot_clone_value(
                a,
                ty,
                &slot.get().map_err(|_| RuntimeError::TypeConfusion)?,
                context,
            )?;
            cloned.put(value).map_err(|_| RuntimeError::TypeConfusion)?;
        }
        return Ok(Value::Place(cloned));
    }
    let ty_descriptor = a.checked_type(ty).ok_or(RuntimeError::TypeConfusion)?;
    match (value, ty_descriptor.representation()) {
        (Value::Unit, Type::Unit) => Ok(Value::Unit),
        (Value::I64(value), _) => Ok(Value::I64(*value)),
        (Value::I128(value), Type::I128) => Ok(Value::I128(*value)),
        (Value::U64(value), _) => Ok(Value::U64(*value)),
        (Value::U128(value), Type::U128) => Ok(Value::U128(*value)),
        (Value::F32(value), Type::F32) => Ok(Value::F32(*value)),
        (Value::F64(value), Type::F64) => Ok(Value::F64(*value)),
        (Value::Text(value), Type::Text) => Ok(Value::Text(value.clone())),
        (Value::Bytes(value), Type::Bytes) => Ok(Value::Bytes(value.clone())),
        (Value::Array(array), Type::Array { element }) => {
            let key = array.identity();
            let cloned = context
                .arrays
                .get(&key)
                .cloned()
                .ok_or(RuntimeError::TypeConfusion)?;
            if context.populated.insert((1, key)) {
                let source = array
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                let mut slots = Vec::new();
                reserve_output(&mut slots, source.slots.len())?;
                for slot in &source.slots {
                    slots.push(
                        slot.as_ref()
                            .map(|value| snapshot_clone_value(a, *element, value, context))
                            .transpose()?,
                    );
                }
                cloned
                    .try_borrow_mut()
                    .map_err(|_| RuntimeError::TypeConfusion)?
                    .slots = slots;
            }
            Ok(Value::Array(cloned))
        }
        (
            Value::Aggregate(aggregate),
            Type::Tuple { .. } | Type::Struct { .. } | Type::Enum { .. } | Type::BindingPack { .. },
        ) => {
            let key = aggregate.identity();
            let cloned = context
                .aggregates
                .get(&key)
                .cloned()
                .ok_or(RuntimeError::TypeConfusion)?;
            if !context.populated.insert((2, key)) {
                return Ok(Value::Aggregate(cloned));
            }
            let aggregate = aggregate
                .try_borrow()
                .map_err(|_| RuntimeError::TypeConfusion)?;
            let layout_type = match ty_descriptor.representation() {
                Type::BindingPack { payload_type, .. } => *payload_type,
                _ => ty,
            };
            let field_types = runtime_field_types(a, layout_type, aggregate.variant)?;
            let mut fields = Vec::new();
            reserve_output(&mut fields, aggregate.fields.len())?;
            for (slot, field_type) in aggregate.fields.iter().zip(field_types) {
                fields.push(
                    slot.as_ref()
                        .map(|value| snapshot_clone_value(a, field_type, value, context))
                        .transpose()?,
                );
            }
            cloned
                .try_borrow_mut()
                .map_err(|_| RuntimeError::TypeConfusion)?
                .fields = fields;
            Ok(Value::Aggregate(cloned))
        }
        (Value::Callable(callable), Type::Callable { capture_type, .. }) => {
            let source_capture = callable.capture();
            let key = source_capture.identity();
            let capture = context
                .captures
                .get(&key)
                .cloned()
                .ok_or(RuntimeError::TypeConfusion)?;
            if context.populated.insert((3, key)) {
                let source = source_capture
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                let value = source
                    .as_ref()
                    .map(|value| snapshot_clone_value(a, *capture_type, value, context))
                    .transpose()?;
                *capture
                    .try_borrow_mut()
                    .map_err(|_| RuntimeError::TypeConfusion)? = value;
            }
            let cloned = context
                .callables
                .get(&callable.identity())
                .cloned()
                .ok_or(RuntimeError::TypeConfusion)?;
            debug_assert!(ArenaObject::ptr_eq(&cloned.capture(), &capture));
            Ok(Value::Callable(cloned))
        }
        (Value::Handler(handler), Type::Handler { .. }) => {
            let key = handler.identity();
            let cloned = context
                .handlers
                .get(&key)
                .cloned()
                .ok_or(RuntimeError::TypeConfusion)?;
            if context.populated.insert((4, key)) {
                let source = handler
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                let clauses = source
                    .clauses
                    .iter()
                    .map(|slot| {
                        slot.as_ref()
                            .map(|value| snapshot_clone_runtime_value(a, value, context))
                            .transpose()
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                cloned
                    .try_borrow_mut()
                    .map_err(|_| RuntimeError::TypeConfusion)?
                    .clauses = clauses;
            }
            Ok(Value::Handler(cloned))
        }
        (Value::Resumption(resumption), Type::Resumption { copy: true, .. }) => {
            let key = resumption.identity();
            let cloned = context
                .resumptions
                .get(&key)
                .cloned()
                .ok_or(RuntimeError::TypeConfusion)?;
            if context.populated.insert((5, key)) {
                let source = resumption
                    .try_borrow()
                    .map_err(|_| RuntimeError::TypeConfusion)?;
                let value = source
                    .as_ref()
                    .map(|value| clone_resumption_snapshot_with(a, value, context))
                    .transpose()?;
                *cloned
                    .try_borrow_mut()
                    .map_err(|_| RuntimeError::TypeConfusion)? = value;
            }
            Ok(Value::Resumption(cloned))
        }
        (
            Value::Reference {
                referent_type,
                unique: false,
                target,
            },
            Type::RefShared { referent },
        ) if referent_type == referent => Ok(Value::Reference {
            referent_type: *referent_type,
            unique: false,
            target: remap_shared_reference_target(target, context)?,
        }),
        (Value::Reference { .. }, Type::RefUnique { .. }) => Err(RuntimeError::TypeConfusion),
        _ => Err(RuntimeError::TypeConfusion),
    }
}

fn remap_shared_reference_target(
    target: &ReferenceTarget,
    context: &SnapshotCloneContext,
) -> Result<ReferenceTarget, RuntimeError> {
    Ok(match target {
        ReferenceTarget::DropSlot(_) => return Err(RuntimeError::TypeConfusion),
        ReferenceTarget::WholePlace(slot) => {
            context.places.get(&slot.identity()).cloned().map_or_else(
                || ReferenceTarget::WholePlace(slot.clone()),
                ReferenceTarget::WholePlace,
            )
        }
        ReferenceTarget::Array(array) => {
            context.arrays.get(&array.identity()).cloned().map_or_else(
                || ReferenceTarget::Array(array.clone()),
                ReferenceTarget::Array,
            )
        }
        ReferenceTarget::ArrayElement { array, index } => ReferenceTarget::ArrayElement {
            array: context
                .arrays
                .get(&array.identity())
                .cloned()
                .unwrap_or_else(|| array.clone()),
            index: *index,
        },
        ReferenceTarget::Aggregate(aggregate) => context
            .aggregates
            .get(&aggregate.identity())
            .cloned()
            .map_or_else(
                || ReferenceTarget::Aggregate(aggregate.clone()),
                ReferenceTarget::Aggregate,
            ),
        ReferenceTarget::AggregateField { aggregate, field } => ReferenceTarget::AggregateField {
            aggregate: context
                .aggregates
                .get(&aggregate.identity())
                .cloned()
                .unwrap_or_else(|| aggregate.clone()),
            field: *field,
        },
        ReferenceTarget::CallableCapture(capture) => context
            .captures
            .get(&capture.identity())
            .cloned()
            .map_or_else(
                || ReferenceTarget::CallableCapture(capture.clone()),
                ReferenceTarget::CallableCapture,
            ),
    })
}

fn constant_value(c: ImageConstant<'_>) -> Result<Value, RuntimeError> {
    match c {
        ImageConstant::Text(text) => Ok(Value::Text(Rc::from(text))),
        ImageConstant::Bytes(bytes) => Ok(Value::Bytes(Rc::from(bytes))),
        ImageConstant::Inline(constant) => inline_constant_value(constant),
    }
}

fn inline_constant_value(c: &Constant) -> Result<Value, RuntimeError> {
    Ok(match c {
        Constant::Unit => Value::Unit,
        Constant::U8(x) => Value::U64(u64::from(*x)),
        Constant::U16(x) => Value::U64(u64::from(*x)),
        Constant::U32(x) => Value::U64(u64::from(*x)),
        Constant::U64(x) => Value::U64(*x),
        Constant::U128(x) => Value::U128(*x),
        Constant::I8(x) => Value::I64(i64::from(*x)),
        Constant::I16(x) => Value::I64(i64::from(*x)),
        Constant::I32(x) => Value::I64(i64::from(*x)),
        Constant::I64(x) => Value::I64(*x),
        Constant::I128(x) => Value::I128(*x),
        Constant::Usize(x) => Value::U64(*x),
        Constant::Isize(x) => Value::I64(*x),
        Constant::F32(x) => Value::F32(*x),
        Constant::F64(x) => Value::F64(*x),
        Constant::Char(x) => Value::U64(u64::from(*x as u32)),
        Constant::Text(x) => Value::Text(Rc::from(x.as_str())),
        Constant::Bytes(x) => Value::Bytes(Rc::from(x.as_slice())),
    })
}
fn constant_eq(v: &Value, c: ImageConstant<'_>) -> bool {
    match c {
        ImageConstant::Text(text) => matches!(v, Value::Text(value) if value.as_ref() == text),
        ImageConstant::Bytes(bytes) => matches!(v, Value::Bytes(value) if value.as_ref() == bytes),
        ImageConstant::Inline(constant) => inline_constant_eq(v, constant),
    }
}

fn inline_constant_eq(v: &Value, c: &Constant) -> bool {
    match (v, c) {
        (Value::Unit, Constant::Unit) => true,
        (Value::U64(x), Constant::U8(y)) => *x == u64::from(*y),
        (Value::U64(x), Constant::U16(y)) => *x == u64::from(*y),
        (Value::U64(x), Constant::U32(y)) => *x == u64::from(*y),
        (Value::U64(x), Constant::U64(y)) => x == y,
        (Value::U128(x), Constant::U128(y)) => x == y,
        (Value::I64(x), Constant::I8(y)) => *x == i64::from(*y),
        (Value::I64(x), Constant::I16(y)) => *x == i64::from(*y),
        (Value::I64(x), Constant::I32(y)) => *x == i64::from(*y),
        (Value::I64(x), Constant::I64(y)) => x == y,
        (Value::I128(x), Constant::I128(y)) => x == y,
        (Value::U64(x), Constant::Usize(y)) => x == y,
        (Value::I64(x), Constant::Isize(y)) => x == y,
        (Value::F32(x), Constant::F32(y)) => x.to_bits() == y.to_bits(),
        (Value::F64(x), Constant::F64(y)) => x.to_bits() == y.to_bits(),
        (Value::U64(x), Constant::Char(y)) => *x == u64::from(*y as u32),
        (Value::Text(x), Constant::Text(y)) => x.as_ref() == y,
        (Value::Bytes(x), Constant::Bytes(y)) => x.as_ref() == y,
        _ => false,
    }
}
fn value_matches(a: &ExecutionImage, v: &Value, ty: TypeId) -> bool {
    let Some(ty_descriptor) = a.checked_type(ty) else {
        return false;
    };
    match (ty_descriptor.representation(), v) {
        (Type::Unit, Value::Unit)
        | (Type::I64 | Type::Isize, Value::I64(_))
        | (Type::I128, Value::I128(_))
        | (Type::U64 | Type::Usize, Value::U64(_))
        | (Type::U128, Value::U128(_))
        | (Type::F32, Value::F32(_))
        | (Type::F64, Value::F64(_))
        | (Type::Text, Value::Text(_))
        | (Type::Bytes, Value::Bytes(_)) => true,
        (Type::I8, Value::I64(value)) => i8::try_from(*value).is_ok(),
        (Type::I16, Value::I64(value)) => i16::try_from(*value).is_ok(),
        (Type::I32, Value::I64(value)) => i32::try_from(*value).is_ok(),
        (Type::U8, Value::U64(value)) => u8::try_from(*value).is_ok(),
        (Type::U16, Value::U64(value)) => u16::try_from(*value).is_ok(),
        (Type::U32, Value::U64(value)) => u32::try_from(*value).is_ok(),
        (Type::Char, Value::U64(value)) => u32::try_from(*value)
            .ok()
            .and_then(char::from_u32)
            .is_some(),
        (Type::Array { element }, Value::Array(array)) => {
            let array = array.borrow();
            array.element_type == *element
                && array.logical_capacity >= array.slots.len()
                && array.slots.iter().all(|slot| {
                    slot.as_ref()
                        .is_none_or(|value| value_matches(a, value, *element))
                })
        }
        (
            Type::RefShared { referent },
            Value::Reference {
                referent_type,
                unique: false,
                ..
            },
        )
        | (
            Type::RefUnique { referent },
            Value::Reference {
                referent_type,
                unique: true,
                ..
            },
        ) => referent == referent_type,
        (
            Type::Tuple { .. } | Type::Struct { .. } | Type::Enum { .. } | Type::BindingPack { .. },
            Value::Aggregate(aggregate),
        ) => {
            let aggregate = aggregate.borrow();
            let layout_type = match ty_descriptor.representation() {
                Type::BindingPack { payload_type, .. } => *payload_type,
                _ => ty,
            };
            let Ok(fields) = runtime_field_types(a, layout_type, aggregate.variant) else {
                return false;
            };
            aggregate.ty == ty
                && fields.len() == aggregate.fields.len()
                && fields
                    .iter()
                    .zip(&aggregate.fields)
                    .all(|(&field_ty, value)| {
                        value
                            .as_ref()
                            .is_some_and(|value| value_matches(a, value, field_ty))
                    })
        }
        (Type::Callable { .. }, Value::Callable(callable)) => {
            callable.callable_type() == ty
                && a.functions.get(callable.function() as usize).is_some()
                && callable.capture().borrow().is_some()
        }
        (Type::Handler { handler_def, .. }, Value::Handler(handler)) => {
            let handler = handler.borrow();
            handler.handler_type == ty
                && handler.handler_def == *handler_def
                && handler.clauses.iter().all(Option::is_some)
        }
        (Type::Resumption { .. }, Value::Resumption(resumption)) => resumption
            .borrow()
            .as_ref()
            .is_some_and(|resumption| resumption.resumption_type == ty),
        _ => false,
    }
}

fn release_aggregate_shell(value: Value) -> Result<(), RuntimeError> {
    let Value::Aggregate(aggregate) = value else {
        return Err(RuntimeError::TypeConfusion);
    };
    if aggregate.borrow().fields.iter().any(Option::is_some) {
        return Err(RuntimeError::TypeConfusion);
    }
    Ok(())
}

fn aggregate_place(
    value: &Value,
    require_unique: bool,
) -> Result<ArenaObject<AggregateValue>, RuntimeError> {
    match value {
        Value::Aggregate(aggregate) => Ok(aggregate.clone()),
        Value::Reference {
            unique,
            target: ReferenceTarget::Aggregate(aggregate),
            ..
        } if !require_unique || *unique => Ok(aggregate.clone()),
        Value::Reference {
            unique,
            target: ReferenceTarget::AggregateField { aggregate, field },
            ..
        } if !require_unique || *unique => {
            let aggregate = aggregate.borrow();
            match aggregate.fields.get(*field).and_then(Option::as_ref) {
                Some(Value::Aggregate(nested)) => Ok(nested.clone()),
                _ => Err(RuntimeError::TypeConfusion),
            }
        }
        Value::Reference {
            unique,
            target: ReferenceTarget::ArrayElement { array, index },
            ..
        } if !require_unique || *unique => {
            let array = array.borrow();
            match array.slots.get(*index).and_then(Option::as_ref) {
                Some(Value::Aggregate(aggregate)) => Ok(aggregate.clone()),
                _ => Err(RuntimeError::TypeConfusion),
            }
        }
        Value::Reference {
            unique,
            target: ReferenceTarget::CallableCapture(capture),
            ..
        } if !require_unique || *unique => {
            let capture = capture.borrow();
            match capture.as_ref() {
                Some(Value::Aggregate(aggregate)) => Ok(aggregate.clone()),
                _ => Err(RuntimeError::TypeConfusion),
            }
        }
        Value::Reference {
            unique,
            target: ReferenceTarget::DropSlot(slot),
            ..
        } if !require_unique || *unique => {
            match slot.get().map_err(|_| RuntimeError::TypeConfusion)? {
                Value::Aggregate(aggregate) => Ok(aggregate),
                _ => Err(RuntimeError::TypeConfusion),
            }
        }
        Value::Reference {
            unique,
            target: ReferenceTarget::WholePlace(slot),
            ..
        } if !require_unique || *unique => {
            match slot.get().map_err(|_| RuntimeError::TypeConfusion)? {
                Value::Aggregate(aggregate) => Ok(aggregate),
                _ => Err(RuntimeError::TypeConfusion),
            }
        }
        _ => Err(RuntimeError::TypeConfusion),
    }
}

fn runtime_field_types(
    a: &ExecutionImage,
    ty: TypeId,
    variant: Option<u32>,
) -> Result<Vec<TypeId>, RuntimeError> {
    crate::bytecode::construction_field_types(
        a.checked_type(ty).ok_or(RuntimeError::TypeConfusion)?,
        variant,
    )
    .ok_or(RuntimeError::TypeConfusion)?
    .into_iter()
    .filter_map(
        |field| match a.checked_type(field).map(Type::representation) {
            Some(Type::Available { .. }) => None,
            Some(_) => Some(Ok(field)),
            None => Some(Err(RuntimeError::TypeConfusion)),
        },
    )
    .collect()
}

fn runtime_field_index(
    a: &ExecutionImage,
    aggregate: &AggregateValue,
    nominal_field: u32,
) -> Result<usize, RuntimeError> {
    let fields = crate::bytecode::construction_field_types(
        a.checked_type(aggregate.ty)
            .ok_or(RuntimeError::TypeConfusion)?,
        aggregate.variant,
    )
    .ok_or(RuntimeError::TypeConfusion)?;
    let nominal_field = nominal_field as usize;
    let field_type = *fields
        .get(nominal_field)
        .ok_or(RuntimeError::TypeConfusion)?;
    if matches!(
        a.checked_type(field_type).map(Type::representation),
        Some(Type::Available { .. })
    ) {
        return Err(RuntimeError::TypeConfusion);
    }
    fields[..nominal_field]
        .iter()
        .try_fold(0usize, |runtime_index, &field| {
            match a.checked_type(field).map(Type::representation) {
                Some(Type::Available { .. }) => Ok(runtime_index),
                Some(_) => Ok(runtime_index + 1),
                None => Err(RuntimeError::TypeConfusion),
            }
        })
}

fn primitive_typed(
    a: &ExecutionImage,
    result_type: TypeId,
    op: Primitive,
    arg_types: &[TypeId],
    v: &[Value],
) -> Result<Value, RuntimeError> {
    match op {
        Primitive::IntCheckedAdd
        | Primitive::IntCheckedSub
        | Primitive::IntCheckedMul
        | Primitive::IntCheckedDiv
        | Primitive::IntCheckedRem
        | Primitive::IntWrappingAdd
        | Primitive::IntWrappingSub
        | Primitive::IntWrappingMul
        | Primitive::IntBitAnd
        | Primitive::IntBitOr
        | Primitive::IntBitXor
        | Primitive::IntBitNot
        | Primitive::IntShl
        | Primitive::IntShr
        | Primitive::IntEq
        | Primitive::IntNe
        | Primitive::IntLt
        | Primitive::IntLe
        | Primitive::IntGt
        | Primitive::IntGe
        | Primitive::IntConvertChecked
        | Primitive::IntConvertWrapping
        | Primitive::IntCheckedNeg
        | Primitive::IntWrappingNeg => int_primitive(result_type, op, arg_types, v),
        Primitive::FloatAdd
        | Primitive::FloatSub
        | Primitive::FloatMul
        | Primitive::FloatDiv
        | Primitive::FloatRem
        | Primitive::FloatEq
        | Primitive::FloatNe
        | Primitive::FloatLt
        | Primitive::FloatLe
        | Primitive::FloatGt
        | Primitive::FloatGe
        | Primitive::FloatConvert
        | Primitive::FloatNeg
        | Primitive::IntToFloat
        | Primitive::FloatToIntChecked
        | Primitive::FloatToBits
        | Primitive::FloatFromBits => float_primitive(result_type, op, arg_types, v),
        Primitive::CharFromU32Checked => match v {
            [Value::U64(value)] => u32::try_from(*value)
                .ok()
                .and_then(char::from_u32)
                .map(|character| Value::U64(character as u32 as u64))
                .ok_or(RuntimeError::InvalidCharacter),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::CharToU32 => match v {
            [Value::U64(value)] => Ok(Value::U64(*value)),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::TextByteLen => match v {
            [Value::Text(x)] => Ok(Value::U64(x.len() as u64)),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::TextConcat => match v {
            [Value::Text(a), Value::Text(b)] => {
                let length = checked_output_len(a.len(), b.len())?;
                let mut result = String::new();
                reserve_string_output(&mut result, length)?;
                result.push_str(a);
                result.push_str(b);
                Ok(Value::Text(result.into()))
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::TextEq => match v {
            [Value::Text(a), Value::Text(b)] => Ok(bool_value(a == b)),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::TextFromUtf8Checked => match v {
            [Value::Bytes(x)] => String::from_utf8(clone_output(x)?)
                .map(|value| Value::Text(value.into()))
                .map_err(|_| RuntimeError::InvalidUtf8),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::TextAsBytes => match v {
            [Value::Text(x)] => Ok(Value::Bytes(clone_output(x.as_bytes())?.into())),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::BytesLen => match v {
            [Value::Bytes(x)] => Ok(Value::U64(x.len() as u64)),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::BytesUtf8ValidUpTo => match v {
            [Value::Bytes(bytes)] => Ok(Value::U64(
                std::str::from_utf8(bytes).map_or_else(|error| error.valid_up_to(), |_| bytes.len())
                    as u64,
            )),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::BytesConcat => match v {
            [Value::Bytes(a), Value::Bytes(b)] => {
                let length = checked_output_len(a.len(), b.len())?;
                let mut result = Vec::new();
                reserve_output(&mut result, length)?;
                result.extend_from_slice(a);
                result.extend_from_slice(b);
                Ok(Value::Bytes(result.into()))
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::BytesGet => match v {
            [Value::Bytes(bytes), Value::U64(index)] => bytes
                .get(to_index(*index)?)
                .copied()
                .map(|x| Value::U64(x as u64))
                .ok_or(RuntimeError::IndexOutOfBounds),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::BytesSlice => match v {
            [Value::Bytes(bytes), Value::U64(start), Value::U64(end)] => bytes
                .get(to_index(*start)?..to_index(*end)?)
                .map(clone_output)
                .transpose()?
                .map(|value| Value::Bytes(value.into()))
                .ok_or(RuntimeError::IndexOutOfBounds),
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::BytesFromArrayMove => match v {
            [Value::Array(array)] => {
                let array = array.borrow();
                let mut bytes = Vec::new();
                reserve_output(&mut bytes, array.slots.len())?;
                for slot in &array.slots {
                    match slot {
                        Some(Value::U64(byte)) if u8::try_from(*byte).is_ok() => {
                            bytes.push(*byte as u8)
                        }
                        None => return Err(RuntimeError::EmptyArraySlot),
                        _ => return Err(RuntimeError::TypeConfusion),
                    }
                }
                Ok(Value::Bytes(bytes.into()))
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::BytesToArray => match v {
            [Value::Bytes(bytes)] => {
                let element_type = array_element_type(a, result_type)?;
                let mut slots = Vec::new();
                reserve_output(&mut slots, bytes.len())?;
                slots.extend(bytes.iter().map(|byte| Some(Value::U64(u64::from(*byte)))));
                Ok(Value::Array(ArenaObject::new_tracked(ArrayValue {
                    element_type,
                    logical_capacity: slots.len(),
                    slots,
                })))
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::ArrayNew => match v {
            [Value::U64(length), fill] => {
                let length = to_index(*length)?;
                let element_type = array_element_type(a, result_type)?;
                let mut slots = Vec::new();
                reserve_output(&mut slots, length)?;
                for _ in 0..length {
                    slots.push(Some(copy_value(a, element_type, fill)?));
                }
                Ok(Value::Array(ArenaObject::new_tracked(ArrayValue {
                    element_type,
                    slots,
                    logical_capacity: length,
                })))
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::ArrayEmpty => Ok(Value::array(
            array_element_type(a, result_type)?,
            std::iter::empty(),
        )),
        Primitive::ArrayLen => {
            let array = referenced_array(v, false)?;
            let length = array.borrow().slots.len();
            Ok(Value::U64(length as u64))
        }
        Primitive::ArrayCapacity => {
            let array = referenced_array(v, false)?;
            let capacity = array.borrow().logical_capacity;
            Ok(Value::U64(capacity as u64))
        }
        Primitive::ArrayGetCopy => match v {
            [reference, Value::U64(index)] => {
                let array = reference_array(reference, false)?;
                let index = to_index(*index)?;
                let array = array.borrow();
                let value = array
                    .slots
                    .get(index)
                    .ok_or(RuntimeError::IndexOutOfBounds)?
                    .as_ref()
                    .ok_or(RuntimeError::EmptyArraySlot)?;
                copy_value(a, array.element_type, value)
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::ArrayGetMove => match v {
            [reference, Value::U64(index)] => {
                let array = reference_array(reference, true)?;
                let index = to_index(*index)?;
                array
                    .borrow_mut()
                    .slots
                    .get_mut(index)
                    .ok_or(RuntimeError::IndexOutOfBounds)?
                    .take()
                    .ok_or(RuntimeError::EmptyArraySlot)
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::ArrayGetBorrowShared | Primitive::ArrayGetBorrowUnique => match v {
            [reference, Value::U64(index)] => {
                let unique = op == Primitive::ArrayGetBorrowUnique;
                let array = reference_array(reference, unique)?;
                let index = to_index(*index)?;
                if array
                    .borrow()
                    .slots
                    .get(index)
                    .ok_or(RuntimeError::IndexOutOfBounds)?
                    .is_none()
                {
                    return Err(RuntimeError::EmptyArraySlot);
                }
                let referent_type = match a.checked_type(result_type).map(Type::representation) {
                    Some(Type::RefShared { referent }) if !unique => *referent,
                    Some(Type::RefUnique { referent }) if unique => *referent,
                    _ => return Err(RuntimeError::TypeConfusion),
                };
                Ok(Value::Reference {
                    referent_type,
                    unique,
                    target: ReferenceTarget::ArrayElement { array, index },
                })
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::ArraySetMove => match v {
            [reference, Value::U64(index), value] => {
                let array = reference_array(reference, true)?;
                let index = to_index(*index)?;
                let mut array = array.borrow_mut();
                let slot = array
                    .slots
                    .get_mut(index)
                    .ok_or(RuntimeError::IndexOutOfBounds)?;
                if slot.is_some() {
                    return Err(RuntimeError::ArraySlotAlreadyInitialized);
                }
                *slot = Some(value.clone());
                Ok(Value::Unit)
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::ArrayPushMove => match v {
            [reference, value] => {
                let array = reference_array(reference, true)?;
                let mut array = array.borrow_mut();
                let required = array
                    .slots
                    .len()
                    .checked_add(1)
                    .ok_or(RuntimeError::AllocationOverflow)?;
                grow_array(&mut array, required)?;
                array.slots.push(Some(value.clone()));
                Ok(Value::Unit)
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::ArrayPopMove => {
            let array = referenced_array(v, true)?;
            array
                .borrow_mut()
                .slots
                .pop()
                .ok_or(RuntimeError::IndexOutOfBounds)?
                .ok_or(RuntimeError::EmptyArraySlot)
        }
        Primitive::ArrayReserve => match v {
            [reference, Value::U64(additional)] => {
                let array = reference_array(reference, true)?;
                let mut array = array.borrow_mut();
                let required = array
                    .slots
                    .len()
                    .checked_add(to_index(*additional)?)
                    .ok_or(RuntimeError::AllocationOverflow)?;
                grow_array(&mut array, required)?;
                Ok(Value::Unit)
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
        Primitive::ArrayFinishDrained => match v {
            [Value::Array(array)] => {
                if array.borrow().slots.iter().any(Option::is_some) {
                    Err(RuntimeError::ArrayNotDrained)
                } else {
                    Ok(Value::Unit)
                }
            }
            _ => Err(RuntimeError::TypeConfusion),
        },
    }
}

#[cfg(test)]
fn primitive(
    a: &ExecutionImage,
    result_type: TypeId,
    op: Primitive,
    values: &[Value],
) -> Result<Value, RuntimeError> {
    let arg_types = values
        .iter()
        .map(|value| match value {
            Value::I64(_) => I64,
            Value::I128(_) => I128,
            Value::U64(_) => U64,
            Value::U128(_) => U128,
            Value::F32(_) => F32,
            Value::F64(_) => F64,
            _ => UNIT,
        })
        .collect::<Vec<_>>();
    primitive_typed(a, result_type, op, &arg_types, values)
}

fn array_element_type(a: &ExecutionImage, array_type: TypeId) -> Result<TypeId, RuntimeError> {
    match a.checked_type(array_type).map(Type::representation) {
        Some(Type::Array { element }) => Ok(*element),
        _ => Err(RuntimeError::TypeConfusion),
    }
}

fn reference_array(
    value: &Value,
    require_unique: bool,
) -> Result<ArenaObject<ArrayValue>, RuntimeError> {
    match value {
        Value::Reference {
            unique,
            target: ReferenceTarget::Array(array),
            ..
        } if !require_unique || *unique => Ok(array.clone()),
        Value::Reference {
            unique,
            target: ReferenceTarget::DropSlot(slot),
            ..
        } if !require_unique || *unique => {
            match slot.get().map_err(|_| RuntimeError::TypeConfusion)? {
                Value::Array(array) => Ok(array),
                _ => Err(RuntimeError::TypeConfusion),
            }
        }
        Value::Reference {
            unique,
            target: ReferenceTarget::WholePlace(slot),
            ..
        } if !require_unique || *unique => {
            match slot.get().map_err(|_| RuntimeError::TypeConfusion)? {
                Value::Array(array) => Ok(array),
                _ => Err(RuntimeError::TypeConfusion),
            }
        }
        Value::Reference {
            unique,
            target: ReferenceTarget::AggregateField { aggregate, field },
            ..
        } if !require_unique || *unique => {
            let aggregate = aggregate.borrow();
            match aggregate.fields.get(*field).and_then(Option::as_ref) {
                Some(Value::Array(array)) => Ok(array.clone()),
                _ => Err(RuntimeError::TypeConfusion),
            }
        }
        _ => Err(RuntimeError::TypeConfusion),
    }
}

fn referenced_array(
    values: &[Value],
    require_unique: bool,
) -> Result<ArenaObject<ArrayValue>, RuntimeError> {
    match values {
        [reference] => reference_array(reference, require_unique),
        _ => Err(RuntimeError::TypeConfusion),
    }
}

fn grow_array(array: &mut ArrayValue, required: usize) -> Result<(), RuntimeError> {
    checked_output_bytes::<Option<Value>>(required)?;
    if required > array.logical_capacity {
        let capacity = required
            .max(4)
            .checked_next_power_of_two()
            .ok_or(RuntimeError::AllocationOverflow)?;
        checked_output_bytes::<Option<Value>>(capacity)?;
        if capacity > array.slots.capacity() {
            array
                .slots
                .try_reserve_exact(capacity.saturating_sub(array.slots.len()))
                .map_err(|_| RuntimeError::AllocationLimit)?;
        }
        array.logical_capacity = capacity;
    } else if required > array.slots.capacity() {
        array
            .slots
            .try_reserve_exact(required.saturating_sub(array.slots.len()))
            .map_err(|_| RuntimeError::AllocationLimit)?;
    }
    Ok(())
}

fn bool_value(value: bool) -> Value {
    Value::U64(u64::from(value))
}

fn to_index(value: u64) -> Result<usize, RuntimeError> {
    usize::try_from(value).map_err(|_| RuntimeError::IndexOutOfBounds)
}

// Primitive results are bounded independently of the native allocator so a
// small artifact cannot turn allocation amplification into a process abort.
pub const MAX_PRIMITIVE_ALLOCATION_BYTES: usize = 16 * 1024 * 1024 * 1024;

fn checked_output_bytes<T>(count: usize) -> Result<(), RuntimeError> {
    let bytes = count
        .checked_mul(std::mem::size_of::<T>().max(1))
        .ok_or(RuntimeError::AllocationOverflow)?;
    if bytes > isize::MAX as usize {
        Err(RuntimeError::AllocationOverflow)
    } else if bytes > MAX_PRIMITIVE_ALLOCATION_BYTES {
        Err(RuntimeError::AllocationLimit)
    } else {
        Ok(())
    }
}

fn checked_output_len(left: usize, right: usize) -> Result<usize, RuntimeError> {
    let length = left
        .checked_add(right)
        .ok_or(RuntimeError::AllocationOverflow)?;
    checked_output_bytes::<u8>(length)?;
    Ok(length)
}

fn reserve_output<T>(values: &mut Vec<T>, count: usize) -> Result<(), RuntimeError> {
    checked_output_bytes::<T>(count)?;
    values
        .try_reserve_exact(count)
        .map_err(|_| RuntimeError::AllocationLimit)
}

fn reserve_string_output(value: &mut String, count: usize) -> Result<(), RuntimeError> {
    checked_output_bytes::<u8>(count)?;
    value
        .try_reserve_exact(count)
        .map_err(|_| RuntimeError::AllocationLimit)
}

fn clone_output<T: Clone>(values: &[T]) -> Result<Vec<T>, RuntimeError> {
    let mut result = Vec::new();
    reserve_output(&mut result, values.len())?;
    result.extend_from_slice(values);
    Ok(result)
}

fn canonical_f64(value: f64) -> f64 {
    if value.is_nan() {
        f64::from_bits(0x7ff8_0000_0000_0000)
    } else {
        value
    }
}

fn canonical_f32(value: f32) -> f32 {
    if value.is_nan() {
        f32::from_bits(0x7fc0_0000)
    } else {
        value
    }
}

#[derive(Clone, Copy)]
struct IntSpec {
    signed: bool,
    bits: u32,
}

fn int_spec(ty: TypeId) -> Option<IntSpec> {
    Some(match ty {
        U8 => IntSpec {
            signed: false,
            bits: 8,
        },
        U16 => IntSpec {
            signed: false,
            bits: 16,
        },
        U32 => IntSpec {
            signed: false,
            bits: 32,
        },
        U64 | USIZE => IntSpec {
            signed: false,
            bits: 64,
        },
        U128 => IntSpec {
            signed: false,
            bits: 128,
        },
        I8 => IntSpec {
            signed: true,
            bits: 8,
        },
        I16 => IntSpec {
            signed: true,
            bits: 16,
        },
        I32 => IntSpec {
            signed: true,
            bits: 32,
        },
        I64 | ISIZE => IntSpec {
            signed: true,
            bits: 64,
        },
        I128 => IntSpec {
            signed: true,
            bits: 128,
        },
        _ => return None,
    })
}

fn int_mask(bits: u32) -> u128 {
    if bits == 128 {
        u128::MAX
    } else {
        (1_u128 << bits) - 1
    }
}

fn int_raw(spec: IntSpec, value: &Value) -> Result<u128, RuntimeError> {
    let raw = match (spec.signed, spec.bits, value) {
        (false, 128, Value::U128(value)) => *value,
        (false, _, Value::U64(value)) => u128::from(*value),
        (true, 128, Value::I128(value)) => *value as u128,
        (true, _, Value::I64(value)) => *value as u128,
        _ => return Err(RuntimeError::TypeConfusion),
    };
    Ok(raw & int_mask(spec.bits))
}

fn int_signed(spec: IntSpec, value: &Value) -> Result<i128, RuntimeError> {
    let raw = int_raw(spec, value)?;
    Ok(if spec.bits == 128 {
        raw as i128
    } else {
        ((raw << (128 - spec.bits)) as i128) >> (128 - spec.bits)
    })
}

fn make_int(spec: IntSpec, raw: u128) -> Value {
    let raw = raw & int_mask(spec.bits);
    match (spec.signed, spec.bits) {
        (false, 128) => Value::U128(raw),
        (false, _) => Value::U64(raw as u64),
        (true, 128) => Value::I128(raw as i128),
        (true, _) => Value::I64((((raw << (128 - spec.bits)) as i128) >> (128 - spec.bits)) as i64),
    }
}

fn signed_bounds(bits: u32) -> (i128, i128) {
    if bits == 128 {
        (i128::MIN, i128::MAX)
    } else {
        let limit = 1_i128 << (bits - 1);
        (-limit, limit - 1)
    }
}

fn make_checked_signed(spec: IntSpec, value: Option<i128>) -> Result<Value, RuntimeError> {
    let value = value.ok_or(RuntimeError::ArithmeticOverflow)?;
    let (min, max) = signed_bounds(spec.bits);
    if value < min || value > max {
        Err(RuntimeError::ArithmeticOverflow)
    } else {
        Ok(make_int(spec, value as u128))
    }
}

fn make_checked_unsigned(spec: IntSpec, value: Option<u128>) -> Result<Value, RuntimeError> {
    let value = value.ok_or(RuntimeError::ArithmeticOverflow)?;
    if value > int_mask(spec.bits) {
        Err(RuntimeError::ArithmeticOverflow)
    } else {
        Ok(make_int(spec, value))
    }
}

fn int_primitive(
    result_type: TypeId,
    op: Primitive,
    arg_types: &[TypeId],
    values: &[Value],
) -> Result<Value, RuntimeError> {
    let source = int_spec(*arg_types.first().ok_or(RuntimeError::TypeConfusion)?)
        .ok_or(RuntimeError::TypeConfusion)?;
    let unary = || values.first().ok_or(RuntimeError::TypeConfusion);
    let binary = || match values {
        [a, b] => Ok((a, b)),
        _ => Err(RuntimeError::TypeConfusion),
    };
    use Primitive::*;
    match op {
        IntConvertChecked | IntConvertWrapping => {
            let target = int_spec(result_type).ok_or(RuntimeError::TypeConfusion)?;
            if op == IntConvertWrapping {
                let raw = if source.signed {
                    int_signed(source, unary()?)? as u128
                } else {
                    int_raw(source, unary()?)?
                };
                return Ok(make_int(target, raw));
            }
            if source.signed {
                let value = int_signed(source, unary()?)?;
                if target.signed {
                    make_checked_signed(target, Some(value))
                } else if value < 0 {
                    Err(RuntimeError::ArithmeticOverflow)
                } else {
                    make_checked_unsigned(target, Some(value as u128))
                }
            } else {
                let value = int_raw(source, unary()?)?;
                if target.signed {
                    if value > signed_bounds(target.bits).1 as u128 {
                        Err(RuntimeError::ArithmeticOverflow)
                    } else {
                        Ok(make_int(target, value))
                    }
                } else {
                    make_checked_unsigned(target, Some(value))
                }
            }
        }
        IntEq | IntNe | IntLt | IntLe | IntGt | IntGe => {
            let (a, b) = binary()?;
            let result = if source.signed {
                let (a, b) = (int_signed(source, a)?, int_signed(source, b)?);
                match op {
                    IntEq => a == b,
                    IntNe => a != b,
                    IntLt => a < b,
                    IntLe => a <= b,
                    IntGt => a > b,
                    IntGe => a >= b,
                    _ => unreachable!(),
                }
            } else {
                let (a, b) = (int_raw(source, a)?, int_raw(source, b)?);
                match op {
                    IntEq => a == b,
                    IntNe => a != b,
                    IntLt => a < b,
                    IntLe => a <= b,
                    IntGt => a > b,
                    IntGe => a >= b,
                    _ => unreachable!(),
                }
            };
            Ok(bool_value(result))
        }
        IntBitNot => Ok(make_int(source, !int_raw(source, unary()?)?)),
        IntCheckedNeg => {
            if source.signed {
                make_checked_signed(source, int_signed(source, unary()?)?.checked_neg())
            } else if int_raw(source, unary()?)? == 0 {
                Ok(make_int(source, 0))
            } else {
                Err(RuntimeError::ArithmeticOverflow)
            }
        }
        IntWrappingNeg => Ok(make_int(source, int_raw(source, unary()?)?.wrapping_neg())),
        IntShl | IntShr => {
            let (value, count) = binary()?;
            let Value::U64(count) = count else {
                return Err(RuntimeError::TypeConfusion);
            };
            let count = u32::try_from(*count)
                .ok()
                .filter(|count| *count < source.bits)
                .ok_or(RuntimeError::InvalidShiftCount)?;
            if op == IntShl {
                Ok(make_int(source, int_raw(source, value)? << count))
            } else if source.signed {
                Ok(make_int(
                    source,
                    (int_signed(source, value)? >> count) as u128,
                ))
            } else {
                Ok(make_int(source, int_raw(source, value)? >> count))
            }
        }
        IntCheckedAdd | IntCheckedSub | IntCheckedMul | IntCheckedDiv | IntCheckedRem => {
            let (a, b) = binary()?;
            if source.signed {
                let (a, b) = (int_signed(source, a)?, int_signed(source, b)?);
                if matches!(op, IntCheckedDiv | IntCheckedRem) && b == 0 {
                    return Err(RuntimeError::DivisionByZero);
                }
                if matches!(op, IntCheckedDiv | IntCheckedRem)
                    && a == signed_bounds(source.bits).0
                    && b == -1
                {
                    return Err(RuntimeError::ArithmeticOverflow);
                }
                let value = match op {
                    IntCheckedAdd => a.checked_add(b),
                    IntCheckedSub => a.checked_sub(b),
                    IntCheckedMul => a.checked_mul(b),
                    IntCheckedDiv => a.checked_div(b),
                    IntCheckedRem => a.checked_rem(b),
                    _ => unreachable!(),
                };
                make_checked_signed(source, value)
            } else {
                let (a, b) = (int_raw(source, a)?, int_raw(source, b)?);
                if matches!(op, IntCheckedDiv | IntCheckedRem) && b == 0 {
                    return Err(RuntimeError::DivisionByZero);
                }
                let value = match op {
                    IntCheckedAdd => a.checked_add(b),
                    IntCheckedSub => a.checked_sub(b),
                    IntCheckedMul => a.checked_mul(b),
                    IntCheckedDiv => a.checked_div(b),
                    IntCheckedRem => a.checked_rem(b),
                    _ => unreachable!(),
                };
                make_checked_unsigned(source, value)
            }
        }
        IntWrappingAdd | IntWrappingSub | IntWrappingMul | IntBitAnd | IntBitOr | IntBitXor => {
            let (a, b) = binary()?;
            let (a, b) = (int_raw(source, a)?, int_raw(source, b)?);
            let raw = match op {
                IntWrappingAdd => a.wrapping_add(b),
                IntWrappingSub => a.wrapping_sub(b),
                IntWrappingMul => a.wrapping_mul(b),
                IntBitAnd => a & b,
                IntBitOr => a | b,
                IntBitXor => a ^ b,
                _ => unreachable!(),
            };
            Ok(make_int(source, raw))
        }
        _ => Err(RuntimeError::TypeConfusion),
    }
}

fn float_primitive(
    result_type: TypeId,
    op: Primitive,
    arg_types: &[TypeId],
    values: &[Value],
) -> Result<Value, RuntimeError> {
    use Primitive::*;
    let source_type = *arg_types.first().ok_or(RuntimeError::TypeConfusion)?;
    if op == FloatToBits {
        return match (source_type, result_type, values) {
            (F32, U32, [Value::F32(value)]) => {
                Ok(Value::U64(u64::from(canonical_f32(*value).to_bits())))
            }
            (F64, U64, [Value::F64(value)]) => Ok(Value::U64(canonical_f64(*value).to_bits())),
            _ => Err(RuntimeError::TypeConfusion),
        };
    }
    if op == FloatFromBits {
        return match (source_type, result_type, values) {
            (U32, F32, [Value::U64(bits)]) if u32::try_from(*bits).is_ok() => {
                Ok(Value::F32(canonical_f32(f32::from_bits(*bits as u32))))
            }
            (U64, F64, [Value::U64(bits)]) => Ok(Value::F64(canonical_f64(f64::from_bits(*bits)))),
            _ => Err(RuntimeError::TypeConfusion),
        };
    }
    if op == IntToFloat {
        let spec = int_spec(source_type).ok_or(RuntimeError::TypeConfusion)?;
        let value = values.first().ok_or(RuntimeError::TypeConfusion)?;
        return match (result_type, spec.signed) {
            (F32, true) => Ok(Value::F32(canonical_f32(int_signed(spec, value)? as f32))),
            (F32, false) => Ok(Value::F32(canonical_f32(int_raw(spec, value)? as f32))),
            (F64, true) => Ok(Value::F64(canonical_f64(int_signed(spec, value)? as f64))),
            (F64, false) => Ok(Value::F64(canonical_f64(int_raw(spec, value)? as f64))),
            _ => Err(RuntimeError::TypeConfusion),
        };
    }
    let as_f64 = |value: &Value| match value {
        Value::F32(x) => Ok(f64::from(*x)),
        Value::F64(x) => Ok(*x),
        _ => Err(RuntimeError::TypeConfusion),
    };
    if op == FloatConvert {
        let value = as_f64(values.first().ok_or(RuntimeError::TypeConfusion)?)?;
        return match result_type {
            F32 => Ok(Value::F32(canonical_f32(value as f32))),
            F64 => Ok(Value::F64(canonical_f64(value))),
            _ => Err(RuntimeError::TypeConfusion),
        };
    }
    if op == FloatToIntChecked {
        let value = as_f64(values.first().ok_or(RuntimeError::TypeConfusion)?)?;
        let target = int_spec(result_type).ok_or(RuntimeError::TypeConfusion)?;
        if !value.is_finite() {
            return Err(RuntimeError::ArithmeticOverflow);
        }
        if target.signed {
            let limit = 2_f64.powi((target.bits - 1) as i32);
            if value < -limit || value >= limit {
                return Err(RuntimeError::ArithmeticOverflow);
            }
            return Ok(make_int(target, (value.trunc() as i128) as u128));
        }
        let limit = 2_f64.powi(target.bits as i32);
        if value < 0.0 || value >= limit {
            return Err(RuntimeError::ArithmeticOverflow);
        }
        return Ok(make_int(target, value.trunc() as u128));
    }
    let comparison = matches!(
        op,
        FloatEq | FloatNe | FloatLt | FloatLe | FloatGt | FloatGe
    );
    match source_type {
        F32 => {
            let one = |value: &Value| match value {
                Value::F32(x) => Ok(*x),
                _ => Err(RuntimeError::TypeConfusion),
            };
            if op == FloatNeg {
                return Ok(Value::F32(canonical_f32(-one(values
                    .first()
                    .ok_or(RuntimeError::TypeConfusion)?)?)));
            }
            let [a, b] = values else {
                return Err(RuntimeError::TypeConfusion);
            };
            let (a, b) = (one(a)?, one(b)?);
            if comparison {
                Ok(bool_value(match op {
                    FloatEq => a == b,
                    FloatNe => a != b,
                    FloatLt => a < b,
                    FloatLe => a <= b,
                    FloatGt => a > b,
                    FloatGe => a >= b,
                    _ => unreachable!(),
                }))
            } else {
                Ok(Value::F32(canonical_f32(match op {
                    FloatAdd => a + b,
                    FloatSub => a - b,
                    FloatMul => a * b,
                    FloatDiv => a / b,
                    FloatRem => a % b,
                    _ => return Err(RuntimeError::TypeConfusion),
                })))
            }
        }
        F64 => {
            let one = |value: &Value| match value {
                Value::F64(x) => Ok(*x),
                _ => Err(RuntimeError::TypeConfusion),
            };
            if op == FloatNeg {
                return Ok(Value::F64(canonical_f64(-one(values
                    .first()
                    .ok_or(RuntimeError::TypeConfusion)?)?)));
            }
            let [a, b] = values else {
                return Err(RuntimeError::TypeConfusion);
            };
            let (a, b) = (one(a)?, one(b)?);
            if comparison {
                Ok(bool_value(match op {
                    FloatEq => a == b,
                    FloatNe => a != b,
                    FloatLt => a < b,
                    FloatLe => a <= b,
                    FloatGt => a > b,
                    FloatGe => a >= b,
                    _ => unreachable!(),
                }))
            } else {
                Ok(Value::F64(canonical_f64(match op {
                    FloatAdd => a + b,
                    FloatSub => a - b,
                    FloatMul => a * b,
                    FloatDiv => a / b,
                    FloatRem => a % b,
                    _ => return Err(RuntimeError::TypeConfusion),
                })))
            }
        }
        _ => Err(RuntimeError::TypeConfusion),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::*;
    fn image(artifact: Artifact) -> ExecutionImage {
        ExecutionImage::from_artifact(artifact)
    }
    fn verify(artifact: Artifact) -> Result<VerifiedArtifact, VerifyError> {
        let artifact = if artifact.cleanups.is_empty() && !artifact.functions.is_empty() {
            crate::verify::with_generated_cleanup_plans(artifact)?
        } else {
            artifact
        };
        crate::verify::verify(artifact)
    }
    fn prim(result: TypeId, op: Primitive, values: &[Value]) -> Result<Value, RuntimeError> {
        primitive(&image(Artifact::default()), result, op, values)
    }

    #[test]
    fn parses_linux_process_memory_status() {
        let status = "Name:\tgrvm\nVmSize:\t  8388608 kB\nVmRSS:\t  7340032 kB\n";
        assert_eq!(
            parse_process_status(status),
            Some(ProcessMemory {
                virtual_kib: 8_388_608,
                rss_kib: 7_340_032,
            })
        );
        assert_eq!(parse_process_status("VmRSS:\t1 kB\n"), None);
    }

    #[test]
    fn extreme_label_namespace_does_not_preallocate_runtime_storage() {
        let artifact = Artifact {
            functions: vec![Function {
                flags: 0,
                name: "sparse_label_namespace".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, UNIT],
                code_start: 0,
                code_len: 3,
                label_slot_count: u32::MAX,
            }],
            code: vec![
                Instruction::LabelPush {
                    slot: u32::MAX - 1,
                    result_register: 1,
                    target: 2,
                },
                Instruction::LabelPop { slot: u32::MAX - 1 },
                Instruction::Return { src: None },
            ],
            required_features: 1 | (1 << 2),
            ..Artifact::default()
        };

        assert_eq!(
            Vm::from_artifact(artifact).unwrap().run(0, vec![]),
            Ok(Value::Unit)
        );
    }

    #[test]
    fn enum_tag_reads_an_enum_through_an_array_element_reference() {
        let Value::Array(array) = Value::array(
            19,
            [Value::aggregate_with_variant(19, Some(2), [Value::Unit])],
        ) else {
            unreachable!();
        };
        assert_eq!(
            reference_target_enum_tag(&ReferenceTarget::ArrayElement { array, index: 0 }).unwrap(),
            2
        );
    }

    #[test]
    fn handler_selection_retains_the_selected_clause_resumption_identity() {
        let mut types = Type::predefined();
        for identity_name in ["first handler resumption", "second handler resumption"] {
            types.push(Type::Resumption {
                input_type: I64,
                output_type: UNIT,
                effect_signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                lower_uses: 1,
                upper_uses: Some(1),
                identity_name: identity_name.into(),
                copy: false,
            });
        }
        let clause = |resumption_type| HandlerClause {
            protocol: 0,
            operation: 0,
            resumption_type: Some(resumption_type),
            callable_signature: Signature {
                params: vec![resumption_type],
                result: UNIT,
                outward_protocols: vec![],
            },
        };
        let artifact = Artifact {
            types,
            protocols: vec![Protocol {
                display_name: "Yield".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "yield".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    resumption_lower: 1,
                    resumption_upper: Some(1),
                    terminal: false,
                }],
            }],
            handler_defs: vec![
                HandlerDef {
                    result_type: UNIT,
                    clauses: vec![clause(19)],
                    partial: false,
                },
                HandlerDef {
                    result_type: UNIT,
                    clauses: vec![clause(20)],
                    partial: false,
                },
                HandlerDef {
                    result_type: UNIT,
                    clauses: vec![],
                    partial: true,
                },
            ],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "clause".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![UNIT],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            }],
            code: vec![Instruction::Return { src: None }],
            ..Artifact::default()
        };
        let callable = Value::Callable(ControlHandle::new(crate::value::CallableValue {
            callable_type: UNIT,
            function: 0,
            capture: ArenaObject::new(Some(Value::Unit)),
        }));
        let handler = Value::Handler(ControlHandle::new(HandlerValue {
            handler_type: UNIT,
            handler_def: 1,
            clauses: vec![Some(callable)],
        }));
        let partial = Value::Handler(ControlHandle::new(HandlerValue {
            handler_type: UNIT,
            handler_def: 2,
            clauses: vec![],
        }));
        let frame = |delimiter| RuntimeFrame {
            function: 0,
            pc: 0,
            registers: vec![Some(Value::Unit)],
            return_dst: None,
            delimiter: Some(delimiter),
            guards: vec![],
            deferred_frames: vec![],
            labels: vec![],
        };
        let mut stack = vec![frame(handler), frame(partial)];
        let selected = select_handler_clause(&image(artifact.clone()), &mut stack, 0, 0).unwrap();
        assert_eq!(selected.delimiter, 0);
        assert_eq!(selected.resumption_type, Some(20));
    }

    #[test]
    fn deconstruct_runtime_releases_only_empty_aggregate_shells() {
        assert_eq!(release_aggregate_shell(Value::aggregate(19, [])), Ok(()));
        assert_eq!(
            release_aggregate_shell(Value::aggregate(19, [Value::I64(1)])),
            Err(RuntimeError::TypeConfusion)
        );
        assert_eq!(
            release_aggregate_shell(Value::I64(1)),
            Err(RuntimeError::TypeConfusion)
        );
    }

    fn nested_drop_artifact(outer_aborts: bool) -> Artifact {
        let mut types = Type::predefined();
        let child = types.len() as TypeId;
        types.push(
            Type::Struct {
                name: "Child".into(),
                fields: vec![],
                copy: false,
            }
            .restricted(false, true),
        );
        let outer = types.len() as TypeId;
        types.push(
            Type::Struct {
                name: "Outer".into(),
                fields: vec![Field {
                    name: "child".into(),
                    ty: child,
                }],
                copy: false,
            }
            .restricted(false, true),
        );
        let child_ref = types.len() as TypeId;
        types.push(Type::RefUnique { referent: child });
        let outer_ref = types.len() as TypeId;
        types.push(Type::RefUnique { referent: outer });

        let outer_code = if outer_aborts {
            vec![Instruction::Abort {
                message: Some("outer".into()),
            }]
        } else {
            vec![
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Return { src: Some(2) },
            ]
        };
        let child_start = 5 + outer_code.len() as u32;
        let mut code = vec![
            Instruction::Construct {
                dst: 1,
                ty: child,
                variant: None,
                fields: vec![],
            },
            Instruction::Construct {
                dst: 2,
                ty: outer,
                variant: None,
                fields: vec![1],
            },
            Instruction::Drop { register: 2 },
            Instruction::Const {
                dst: 3,
                constant: 0,
            },
            Instruction::Return { src: Some(3) },
        ];
        code.extend(outer_code);
        code.push(Instruction::Abort {
            message: Some("child".into()),
        });
        Artifact {
            required_features: 3,
            entry_function: None,
            types,
            constants: vec![Constant::Unit],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![
                DropGlue {
                    ty: child,
                    function: 2,
                },
                DropGlue {
                    ty: outer,
                    function: 1,
                },
            ],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, child, outer, UNIT],
                    code_start: 0,
                    code_len: 5,
                    label_slot_count: 0,
                },
                Function {
                    flags: DROP_HOOK,
                    name: "drop_outer".into(),
                    params: vec![outer_ref],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: if outer_aborts {
                        vec![UNIT, outer_ref]
                    } else {
                        vec![UNIT, outer_ref, UNIT]
                    },
                    code_start: 5,
                    code_len: if outer_aborts { 1 } else { 3 },
                    label_slot_count: 0,
                },
                Function {
                    flags: DROP_HOOK,
                    name: "drop_child".into(),
                    params: vec![child_ref],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, child_ref],
                    code_start: child_start,
                    code_len: 1,
                    label_slot_count: 0,
                },
            ],
            code,
        }
    }

    #[test]
    fn custom_drop_hook_runs_before_child_and_abort_stops_structural_destruction() {
        let vm = Vm::from_artifact(nested_drop_artifact(true)).unwrap();
        assert_eq!(
            vm.run(0, vec![]),
            Err(RuntimeError::Aborted(Some("outer".into())))
        );
    }

    #[test]
    fn returning_custom_drop_hook_is_followed_by_reverse_structural_destruction() {
        let vm = Vm::from_artifact(nested_drop_artifact(false)).unwrap();
        assert_eq!(
            vm.run(0, vec![]),
            Err(RuntimeError::Aborted(Some("child".into())))
        );
    }
    #[test]
    fn executes_call_and_checked_primitive() {
        let a = Artifact {
            types: Type::predefined(),
            constants: vec![Constant::I64(20), Constant::I64(22)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, I64, I64],
                    code_start: 0,
                    code_len: 4,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "add".into(),
                    params: vec![I64, I64],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, I64, I64],
                    code_start: 4,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 1,
                },
                Instruction::Call {
                    dst: Some(3),
                    function: 1,
                    args: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
                Instruction::Primitive {
                    dst: 3,
                    op: Primitive::IntCheckedAdd,
                    args: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1,
            entry_function: None,
        };
        assert_eq!(
            Vm::from_artifact(a).unwrap().run(0, vec![]).unwrap(),
            Value::I64(42)
        );
    }

    #[test]
    fn whole_scalar_place_and_shared_reference_forward_through_direct_call() {
        let mut types = Type::predefined();
        let shared_i64 = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(42)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, shared_i64, shared_i64],
                    code_start: 0,
                    code_len: 5,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "forward_shared".into(),
                    params: vec![shared_i64],
                    return_type: shared_i64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, shared_i64, shared_i64],
                    code_start: 5,
                    code_len: 3,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::Call {
                    dst: Some(3),
                    function: 1,
                    args: vec![2],
                },
                Instruction::EndBorrow { reference: 3 },
                Instruction::Return { src: Some(1) },
                Instruction::ReborrowShared { dst: 2, src: 1 },
                Instruction::EndBorrow { reference: 1 },
                Instruction::Return { src: Some(2) },
            ],
            required_features: 1 | (1 << 1),
            entry_function: None,
        };
        assert_eq!(
            Vm::from_artifact(artifact).unwrap().run(0, vec![]),
            Ok(Value::I64(42))
        );
    }

    #[test]
    fn deref_copy_reads_a_projected_target_without_consuming_the_loan() {
        let mut types = Type::predefined();
        let pair = types.len() as TypeId;
        types.push(Type::Struct {
            name: "CopyBox".into(),
            fields: vec![Field {
                name: "value".into(),
                ty: I64,
            }],
            copy: true,
        });
        let shared_pair = types.len() as TypeId;
        types.push(Type::RefShared { referent: pair });
        let shared_i64 = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let artifact = Artifact {
            required_features: 1 | (1 << 1),
            types,
            constants: vec![Constant::I64(42)],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, pair, shared_pair, shared_i64, I64, I64, I64],
                code_start: 0,
                code_len: 11,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 2,
                    ty: pair,
                    variant: None,
                    fields: vec![1],
                },
                Instruction::BorrowShared { dst: 3, src: 2 },
                Instruction::ProjectBorrowShared {
                    dst: 4,
                    src: 3,
                    field: 0,
                },
                Instruction::DerefCopy { dst: 5, src: 4 },
                Instruction::EndBorrow { reference: 4 },
                Instruction::EndBorrow { reference: 3 },
                Instruction::ProjectMove {
                    dst: 6,
                    src: 2,
                    field: 0,
                },
                Instruction::Deconstruct { src: 2 },
                Instruction::Primitive {
                    dst: 7,
                    op: Primitive::IntCheckedAdd,
                    args: vec![5, 6],
                },
                Instruction::Return { src: Some(7) },
            ],
            ..Artifact::default()
        };
        let verified = verify(artifact).expect("DEREF_COPY artifact must verify");
        assert_eq!(Vm::new(verified).run(0, vec![]), Ok(Value::I64(84)));
    }

    #[test]
    fn deref_copy_repeatedly_reads_a_whole_place_and_keeps_the_reference_live() {
        let mut types = Type::predefined();
        let unique_i64 = types.len() as TypeId;
        types.push(Type::RefUnique { referent: I64 });
        let artifact = Artifact {
            required_features: 1 | (1 << 1),
            types,
            constants: vec![Constant::I64(42)],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, unique_i64, I64, I64],
                code_start: 0,
                code_len: 8,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::DerefCopy { dst: 3, src: 2 },
                Instruction::DerefCopy { dst: 4, src: 2 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Drop { register: 1 },
                Instruction::Drop { register: 3 },
                Instruction::Return { src: Some(4) },
            ],
            ..Artifact::default()
        };
        let verified = verify(artifact).expect("repeated DEREF_COPY artifact must verify");
        assert_eq!(Vm::new(verified).run(0, vec![]), Ok(Value::I64(42)));
    }

    #[test]
    fn deref_move_store_replaces_a_whole_place_without_ending_its_unique_loan() {
        let mut types = Type::predefined();
        let unique_i64 = types.len() as TypeId;
        types.push(Type::RefUnique { referent: I64 });
        let artifact = Artifact {
            required_features: 1 | (1 << 1),
            types,
            constants: vec![Constant::I64(42), Constant::I64(7)],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "replace".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, unique_i64, I64, I64],
                code_start: 0,
                code_len: 8,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::DerefMove { dst: 3, src: 2 },
                Instruction::Const {
                    dst: 4,
                    constant: 1,
                },
                Instruction::DerefStore { dst: 2, src: 4 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Drop { register: 3 },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        let verified = verify(artifact).expect("DEREF_MOVE/STORE artifact must verify");
        assert_eq!(Vm::new(verified).run(0, vec![]), Ok(Value::I64(7)));
    }

    #[test]
    fn deref_copy_and_snapshot_copy_share_immutable_text_and_bytes_backing() {
        let mut types = Type::predefined();
        let shared_text = types.len() as TypeId;
        types.push(Type::RefShared { referent: TEXT });
        let artifact = Artifact {
            required_features: 1 | (1 << 1),
            types,
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "read_text".into(),
                params: vec![shared_text],
                return_type: TEXT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, shared_text, TEXT],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::DerefCopy { dst: 2, src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        let verified = verify(artifact).expect("Text DEREF_COPY artifact must verify");
        let text: Rc<str> = Rc::from("shared text");
        let slot = SlotStore::default()
            .insert(Some(Value::Text(text.clone())))
            .unwrap();
        let reference = Value::Reference {
            referent_type: TEXT,
            unique: false,
            target: ReferenceTarget::WholePlace(slot),
        };
        let Value::Text(copied_text) = Vm::new(verified).run(0, vec![reference]).unwrap() else {
            panic!("DEREF_COPY returned a non-Text value")
        };
        assert!(Rc::ptr_eq(&text, &copied_text));

        let bytes: Rc<[u8]> = Rc::from(&b"shared bytes"[..]);
        let copied = copy_value(
            &image(Artifact::default()),
            BYTES,
            &Value::Bytes(bytes.clone()),
        )
        .unwrap();
        let Value::Bytes(copied_bytes) = copied else {
            panic!("Bytes COPY returned a non-Bytes value")
        };
        assert!(Rc::ptr_eq(&bytes, &copied_bytes));

        let snapshotted = snapshot_clone_value(
            &image(Artifact::default()),
            BYTES,
            &Value::Bytes(bytes.clone()),
            &mut SnapshotCloneContext::default(),
        )
        .unwrap();
        let Value::Bytes(snapshotted_bytes) = snapshotted else {
            panic!("snapshot clone returned a non-Bytes value")
        };
        assert!(Rc::ptr_eq(&bytes, &snapshotted_bytes));
    }

    #[test]
    fn whole_text_place_and_unique_reference_forward_through_indirect_call() {
        let mut types = Type::predefined();
        let unique_text = types.len() as TypeId;
        types.push(Type::RefUnique {
            referent: crate::bytecode::TEXT,
        });
        let callable = types.len() as TypeId;
        types.push(Type::Callable {
            signature: Signature {
                params: vec![unique_text],
                result: unique_text,
                outward_protocols: vec![],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "forward unique text".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let artifact = Artifact {
            types,
            constants: vec![Constant::Text("stable".into())],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: crate::bytecode::TEXT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![
                        UNIT,
                        crate::bytecode::TEXT,
                        unique_text,
                        callable,
                        unique_text,
                    ],
                    code_start: 0,
                    code_len: 6,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "forward_unique".into(),
                    params: vec![unique_text],
                    return_type: unique_text,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, unique_text],
                    code_start: 6,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::MakeCallable {
                    dst: 3,
                    callable_type: callable,
                    function: 1,
                    captures: vec![],
                },
                Instruction::CallIndirect {
                    dst: Some(4),
                    callable: 3,
                    receiver_mode: 2,
                    args: vec![2],
                },
                Instruction::EndBorrow { reference: 4 },
                Instruction::Return { src: Some(1) },
                Instruction::Drop { register: 0 },
                Instruction::Return { src: Some(1) },
            ],
            required_features: 1 | (1 << 1),
            entry_function: None,
        };
        assert_eq!(
            Vm::from_artifact(artifact).unwrap().run(0, vec![]),
            Ok(Value::Text("stable".into()))
        );
    }

    #[test]
    fn verifier_rejects_returning_a_reference_to_a_local_scalar_place() {
        let mut types = Type::predefined();
        let shared_i64 = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(1)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "dangling".into(),
                params: vec![],
                return_type: shared_i64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, shared_i64],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            required_features: 1 | (1 << 1),
            entry_function: None,
        };
        assert!(Vm::from_artifact(artifact).is_err());
    }
    #[test]
    fn unit_calls_and_returns_use_none32_without_materializing_a_register() {
        let mut types = Type::predefined();
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "unit thunk".into(),
            copy: true,
            zero_use_allowed: true,
        });
        let artifact = Artifact {
            types,
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19],
                    code_start: 0,
                    code_len: 4,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "direct_unit".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT],
                    code_start: 4,
                    code_len: 1,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "indirect_unit".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT],
                    code_start: 5,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Call {
                    dst: None,
                    function: 1,
                    args: vec![],
                },
                Instruction::MakeCallable {
                    dst: 1,
                    callable_type: 19,
                    function: 2,
                    captures: vec![],
                },
                Instruction::CallIndirect {
                    dst: None,
                    callable: 1,
                    receiver_mode: 2,
                    args: vec![],
                },
                Instruction::Return { src: None },
                Instruction::Return { src: None },
                Instruction::Drop { register: 0 },
                Instruction::Return { src: None },
            ],
            ..Artifact::default()
        };
        let bytes = artifact.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(decoded.code, artifact.code);
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]),
            Ok(Value::Unit)
        );
    }
    #[test]
    fn tail_calls_do_not_need_a_growing_caller_frame() {
        let a = Artifact {
            types: Type::predefined(),
            constants: vec![Constant::I64(9)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "id".into(),
                    params: vec![I64],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64],
                    code_start: 2,
                    code_len: 1,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::TailCall {
                    function: 1,
                    args: vec![1],
                },
                Instruction::Return { src: Some(1) },
            ],
            required_features: 1,
            entry_function: None,
        };
        assert_eq!(
            Vm::from_artifact(a).unwrap().run(0, vec![]).unwrap(),
            Value::I64(9)
        );
    }

    #[test]
    fn moving_a_field_leaves_the_aggregate_for_later_drop() {
        let a = Artifact {
            types: {
                let mut types = Type::predefined();
                types.push(
                    Type::Struct {
                        name: "Pair".into(),
                        fields: vec![
                            Field {
                                name: "left".into(),
                                ty: I64,
                            },
                            Field {
                                name: "right".into(),
                                ty: I64,
                            },
                        ],
                        copy: false,
                    }
                    .restricted(false, true),
                );
                types
            },
            constants: vec![Constant::I64(20), Constant::I64(22)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, I64, 19, I64],
                code_start: 0,
                code_len: 6,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 1,
                },
                Instruction::Construct {
                    dst: 3,
                    ty: 19,
                    variant: None,
                    fields: vec![1, 2],
                },
                Instruction::ProjectMove {
                    dst: 4,
                    src: 3,
                    field: 1,
                },
                Instruction::Drop { register: 3 },
                Instruction::Return { src: Some(4) },
            ],
            required_features: 1,
            entry_function: None,
        };
        assert_eq!(
            Vm::from_artifact(a).unwrap().run(0, vec![]).unwrap(),
            Value::I64(22)
        );
    }

    #[test]
    fn executes_frozen_scalar_text_and_bytes_primitives() {
        assert_eq!(
            prim(
                U64,
                Primitive::IntBitXor,
                &[Value::U64(0b1010), Value::U64(0b1100)]
            ),
            Ok(Value::U64(0b0110))
        );
        assert_eq!(
            prim(U32, Primitive::IntLt, &[Value::I64(-1), Value::I64(0)]),
            Ok(Value::U64(1))
        );
        assert_eq!(
            prim(U64, Primitive::IntShl, &[Value::U64(1), Value::U64(64)]),
            Err(RuntimeError::InvalidShiftCount)
        );
        let Value::F64(nan) = prim(
            F64,
            Primitive::FloatAdd,
            &[Value::F64(f64::NAN), Value::F64(1.0)],
        )
        .unwrap() else {
            panic!("float.add returned a non-float")
        };
        assert_eq!(nan.to_bits(), 0x7ff8_0000_0000_0000);
        assert_eq!(
            prim(
                TEXT,
                Primitive::TextConcat,
                &[Value::Text("grand".into()), Value::Text("iose".into())]
            ),
            Ok(Value::Text("grandiose".into()))
        );
        let left_text: Rc<str> = Rc::from("grand");
        let Value::Text(joined_text) = prim(
            TEXT,
            Primitive::TextConcat,
            &[Value::Text(left_text.clone()), Value::Text("iose".into())],
        )
        .unwrap() else {
            panic!("TextConcat returned a non-Text value")
        };
        assert!(!Rc::ptr_eq(&left_text, &joined_text));
        assert_eq!(
            prim(CHAR, Primitive::CharFromU32Checked, &[Value::U64(0x1f600)]),
            Ok(Value::U64(0x1f600))
        );
        assert_eq!(
            prim(CHAR, Primitive::CharFromU32Checked, &[Value::U64(0xd800)]),
            Err(RuntimeError::InvalidCharacter)
        );
        assert_eq!(
            prim(
                TEXT,
                Primitive::TextFromUtf8Checked,
                &[Value::Bytes(vec![0xff].into())]
            ),
            Err(RuntimeError::InvalidUtf8)
        );
        assert_eq!(
            prim(
                USIZE,
                Primitive::BytesUtf8ValidUpTo,
                &[Value::Bytes(
                    b"a\xc2\xa2\xe2\x82\xac\xf0\x9f\x92\xa9".to_vec().into()
                )]
            ),
            Ok(Value::U64(10))
        );
        assert_eq!(
            prim(
                USIZE,
                Primitive::BytesUtf8ValidUpTo,
                &[Value::Bytes(b"ab\xed\xa0\x80".to_vec().into())]
            ),
            Ok(Value::U64(2))
        );
        assert_eq!(
            prim(
                USIZE,
                Primitive::BytesUtf8ValidUpTo,
                &[Value::Bytes(b"ab\xf0\x9f\x92".to_vec().into())]
            ),
            Ok(Value::U64(2))
        );
        assert_eq!(
            prim(
                BYTES,
                Primitive::BytesSlice,
                &[
                    Value::Bytes(vec![10, 20, 30].into()),
                    Value::U64(1),
                    Value::U64(3),
                ]
            ),
            Ok(Value::Bytes(vec![20, 30].into()))
        );
        let left_bytes: Rc<[u8]> = vec![10, 20].into();
        let Value::Bytes(joined_bytes) = prim(
            BYTES,
            Primitive::BytesConcat,
            &[
                Value::Bytes(left_bytes.clone()),
                Value::Bytes(vec![30].into()),
            ],
        )
        .unwrap() else {
            panic!("BytesConcat returned a non-Bytes value")
        };
        assert!(!Rc::ptr_eq(&left_bytes, &joined_bytes));
        assert_eq!(
            prim(
                U8,
                Primitive::BytesGet,
                &[Value::Bytes(vec![10].into()), Value::U64(1)]
            ),
            Err(RuntimeError::IndexOutOfBounds)
        );
    }

    #[test]
    fn every_integer_width_obeys_checked_wrapping_and_shift_boundaries() {
        let integer_types = [
            U8, U16, U32, U64, U128, I8, I16, I32, I64, I128, USIZE, ISIZE,
        ];
        let binary_ops = [
            Primitive::IntCheckedAdd,
            Primitive::IntCheckedSub,
            Primitive::IntCheckedMul,
            Primitive::IntCheckedDiv,
            Primitive::IntCheckedRem,
            Primitive::IntWrappingAdd,
            Primitive::IntWrappingSub,
            Primitive::IntWrappingMul,
            Primitive::IntBitAnd,
            Primitive::IntBitOr,
            Primitive::IntBitXor,
            Primitive::IntEq,
            Primitive::IntNe,
            Primitive::IntLt,
            Primitive::IntLe,
            Primitive::IntGt,
            Primitive::IntGe,
        ];
        for ty in integer_types {
            let spec = int_spec(ty).unwrap();
            let three = make_int(spec, 3);
            let six = make_int(spec, 6);
            for op in binary_ops {
                let result = if matches!(
                    op,
                    Primitive::IntEq
                        | Primitive::IntNe
                        | Primitive::IntLt
                        | Primitive::IntLe
                        | Primitive::IntGt
                        | Primitive::IntGe
                ) {
                    U32
                } else {
                    ty
                };
                primitive_typed(
                    &image(Artifact::default()),
                    result,
                    op,
                    &[ty, ty],
                    &[six.clone(), three.clone()],
                )
                .unwrap();
            }
            for op in [
                Primitive::IntBitNot,
                Primitive::IntCheckedNeg,
                Primitive::IntWrappingNeg,
            ] {
                let input = if !spec.signed && op == Primitive::IntCheckedNeg {
                    make_int(spec, 0)
                } else {
                    three.clone()
                };
                primitive_typed(&image(Artifact::default()), ty, op, &[ty], &[input]).unwrap();
            }

            let maximum = if spec.signed {
                signed_bounds(spec.bits).1 as u128
            } else {
                int_mask(spec.bits)
            };
            assert_eq!(
                primitive_typed(
                    &image(Artifact::default()),
                    ty,
                    Primitive::IntCheckedAdd,
                    &[ty, ty],
                    &[make_int(spec, maximum), make_int(spec, 1)]
                ),
                Err(RuntimeError::ArithmeticOverflow),
                "checked maximum overflow for type {ty}",
            );
            let wrapped = primitive_typed(
                &image(Artifact::default()),
                ty,
                Primitive::IntWrappingAdd,
                &[ty, ty],
                &[make_int(spec, maximum), make_int(spec, 1)],
            )
            .unwrap();
            assert_eq!(
                wrapped,
                make_int(spec, maximum.wrapping_add(1)),
                "wrapping maximum for type {ty}"
            );
            assert_eq!(
                primitive_typed(
                    &image(Artifact::default()),
                    ty,
                    Primitive::IntShl,
                    &[ty, U32],
                    &[make_int(spec, 1), Value::U64(u64::from(spec.bits))]
                ),
                Err(RuntimeError::InvalidShiftCount),
                "shift width for type {ty}",
            );
            if spec.signed {
                let minimum = 1_u128 << (spec.bits - 1);
                assert_eq!(
                    primitive_typed(
                        &image(Artifact::default()),
                        ty,
                        Primitive::IntCheckedNeg,
                        &[ty],
                        &[make_int(spec, minimum)]
                    ),
                    Err(RuntimeError::ArithmeticOverflow),
                );
                assert_eq!(
                    primitive_typed(
                        &image(Artifact::default()),
                        ty,
                        Primitive::IntWrappingNeg,
                        &[ty],
                        &[make_int(spec, minimum)]
                    ),
                    Ok(make_int(spec, minimum)),
                );
            }
        }
    }

    #[test]
    fn numeric_conversions_are_width_signedness_and_float_checked() {
        assert_eq!(
            primitive_typed(
                &image(Artifact::default()),
                U8,
                Primitive::IntConvertChecked,
                &[I16],
                &[Value::I64(-1)]
            ),
            Err(RuntimeError::ArithmeticOverflow),
        );
        assert_eq!(
            primitive_typed(
                &image(Artifact::default()),
                U16,
                Primitive::IntConvertWrapping,
                &[I8],
                &[Value::I64(-1)]
            ),
            Ok(Value::U64(u16::MAX.into())),
        );
        assert_eq!(
            primitive_typed(
                &image(Artifact::default()),
                I8,
                Primitive::IntConvertChecked,
                &[U16],
                &[Value::U64(128)]
            ),
            Err(RuntimeError::ArithmeticOverflow),
        );
        assert_eq!(
            primitive_typed(
                &image(Artifact::default()),
                I8,
                Primitive::IntConvertWrapping,
                &[U16],
                &[Value::U64(255)]
            ),
            Ok(Value::I64(-1)),
        );

        let Value::F32(nan32) = primitive_typed(
            &image(Artifact::default()),
            F32,
            Primitive::FloatAdd,
            &[F32, F32],
            &[Value::F32(f32::NAN), Value::F32(1.0)],
        )
        .unwrap() else {
            panic!()
        };
        assert_eq!(nan32.to_bits(), 0x7fc0_0000);
        let Value::F32(converted_nan) = primitive_typed(
            &image(Artifact::default()),
            F32,
            Primitive::FloatConvert,
            &[F64],
            &[Value::F64(f64::NAN)],
        )
        .unwrap() else {
            panic!()
        };
        assert_eq!(converted_nan.to_bits(), 0x7fc0_0000);
        assert_eq!(
            primitive_typed(
                &image(Artifact::default()),
                U8,
                Primitive::FloatToIntChecked,
                &[F64],
                &[Value::F64(255.9)]
            ),
            Ok(Value::U64(255)),
        );
        for invalid in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 256.0, -1.0] {
            assert_eq!(
                primitive_typed(
                    &image(Artifact::default()),
                    U8,
                    Primitive::FloatToIntChecked,
                    &[F64],
                    &[Value::F64(invalid)]
                ),
                Err(RuntimeError::ArithmeticOverflow),
            );
        }
        assert_eq!(
            primitive_typed(
                &image(Artifact::default()),
                F64,
                Primitive::IntToFloat,
                &[U128],
                &[Value::U128(u128::MAX)]
            ),
            Ok(Value::F64(u128::MAX as f64)),
        );
        assert_eq!(
            primitive_typed(
                &image(Artifact::default()),
                I128,
                Primitive::FloatToIntChecked,
                &[F64],
                &[Value::F64(2_f64.powi(127))]
            ),
            Err(RuntimeError::ArithmeticOverflow),
        );
    }

    #[test]
    fn frozen_float_leaves_preserve_zero_and_canonicalize_every_nan_bit_path() {
        for (ty, negative_zero, canonical_nan, bits_ty) in [
            (F32, Value::F32(-0.0), 0x7fc0_0000_u64, U32),
            (F64, Value::F64(-0.0), 0x7ff8_0000_0000_0000_u64, U64),
        ] {
            let negated = primitive_typed(
                &image(Artifact::default()),
                ty,
                Primitive::FloatNeg,
                &[ty],
                std::slice::from_ref(&negative_zero),
            )
            .unwrap();
            match negated {
                Value::F32(value) => assert_eq!(value.to_bits(), 0),
                Value::F64(value) => assert_eq!(value.to_bits(), 0),
                _ => panic!(),
            }
            assert_eq!(
                primitive_typed(
                    &image(Artifact::default()),
                    bits_ty,
                    Primitive::FloatToBits,
                    &[ty],
                    std::slice::from_ref(&negative_zero),
                ),
                Ok(Value::U64(if ty == F32 {
                    1_u64 << 31
                } else {
                    1_u64 << 63
                }))
            );

            let hostile_nan = if ty == F32 {
                Value::F32(f32::from_bits(0xff80_0001))
            } else {
                Value::F64(f64::from_bits(0xfff0_0000_0000_0001))
            };
            assert_eq!(
                primitive_typed(
                    &image(Artifact::default()),
                    bits_ty,
                    Primitive::FloatToBits,
                    &[ty],
                    &[hostile_nan],
                ),
                Ok(Value::U64(canonical_nan))
            );
            let from_bits = primitive_typed(
                &image(Artifact::default()),
                ty,
                Primitive::FloatFromBits,
                &[bits_ty],
                &[Value::U64(if ty == F32 {
                    0xff80_0001
                } else {
                    0xfff0_0000_0000_0001
                })],
            )
            .unwrap();
            match from_bits {
                Value::F32(value) => assert_eq!(u64::from(value.to_bits()), canonical_nan),
                Value::F64(value) => assert_eq!(value.to_bits(), canonical_nan),
                _ => panic!(),
            }
        }

        for (ty, a, b) in [
            (F32, Value::F32(7.5), Value::F32(2.0)),
            (F64, Value::F64(7.5), Value::F64(2.0)),
        ] {
            for op in [
                Primitive::FloatAdd,
                Primitive::FloatSub,
                Primitive::FloatMul,
                Primitive::FloatDiv,
                Primitive::FloatRem,
            ] {
                assert!(
                    primitive_typed(
                        &image(Artifact::default()),
                        ty,
                        op,
                        &[ty, ty],
                        &[a.clone(), b.clone()],
                    )
                    .is_ok()
                );
            }
            for op in [
                Primitive::FloatEq,
                Primitive::FloatNe,
                Primitive::FloatLt,
                Primitive::FloatLe,
                Primitive::FloatGt,
                Primitive::FloatGe,
            ] {
                assert!(matches!(
                    primitive_typed(
                        &image(Artifact::default()),
                        U32,
                        op,
                        &[ty, ty],
                        &[a.clone(), b.clone()],
                    ),
                    Ok(Value::U64(value)) if value <= 1
                ));
            }
        }
    }

    #[test]
    fn checked_float_to_integer_observes_every_width_boundary() {
        let image = image(Artifact::default());
        for ty in [
            U8, U16, U32, U64, U128, USIZE, I8, I16, I32, I64, I128, ISIZE,
        ] {
            let spec = int_spec(ty).unwrap();
            let (inside, outside, expected) = if spec.signed {
                let limit = 2_f64.powi((spec.bits - 1) as i32);
                (-limit, limit, make_int(spec, (-limit as i128) as u128))
            } else {
                let limit = 2_f64.powi(spec.bits as i32);
                (0.0, limit, make_int(spec, 0))
            };
            assert_eq!(
                primitive_typed(
                    &image,
                    ty,
                    Primitive::FloatToIntChecked,
                    &[F64],
                    &[Value::F64(inside)],
                ),
                Ok(expected)
            );
            assert_eq!(
                primitive_typed(
                    &image,
                    ty,
                    Primitive::FloatToIntChecked,
                    &[F64],
                    &[Value::F64(outside)],
                ),
                Err(RuntimeError::ArithmeticOverflow)
            );
            assert!(
                primitive_typed(
                    &image,
                    F32,
                    Primitive::IntToFloat,
                    &[ty],
                    &[make_int(
                        spec,
                        if spec.signed {
                            u128::MAX
                        } else {
                            int_mask(spec.bits)
                        }
                    )],
                )
                .is_ok()
            );
        }
        for invalid in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert_eq!(
                primitive_typed(
                    &image,
                    I128,
                    Primitive::FloatToIntChecked,
                    &[F64],
                    &[Value::F64(invalid)],
                ),
                Err(RuntimeError::ArithmeticOverflow)
            );
        }
    }

    #[test]
    fn comparison_primitive_runs_through_verified_bytecode() {
        let a = Artifact {
            types: Type::predefined(),
            constants: vec![Constant::I64(-1), Constant::I64(0)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: U32,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, I64, U32],
                code_start: 0,
                code_len: 4,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 1,
                },
                Instruction::Primitive {
                    dst: 3,
                    op: Primitive::IntLt,
                    args: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1,
            entry_function: None,
        };
        assert_eq!(
            Vm::from_artifact(a).unwrap().run(0, vec![]).unwrap(),
            Value::U64(1)
        );
    }

    #[test]
    fn array_push_uses_frozen_geometric_capacity() {
        let mut types = Type::predefined();
        types.push(Type::Array { element: U64 }.restricted(false, true));
        types.push(Type::RefUnique { referent: 19 });
        types.push(Type::RefShared { referent: 19 });
        let a = Artifact {
            required_features: 1 | (1 << 1) | (1 << 6),
            types,
            constants: vec![Constant::U64(42)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: USIZE,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 20, U64, UNIT, 21, USIZE],
                code_start: 0,
                code_len: 9,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 1,
                    op: Primitive::ArrayEmpty,
                    args: vec![],
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Primitive {
                    dst: 4,
                    op: Primitive::ArrayPushMove,
                    args: vec![2, 3],
                },
                Instruction::Drop { register: 4 },
                Instruction::BorrowShared { dst: 5, src: 1 },
                Instruction::Primitive {
                    dst: 6,
                    op: Primitive::ArrayCapacity,
                    args: vec![5],
                },
                Instruction::Drop { register: 1 },
                Instruction::Return { src: Some(6) },
            ],
            entry_function: None,
        };
        let encoded = a.encode();
        let decoded = Artifact::decode(&encoded).unwrap();
        assert_eq!(decoded.encode(), encoded);
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::U64(4)
        );
    }

    #[test]
    fn array_move_leaves_an_empty_slot_that_drops_safely() {
        let mut types = Type::predefined();
        types.push(Type::Array { element: U64 }.restricted(false, true));
        types.push(Type::RefUnique { referent: 19 });
        let a = Artifact {
            required_features: 1 | (1 << 1),
            types,
            constants: vec![Constant::U64(42)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![USIZE, USIZE],
                return_type: U64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, USIZE, USIZE, U64, 19, 20, U64],
                code_start: 0,
                code_len: 6,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Primitive {
                    dst: 4,
                    op: Primitive::ArrayNew,
                    args: vec![1, 3],
                },
                Instruction::BorrowUnique { dst: 5, src: 4 },
                Instruction::Primitive {
                    dst: 6,
                    op: Primitive::ArrayGetMove,
                    args: vec![5, 2],
                },
                Instruction::Drop { register: 4 },
                Instruction::Return { src: Some(6) },
            ],
            entry_function: None,
        };
        assert_eq!(
            Vm::from_artifact(a)
                .unwrap()
                .run(0, vec![Value::U64(1), Value::U64(0)])
                .unwrap(),
            Value::U64(42)
        );
    }

    #[test]
    fn finish_drained_closes_an_exact_linear_array_after_its_element_moves() {
        let mut types = Type::predefined();
        types[U64 as usize] = Type::U64.restricted(false, false);
        types.push(Type::Array { element: U64 });
        types.push(Type::RefUnique { referent: 19 });
        let artifact = Artifact {
            required_features: 1 | (1 << 1) | (1 << 7),
            types,
            constants: vec![],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "drain_one".into(),
                params: vec![19, USIZE],
                return_type: U64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, USIZE, 20, U64, UNIT],
                code_start: 0,
                code_len: 4,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::BorrowUnique { dst: 3, src: 1 },
                Instruction::Primitive {
                    dst: 4,
                    op: Primitive::ArrayGetMove,
                    args: vec![3, 2],
                },
                Instruction::Primitive {
                    dst: 5,
                    op: Primitive::ArrayFinishDrained,
                    args: vec![1],
                },
                Instruction::Return { src: Some(4) },
            ],
            entry_function: None,
        };

        assert_eq!(
            Vm::from_artifact(artifact)
                .unwrap()
                .run(0, vec![Value::array(U64, [Value::U64(42)]), Value::U64(0)])
                .unwrap(),
            Value::U64(42)
        );
    }

    #[test]
    fn finish_drained_faults_without_destroying_a_resident_element() {
        let mut types = Type::predefined();
        types[U64 as usize] = Type::U64.restricted(false, false);
        types.push(Type::Array { element: U64 });
        let artifact = Artifact {
            required_features: 1 | (1 << 7),
            types,
            constants: vec![],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "finish_resident".into(),
                params: vec![19],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, UNIT],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 2,
                    op: Primitive::ArrayFinishDrained,
                    args: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            entry_function: None,
        };
        let input = Value::array(U64, [Value::U64(42)]);
        let Value::Array(storage) = &input else {
            unreachable!()
        };
        let retained = storage.clone();

        let error = Vm::from_artifact(artifact)
            .unwrap()
            .run(0, vec![input])
            .unwrap_err();
        assert_eq!(error, RuntimeError::ArrayNotDrained);
        assert_eq!(error.category(), RuntimeFaultCategory::PrimitiveTrap);
        assert_eq!(retained.borrow().slots, [Some(Value::U64(42))]);
    }

    #[test]
    fn array_slot_mutation_reserve_pop_and_bytes_conversion_follow_g1() {
        let mut types = Type::predefined();
        types.push(Type::Array { element: U64 });
        types.push(Type::RefUnique { referent: 19 });
        types.push(Type::RefShared { referent: 19 });
        types.push(Type::Array { element: U8 });
        let artifact = image(Artifact {
            types,
            ..Artifact::default()
        });
        let array = primitive(
            &artifact,
            19,
            Primitive::ArrayNew,
            &[Value::U64(1), Value::U64(42)],
        )
        .unwrap();
        let Value::Array(storage) = &array else {
            panic!("array.new returned a non-array")
        };
        let unique = || Value::Reference {
            referent_type: 19,
            unique: true,
            target: ReferenceTarget::Array(storage.clone()),
        };
        let shared = || Value::Reference {
            referent_type: 19,
            unique: false,
            target: ReferenceTarget::Array(storage.clone()),
        };
        assert_eq!(
            primitive(
                &artifact,
                U64,
                Primitive::ArrayGetMove,
                &[unique(), Value::U64(0)]
            ),
            Ok(Value::U64(42))
        );
        assert_eq!(
            primitive(
                &artifact,
                UNIT,
                Primitive::ArraySetMove,
                &[unique(), Value::U64(0), Value::U64(9)]
            ),
            Ok(Value::Unit)
        );
        assert_eq!(
            primitive(
                &artifact,
                U64,
                Primitive::ArrayGetCopy,
                &[shared(), Value::U64(0)]
            ),
            Ok(Value::U64(9))
        );
        primitive(
            &artifact,
            UNIT,
            Primitive::ArrayPushMove,
            &[unique(), Value::U64(10)],
        )
        .unwrap();
        primitive(
            &artifact,
            UNIT,
            Primitive::ArrayReserve,
            &[unique(), Value::U64(10)],
        )
        .unwrap();
        assert_eq!(
            primitive(&artifact, USIZE, Primitive::ArrayCapacity, &[shared()]),
            Ok(Value::U64(16))
        );
        assert_eq!(
            primitive(&artifact, U64, Primitive::ArrayPopMove, &[unique()]),
            Ok(Value::U64(10))
        );

        let backing: Rc<[u8]> = vec![1, 2, 3].into();
        let bytes = Value::Bytes(backing.clone());
        let byte_array = primitive(&artifact, 22, Primitive::BytesToArray, &[bytes]).unwrap();
        let Value::Array(storage) = &byte_array else {
            panic!("BytesToArray returned a non-Array value")
        };
        assert_eq!(storage.borrow().logical_capacity, 3);
        storage.borrow_mut().slots[0] = Some(Value::U64(9));
        assert_eq!(backing.as_ref(), &[1, 2, 3]);
        assert_eq!(
            primitive(
                &artifact,
                BYTES,
                Primitive::BytesFromArrayMove,
                &[byte_array]
            ),
            Ok(Value::Bytes(vec![9, 2, 3].into()))
        );
    }

    #[test]
    fn array_reference_follows_an_aggregate_field_projection() {
        let array = Value::array(U64, [Value::U64(42)]);
        let Value::Array(storage) = &array else {
            panic!("array constructor returned a non-array")
        };
        let retained = storage.clone();
        let owner = Value::aggregate(19, [array]);
        let Value::Aggregate(owner) = owner else {
            panic!("aggregate constructor returned a non-aggregate")
        };
        let projected = Value::Reference {
            referent_type: 20,
            unique: true,
            target: ReferenceTarget::AggregateField {
                aggregate: owner,
                field: 0,
            },
        };

        let resolved = reference_array(&projected, true).unwrap();
        assert!(ArenaObject::ptr_eq(&resolved, &retained));
        assert_eq!(resolved.borrow().slots, [Some(Value::U64(42))]);
    }

    #[test]
    fn array_copy_primitives_structurally_copy_aggregate_elements() {
        let mut types = Type::predefined();
        types.push(Type::Tuple {
            fields: vec![U64],
            copy: true,
        });
        types.push(Type::Array { element: 19 });
        types.push(Type::RefShared { referent: 20 });
        let artifact = image(Artifact {
            types,
            ..Artifact::default()
        });
        let fill = Value::aggregate(19, [Value::U64(7)]);
        let array = primitive(
            &artifact,
            20,
            Primitive::ArrayNew,
            &[Value::U64(2), fill.clone()],
        )
        .unwrap();
        let Value::Array(storage) = &array else {
            panic!("array.new returned a non-array")
        };
        let first = storage.borrow().slots[0].as_ref().unwrap().clone();
        let second = storage.borrow().slots[1].as_ref().unwrap().clone();
        let (Value::Aggregate(fill), Value::Aggregate(first), Value::Aggregate(second)) =
            (&fill, &first, &second)
        else {
            panic!("aggregate array elements")
        };
        assert!(!ArenaObject::ptr_eq(fill, first));
        assert!(!ArenaObject::ptr_eq(first, second));
        first.borrow_mut().fields[0] = Some(Value::U64(9));
        assert_eq!(second.borrow().fields[0], Some(Value::U64(7)));

        let copied = primitive(
            &artifact,
            19,
            Primitive::ArrayGetCopy,
            &[
                Value::Reference {
                    referent_type: 20,
                    unique: false,
                    target: ReferenceTarget::Array(storage.clone()),
                },
                Value::U64(1),
            ],
        )
        .unwrap();
        let Value::Aggregate(copied) = copied else {
            panic!("array.get_copy returned a non-aggregate")
        };
        assert!(!ArenaObject::ptr_eq(&copied, second));
        copied.borrow_mut().fields[0] = Some(Value::U64(11));
        assert_eq!(second.borrow().fields[0], Some(Value::U64(7)));
    }

    #[test]
    fn hostile_array_length_traps_before_allocating() {
        let mut types = Type::predefined();
        types.push(Type::Array { element: U64 });
        let artifact = Artifact {
            types,
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "huge_array".into(),
                params: vec![USIZE, U64],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, USIZE, U64, 19],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 3,
                    op: Primitive::ArrayNew,
                    args: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
            ],
            ..Artifact::default()
        };
        assert_eq!(
            Vm::from_artifact(artifact)
                .unwrap()
                .run(0, vec![Value::U64(u64::MAX), Value::U64(1)]),
            Err(RuntimeError::AllocationOverflow)
        );
        assert_eq!(
            RuntimeError::AllocationOverflow.category(),
            RuntimeFaultCategory::PrimitiveTrap
        );
        assert_eq!(
            checked_output_bytes::<u8>(MAX_PRIMITIVE_ALLOCATION_BYTES + 1),
            Err(RuntimeError::AllocationLimit)
        );
        assert_eq!(
            RuntimeError::AllocationLimit.category(),
            RuntimeFaultCategory::MemoryLimit
        );
    }

    #[test]
    fn enum_payload_projection_requires_and_uses_a_dominating_tag_edge() {
        let mut types = Type::predefined();
        types.push(
            Type::Enum {
                name: "Choice".into(),
                variants: vec![
                    EnumVariant {
                        name: "Signed".into(),
                        fields: vec![Field {
                            name: "value".into(),
                            ty: I64,
                        }],
                    tag: None,
},
                    EnumVariant {
                        name: "Unsigned".into(),
                        fields: vec![Field {
                            name: "value".into(),
                            ty: U64,
                        }],
                    tag: None,
},
                ],
                copy: false,
            }
            .restricted(false, true),
        );
        let a = Artifact {
            types,
            constants: vec![Constant::U32(0), Constant::I64(42)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, 19, U32, I64],
                code_start: 0,
                code_len: 9,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 1,
                },
                Instruction::Construct {
                    dst: 2,
                    ty: 19,
                    variant: Some(0),
                    fields: vec![1],
                },
                Instruction::EnumTag { dst: 3, src: 2 },
                Instruction::Switch {
                    discr: 3,
                    cases: vec![(0, 4)],
                    otherwise: 8,
                },
                Instruction::Drop { register: 3 },
                Instruction::ProjectMove {
                    dst: 4,
                    src: 2,
                    field: 0,
                },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(4) },
                Instruction::Unreachable,
            ],
            required_features: 1,
            entry_function: None,
        };
        let bytes = a.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::I64(42)
        );
    }

    #[test]
    fn reborrow_and_projected_unique_loan_restore_the_parent_after_end() {
        let mut types = Type::predefined();
        types.push(
            Type::Struct {
                name: "Pair".into(),
                fields: vec![
                    Field {
                        name: "left".into(),
                        ty: I64,
                    },
                    Field {
                        name: "right".into(),
                        ty: I64,
                    },
                ],
                copy: false,
            }
            .restricted(false, true),
        );
        types.push(Type::RefUnique { referent: 19 });
        types.push(Type::RefShared { referent: 19 }.restricted(false, true));
        types.push(Type::RefUnique { referent: I64 });
        let a = Artifact {
            types,
            constants: vec![Constant::Unit, Constant::I64(20), Constant::I64(22)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, I64, 19, 20, 21, 22, UNIT],
                code_start: 0,
                code_len: 12,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 1,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 2,
                },
                Instruction::Construct {
                    dst: 3,
                    ty: 19,
                    variant: None,
                    fields: vec![1, 2],
                },
                Instruction::BorrowUnique { dst: 4, src: 3 },
                Instruction::ReborrowShared { dst: 5, src: 4 },
                Instruction::EndBorrow { reference: 5 },
                Instruction::ProjectBorrowUnique {
                    dst: 6,
                    src: 4,
                    field: 1,
                },
                Instruction::EndBorrow { reference: 6 },
                Instruction::EndBorrow { reference: 4 },
                Instruction::Drop { register: 3 },
                Instruction::Const {
                    dst: 7,
                    constant: 0,
                },
                Instruction::Return { src: Some(7) },
            ],
            required_features: 1 | (1 << 1),
            entry_function: None,
        };
        let bytes = a.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::Unit
        );
    }

    #[test]
    fn disjoint_struct_fields_support_simultaneous_unique_loans() {
        let mut types = Type::predefined();
        types.push(
            Type::Struct {
                name: "Pair".into(),
                fields: vec![
                    Field {
                        name: "left".into(),
                        ty: I64,
                    },
                    Field {
                        name: "right".into(),
                        ty: I64,
                    },
                ],
                copy: false,
            }
            .restricted(false, true),
        );
        types.push(Type::RefUnique { referent: I64 });
        let a = Artifact {
            types,
            constants: vec![Constant::Unit, Constant::I64(20), Constant::I64(22)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, I64, 19, 20, 20, UNIT],
                code_start: 0,
                code_len: 10,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 1,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 2,
                },
                Instruction::Construct {
                    dst: 3,
                    ty: 19,
                    variant: None,
                    fields: vec![1, 2],
                },
                Instruction::ProjectBorrowUnique {
                    dst: 4,
                    src: 3,
                    field: 0,
                },
                Instruction::ProjectBorrowUnique {
                    dst: 5,
                    src: 3,
                    field: 1,
                },
                Instruction::EndBorrow { reference: 5 },
                Instruction::EndBorrow { reference: 4 },
                Instruction::Drop { register: 3 },
                Instruction::Const {
                    dst: 6,
                    constant: 0,
                },
                Instruction::Return { src: Some(6) },
            ],
            required_features: 1 | (1 << 1),
            entry_function: None,
        };
        let bytes = a.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::Unit
        );
    }

    #[test]
    fn ordinary_integer_switch_is_independent_of_enum_tag_analysis() {
        let a = Artifact {
            constants: vec![Constant::I64(1), Constant::I64(42)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, I64],
                code_start: 0,
                code_len: 6,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Switch {
                    discr: 1,
                    cases: vec![(0, 2)],
                    otherwise: 5,
                },
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 2,
                    constant: 1,
                },
                Instruction::Return { src: Some(2) },
                Instruction::Unreachable,
            ],
            ..Artifact::default()
        };
        let bytes = a.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::I64(42)
        );
    }

    #[test]
    fn callable_roundtrip_move_call_and_structural_copy_use_independent_captures() {
        let mut types = Type::predefined();
        types.push(Type::Available {
            identity_name: "erased capture witness".into(),
        });
        types.push(
            Type::Tuple {
                fields: vec![19, I64, 19],
                copy: true,
            }
            .restricted(true, true),
        );
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            capture_type: 20,
            receiver_mode: 2,
            identity_name: "copyable closure".into(),
            copy: true,
            zero_use_allowed: true,
        });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(21)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, 21, 21, I64, I64, I64],
                    code_start: 0,
                    code_len: 7,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "closure body".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![20, I64],
                    code_start: 7,
                    code_len: 3,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::MakeCallable {
                    dst: 2,
                    callable_type: 21,
                    function: 1,
                    captures: vec![1],
                },
                Instruction::Copy { dst: 3, src: 2 },
                Instruction::CallIndirect {
                    dst: Some(4),
                    callable: 2,
                    receiver_mode: 2,
                    args: vec![],
                },
                Instruction::CallIndirect {
                    dst: Some(5),
                    callable: 3,
                    receiver_mode: 2,
                    args: vec![],
                },
                Instruction::Primitive {
                    dst: 6,
                    op: Primitive::IntCheckedAdd,
                    args: vec![4, 5],
                },
                Instruction::Return { src: Some(6) },
                Instruction::ProjectMove {
                    dst: 1,
                    src: 0,
                    field: 1,
                },
                Instruction::Drop { register: 0 },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(decoded.types, artifact.types);
        assert_eq!(decoded.functions[1].receiver_mode, Some(2));
        assert_eq!(decoded.code, artifact.code);
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::I64(42)
        );

        let mut invalid = artifact;
        invalid.code[7] = Instruction::ProjectMove {
            dst: 1,
            src: 0,
            field: 0,
        };
        assert!(matches!(
            Vm::from_artifact(invalid),
            Err(VerifyError::InvalidAggregate {
                function: 1,
                instruction: 0
            })
        ));
    }

    #[test]
    fn shared_callable_receiver_can_be_reused_after_each_call() {
        let mut types = Type::predefined();
        types.push(
            Type::Tuple {
                fields: vec![I64],
                copy: true,
            }
            .restricted(true, true),
        );
        types.push(Type::RefShared { referent: 19 });
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            capture_type: 19,
            receiver_mode: 0,
            identity_name: "shared closure".into(),
            copy: true,
            zero_use_allowed: true,
        });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(6)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, 21, I64, I64, I64],
                    code_start: 0,
                    code_len: 7,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "shared body".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: Some(0),
                    register_types: vec![20, I64],
                    code_start: 7,
                    code_len: 3,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::MakeCallable {
                    dst: 2,
                    callable_type: 21,
                    function: 1,
                    captures: vec![1],
                },
                Instruction::CallIndirect {
                    dst: Some(3),
                    callable: 2,
                    receiver_mode: 0,
                    args: vec![],
                },
                Instruction::CallIndirect {
                    dst: Some(4),
                    callable: 2,
                    receiver_mode: 0,
                    args: vec![],
                },
                Instruction::Primitive {
                    dst: 5,
                    op: Primitive::IntCheckedAdd,
                    args: vec![3, 4],
                },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(5) },
                Instruction::ProjectCopy {
                    dst: 1,
                    src: 0,
                    field: 0,
                },
                Instruction::EndBorrow { reference: 0 },
                Instruction::Return { src: Some(1) },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::I64(12)
        );
    }

    #[test]
    fn tail_call_indirect_moves_receiver_and_replaces_the_frame() {
        let mut types = Type::predefined();
        types.push(
            Type::Tuple {
                fields: vec![I64],
                copy: false,
            }
            .restricted(false, true),
        );
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            capture_type: 19,
            receiver_mode: 2,
            identity_name: "tail closure".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(9)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, 20],
                    code_start: 0,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "tail body".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![19, I64],
                    code_start: 3,
                    code_len: 3,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::MakeCallable {
                    dst: 2,
                    callable_type: 20,
                    function: 1,
                    captures: vec![1],
                },
                Instruction::TailCallIndirect {
                    callable: 2,
                    receiver_mode: 2,
                    args: vec![],
                },
                Instruction::ProjectMove {
                    dst: 1,
                    src: 0,
                    field: 0,
                },
                Instruction::Drop { register: 0 },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::I64(9)
        );
    }

    #[test]
    fn protocol_handler_descriptors_and_make_handler_roundtrip_exactly() {
        let clause_signature = Signature {
            params: vec![],
            result: I64,
            outward_protocols: vec![],
        };
        let mut types = Type::predefined();
        types.push(Type::Callable {
            signature: clause_signature.clone(),
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "terminal clause".into(),
            copy: true,
            zero_use_allowed: true,
        });
        types.push(Type::Tuple {
            fields: vec![19],
            copy: false,
        });
        types.push(Type::Handler {
            handler_def: 0,
            capture_type: 20,
            identity_name: "test handler".into(),
        });
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![0],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "terminal body".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let protocol = Protocol {
            display_name: "Stop".into(),
            type_arguments: vec![],
            operations: vec![Operation {
                name: "stop".into(),
                payload_signature: Signature {
                    params: vec![],
                    result: NEVER,
                    outward_protocols: vec![],
                },
                result_type: NEVER,
                resumption_lower: 0,
                resumption_upper: Some(0),
                terminal: true,
            }],
        };
        let handler_def = HandlerDef {
            result_type: I64,
            clauses: vec![HandlerClause {
                protocol: 0,
                operation: 0,
                resumption_type: None,
                callable_signature: clause_signature,
            }],
            partial: false,
        };
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(7)],
            imports: vec![],
            protocols: vec![protocol],
            handler_defs: vec![handler_def],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 21, 22, I64],
                    code_start: 0,
                    code_len: 5,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "clause".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, I64],
                    code_start: 5,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "body".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT],
                    code_start: 8,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::MakeCallable {
                    dst: 1,
                    callable_type: 19,
                    function: 1,
                    captures: vec![],
                },
                Instruction::MakeHandler {
                    dst: 2,
                    handler_def: 0,
                    clauses: vec![1],
                },
                Instruction::MakeCallable {
                    dst: 3,
                    callable_type: 22,
                    function: 2,
                    captures: vec![],
                },
                Instruction::Handle {
                    dst: 4,
                    handler: 2,
                    body: 3,
                    args: vec![],
                },
                Instruction::Return { src: Some(4) },
                Instruction::Drop { register: 0 },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
                Instruction::Drop { register: 0 },
                Instruction::Perform {
                    dst: None,
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
            ],
            required_features: 1 | (1 << 3),
            entry_function: None,
        };
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(decoded.protocols, artifact.protocols);
        assert_eq!(decoded.handler_defs, artifact.handler_defs);
        assert_eq!(decoded.types, artifact.types);
        assert_eq!(decoded.code, artifact.code);
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::I64(7)
        );
    }

    #[test]
    fn reusable_handler_clause_survives_repeated_deep_resumptions() {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: Some(1),
            identity_name: "Ask continuation".into(),
            copy: false,
        });
        let clause_signature = Signature {
            params: vec![19],
            result: I64,
            outward_protocols: vec![],
        };
        types.push(Type::Callable {
            signature: clause_signature.clone(),
            capture_type: UNIT,
            receiver_mode: 0,
            identity_name: "Ask clause".into(),
            copy: false,
            zero_use_allowed: true,
        });
        types.push(Type::Tuple {
            fields: vec![20],
            copy: false,
        });
        types.push(Type::Handler {
            handler_def: 0,
            capture_type: 21,
            identity_name: "Ask handler".into(),
        });
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![0],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "Ask body".into(),
            copy: false,
            zero_use_allowed: true,
        });
        types.push(Type::RefShared { referent: UNIT });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(40)],
            imports: vec![],
            protocols: vec![Protocol {
                display_name: "Ask".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "ask".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    resumption_lower: 1,
                    resumption_upper: Some(1),
                    terminal: false,
                }],
            }],
            handler_defs: vec![HandlerDef {
                result_type: I64,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: Some(19),
                    callable_signature: clause_signature,
                }],
                partial: false,
            }],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "main".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 20, 22, 23, I64],
                    code_start: 0,
                    code_len: 5,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "ask clause".into(),
                    params: vec![19],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: Some(0),
                    register_types: vec![24, 19, I64, I64],
                    code_start: 5,
                    code_len: 4,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "ask body".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, I64, I64, I64],
                    code_start: 9,
                    code_len: 5,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::MakeCallable {
                    dst: 1,
                    callable_type: 20,
                    function: 1,
                    captures: vec![],
                },
                Instruction::MakeHandler {
                    dst: 2,
                    handler_def: 0,
                    clauses: vec![1],
                },
                Instruction::MakeCallable {
                    dst: 3,
                    callable_type: 23,
                    function: 2,
                    captures: vec![],
                },
                Instruction::Handle {
                    dst: 4,
                    handler: 2,
                    body: 3,
                    args: vec![],
                },
                Instruction::Return { src: Some(4) },
                Instruction::Drop { register: 0 },
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Resume {
                    dst: 3,
                    resumption: 1,
                    receiver_mode: 2,
                    value: 2,
                },
                Instruction::Return { src: Some(3) },
                Instruction::Drop { register: 0 },
                Instruction::Perform {
                    dst: Some(1),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Perform {
                    dst: Some(2),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Primitive {
                    dst: 3,
                    op: Primitive::IntCheckedAdd,
                    args: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1 | (1 << 1) | (1 << 3),
            entry_function: None,
        };
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(decoded.types, artifact.types);
        assert_eq!(decoded.code, artifact.code);
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::I64(80)
        );

        let mut unique = artifact.clone();
        unique.types.push(Type::RefUnique { referent: UNIT });
        let Type::Callable { receiver_mode, .. } = &mut unique.types[20] else {
            unreachable!()
        };
        *receiver_mode = 1;
        unique.functions[1].receiver_mode = Some(1);
        unique.functions[1].register_types[0] = 25;
        assert_eq!(
            Vm::from_artifact(Artifact::decode(&unique.encode()).unwrap())
                .unwrap()
                .run(0, vec![])
                .unwrap(),
            Value::I64(80)
        );

        let mut invalid_move = artifact;
        let Type::Callable { receiver_mode, .. } = &mut invalid_move.types[20] else {
            unreachable!()
        };
        *receiver_mode = 2;
        invalid_move.functions[1].receiver_mode = Some(2);
        invalid_move.functions[1].register_types[0] = UNIT;
        assert!(matches!(
            verify(invalid_move),
            Err(VerifyError::InvalidType(20))
        ));
    }

    #[test]
    fn partial_handler_miss_continues_to_the_outward_delimiter() {
        let signature = Signature {
            params: vec![],
            result: I64,
            outward_protocols: vec![],
        };
        let mut types = Type::predefined();
        types.push(Type::Callable {
            signature: signature.clone(),
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "terminal clause".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let artifact = Artifact {
            types,
            protocols: vec![Protocol {
                display_name: "Stop".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "stop".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: NEVER,
                        outward_protocols: vec![],
                    },
                    result_type: NEVER,
                    resumption_lower: 0,
                    resumption_upper: Some(0),
                    terminal: true,
                }],
            }],
            handler_defs: vec![
                HandlerDef {
                    result_type: I64,
                    clauses: vec![],
                    partial: true,
                },
                HandlerDef {
                    result_type: I64,
                    clauses: vec![HandlerClause {
                        protocol: 0,
                        operation: 0,
                        resumption_type: None,
                        callable_signature: signature,
                    }],
                    partial: false,
                },
            ],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "terminal clause".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![UNIT],
                code_start: 0,
                code_len: 0,
                label_slot_count: 0,
            }],
            ..Artifact::default()
        };
        let callable = Value::Callable(ControlHandle::new(CallableValue {
            callable_type: 19,
            function: 0,
            capture: ArenaObject::new(Some(Value::Unit)),
        }));
        let handler = |handler_def, clauses| {
            Value::Handler(ControlHandle::new(HandlerValue {
                handler_type: UNIT,
                handler_def,
                clauses,
            }))
        };
        let mut stack = vec![
            RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![],
                return_dst: None,
                delimiter: Some(handler(1, vec![Some(callable)])),
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            },
            RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![],
                return_dst: None,
                delimiter: Some(handler(0, vec![])),
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            },
        ];
        let selected = select_handler_clause(&image(artifact.clone()), &mut stack, 0, 0).unwrap();
        assert_eq!(selected.delimiter, 0);
        assert_eq!(selected.receiver_mode, 2);
    }

    #[test]
    fn move_then_cancel_consumes_a_zero_lower_bound_resumption_and_destroys_its_frames() {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: UNIT,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 0,
            upper_uses: Some(1),
            identity_name: "cancelable continuation".into(),
            copy: false,
        });
        let artifact = Artifact {
            types,
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "cancel".into(),
                params: vec![19],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 19, UNIT],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Move { dst: 2, src: 1 },
                Instruction::Cancel {
                    dst: 3,
                    resumption: 2,
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1 | (1 << 3),
            ..Artifact::default()
        };
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        let resumption = Value::Resumption(ControlHandle::new(Some(ResumptionValue {
            resumption_type: 19,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![Some(Value::Unit), None, None, None],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
        })));
        assert_eq!(
            Vm::from_artifact(decoded)
                .unwrap()
                .run(0, vec![resumption])
                .unwrap(),
            Value::Unit
        );
    }

    #[test]
    fn binding_pack_uses_payload_layout_and_available_is_erased_from_registers() {
        let mut types = Type::predefined();
        types.push(Type::Available {
            identity_name: "compile-time witness".into(),
        });
        types.push(
            Type::Tuple {
                fields: vec![19, I64, 19],
                copy: true,
            }
            .restricted(true, true),
        );
        types.push(
            Type::BindingPack {
                payload_type: 20,
                identity_name: "refinement bindings".into(),
                copy: true,
            }
            .restricted(true, true),
        );
        let artifact = Artifact {
            types,
            constants: vec![Constant::Unit, Constant::I64(5)],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "bindings".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, 21, 21, UNIT],
                code_start: 0,
                code_len: 7,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 1,
                },
                Instruction::MakeBindingPack {
                    dst: 2,
                    binding_type: 21,
                    payloads: vec![1],
                },
                Instruction::Copy { dst: 3, src: 2 },
                Instruction::Drop { register: 2 },
                Instruction::Drop { register: 3 },
                Instruction::Const {
                    dst: 4,
                    constant: 0,
                },
                Instruction::Return { src: Some(4) },
            ],
            ..Artifact::default()
        };
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(decoded.types, artifact.types);
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::Unit
        );

        let mut invalid = artifact;
        invalid.functions[0].register_types[1] = 19;
        assert!(Vm::from_artifact(invalid).is_err());
    }

    #[test]
    fn construct_omits_available_fields_but_keeps_nominal_projection_indices() {
        let mut types = Type::predefined();
        types.push(Type::Available {
            identity_name: "erased field".into(),
        });
        types.push(
            Type::Struct {
                name: "WitnessedValue".into(),
                fields: vec![
                    Field {
                        name: "witness".into(),
                        ty: 19,
                    },
                    Field {
                        name: "value".into(),
                        ty: I64,
                    },
                ],
                copy: false,
            }
            .restricted(false, true),
        );
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(42)],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "construct erased field".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, 20, I64],
                code_start: 0,
                code_len: 5,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 2,
                    ty: 20,
                    variant: None,
                    fields: vec![1],
                },
                Instruction::ProjectMove {
                    dst: 3,
                    src: 2,
                    field: 1,
                },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(3) },
            ],
            ..Artifact::default()
        };

        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(decoded.code, artifact.code);
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]).unwrap(),
            Value::I64(42)
        );
    }

    #[test]
    fn abort_message_roundtrips_and_terminates_without_a_normal_return() {
        let artifact = Artifact {
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "aborter".into(),
                params: vec![],
                return_type: NEVER,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            }],
            code: vec![Instruction::Abort {
                message: Some("deliberate stop".into()),
            }],
            ..Artifact::default()
        };
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(decoded.code, artifact.code);
        assert_eq!(
            Vm::from_artifact(decoded).unwrap().run(0, vec![]),
            Err(RuntimeError::Aborted(Some("deliberate stop".into())))
        );
    }

    #[test]
    fn leave_protects_a_noncopy_aggregate_and_destroys_only_the_cleanup_prefix() {
        let mut types = Type::predefined();
        types.push(
            Type::Struct {
                name: "Pair".into(),
                fields: vec![
                    Field {
                        name: "left".into(),
                        ty: I64,
                    },
                    Field {
                        name: "right".into(),
                        ty: I64,
                    },
                ],
                copy: false,
            }
            .restricted(false, true),
        );
        let artifact = Artifact {
            types,
            constants: vec![
                Constant::I64(20),
                Constant::I64(22),
                Constant::I64(1),
                Constant::I64(2),
            ],
            cleanups: vec![
                CleanupPlan {
                    function: 0,
                    first_instruction: 0,
                    end_instruction: 1,
                    registers: vec![],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 1,
                    end_instruction: 2,
                    registers: vec![1],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 2,
                    end_instruction: 3,
                    registers: vec![2, 1],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 3,
                    end_instruction: 4,
                    registers: vec![3],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 4,
                    end_instruction: 5,
                    registers: vec![4, 3],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 5,
                    end_instruction: 6,
                    registers: vec![5, 4, 3],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 6,
                    end_instruction: 7,
                    registers: vec![3, 6],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 7,
                    end_instruction: 8,
                    registers: vec![3, 7, 6],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 8,
                    end_instruction: 9,
                    registers: vec![],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 9,
                    end_instruction: 10,
                    registers: vec![7, 6],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 10,
                    end_instruction: 11,
                    registers: vec![8, 7, 6],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 11,
                    end_instruction: 12,
                    registers: vec![8, 6],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 12,
                    end_instruction: 13,
                    registers: vec![8],
                },
            ],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "leave_pair".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, I64, 19, I64, I64, 19, 19, I64],
                code_start: 0,
                code_len: 13,
                label_slot_count: 1,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 1,
                },
                Instruction::Construct {
                    dst: 3,
                    ty: 19,
                    variant: None,
                    fields: vec![1, 2],
                },
                Instruction::Const {
                    dst: 4,
                    constant: 2,
                },
                Instruction::Const {
                    dst: 5,
                    constant: 3,
                },
                Instruction::Construct {
                    dst: 6,
                    ty: 19,
                    variant: None,
                    fields: vec![4, 5],
                },
                Instruction::LabelPush {
                    slot: 0,
                    result_register: 7,
                    target: 9,
                },
                Instruction::Leave { slot: 0, value: 3 },
                Instruction::LabelPop { slot: 0 },
                Instruction::ProjectMove {
                    dst: 8,
                    src: 7,
                    field: 1,
                },
                Instruction::Drop { register: 7 },
                Instruction::Drop { register: 6 },
                Instruction::Return { src: Some(8) },
            ],
            required_features: 1 | (1 << 2),
            ..Artifact::default()
        };

        assert_eq!(
            Vm::from_artifact(artifact).unwrap().run(0, vec![]).unwrap(),
            Value::I64(22)
        );
    }

    #[test]
    fn const_executes_every_scalar_runtime_representation() {
        let cases = vec![
            (Constant::U8(0xff), U8, Value::U64(0xff)),
            (Constant::U16(0x1234), U16, Value::U64(0x1234)),
            (Constant::U128(u128::MAX), U128, Value::U128(u128::MAX)),
            (Constant::I8(-2), I8, Value::I64(-2)),
            (Constant::I16(-0x1234), I16, Value::I64(-0x1234)),
            (Constant::I32(-0x1234567), I32, Value::I64(-0x1234567)),
            (Constant::I128(i128::MIN), I128, Value::I128(i128::MIN)),
            (Constant::Usize(u64::MAX), USIZE, Value::U64(u64::MAX)),
            (Constant::Isize(i64::MIN), ISIZE, Value::I64(i64::MIN)),
            (Constant::F32(-0.0), F32, Value::F32(-0.0)),
            (Constant::Char('\u{1f600}'), CHAR, Value::U64(0x1f600)),
        ];

        for (constant, ty, expected) in cases {
            let artifact = Artifact {
                constants: vec![constant],
                reference_return_contracts: vec![],
                functions: vec![Function {
                    flags: 0,
                    name: "scalar_constant".into(),
                    params: vec![],
                    return_type: ty,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, ty],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                }],
                code: vec![
                    Instruction::Const {
                        dst: 1,
                        constant: 0,
                    },
                    Instruction::Return { src: Some(1) },
                ],
                ..Artifact::default()
            };

            assert_eq!(
                Vm::from_artifact(artifact).unwrap().run(0, vec![]).unwrap(),
                expected
            );
        }
    }

    #[derive(Default)]
    struct MockHost {
        args: Vec<String>,
        diagnostic_fault: Option<String>,
    }

    impl Host for MockHost {
        fn process_args(&self) -> Result<Vec<String>, HostFault> {
            Ok(self.args.clone())
        }

        fn fs_read(&self, _path: String) -> Result<Vec<u8>, HostFault> {
            Err(HostFault::new("unexpected fs.read"))
        }

        fn fs_write(&self, _path: String, _contents: Vec<u8>) -> Result<(), HostFault> {
            Err(HostFault::new("unexpected fs.write"))
        }

        fn diagnostic_write(&self, _message: String) -> Result<(), HostFault> {
            match &self.diagnostic_fault {
                Some(message) => Err(HostFault::new(message.clone())),
                None => Ok(()),
            }
        }
    }

    fn process_args_artifact() -> Artifact {
        let mut artifact = Artifact {
            required_features: 1 | (1 << 5),
            ..Artifact::default()
        };
        artifact.types.push(Type::Array { element: TEXT });
        artifact.imports.push(Import {
            capability: "process.args".into(),
            symbol: "get".into(),
            signature: crate::bytecode::Signature {
                params: vec![],
                result: 19,
                outward_protocols: vec![],
            },
            may_trap: true,
        });
        artifact.functions.push(Function {
            flags: 0,
            name: "args".into(),
            params: vec![],
            return_type: 19,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 19],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        });
        artifact.code = vec![
            Instruction::HostCall {
                dst: Some(1),
                import: 0,
                args: vec![],
            },
            Instruction::Return { src: Some(1) },
        ];
        artifact
    }

    #[test]
    fn links_and_invokes_process_args_through_typed_host() {
        let artifact = verify(process_args_artifact()).unwrap();
        let vm = Vm::with_host(
            artifact,
            ["process.args"],
            MockHost {
                args: vec!["one".into(), "two".into()],
                ..MockHost::default()
            },
        )
        .unwrap();

        assert_eq!(
            vm.run(0, vec![]).unwrap(),
            Value::array(TEXT, [Value::Text("one".into()), Value::Text("two".into())])
        );
    }

    #[test]
    fn host_imports_are_rejected_before_entry_when_denied_or_mistyped() {
        let artifact = verify(process_args_artifact()).unwrap();
        assert!(matches!(
            Vm::with_host(artifact, [] as [&str; 0], MockHost::default()),
            Err(HostLinkError::DeniedCapability(capability)) if capability == "process.args"
        ));

        let mut cannot_trap = process_args_artifact();
        cannot_trap.imports[0].may_trap = false;
        let cannot_trap = verify(cannot_trap).unwrap();
        assert!(matches!(
            Vm::with_host(cannot_trap, ["process.args"], MockHost::default()),
            Err(HostLinkError::MissingMayTrap { capability, symbol })
                if capability == "process.args" && symbol == "get"
        ));

        let mut wrong = process_args_artifact();
        wrong.imports[0].signature.result = BYTES;
        wrong.functions[0].register_types[1] = BYTES;
        wrong.functions[0].return_type = BYTES;
        let wrong = verify(wrong).unwrap();
        assert!(matches!(
            Vm::with_host(wrong, ["process.args"], MockHost::default()),
            Err(HostLinkError::SignatureMismatch { capability, symbol })
                if capability == "process.args" && symbol == "get"
        ));
    }

    #[test]
    fn host_fault_is_distinct_and_stops_execution() {
        let artifact = Artifact {
            required_features: 1 | (1 << 5),
            constants: vec![Constant::Text("bad news".into()), Constant::Unit],
            imports: vec![Import {
                capability: "diagnostic".into(),
                symbol: "write".into(),
                signature: crate::bytecode::Signature {
                    params: vec![TEXT],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                may_trap: true,
            }],
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "diagnostic".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, TEXT, UNIT],
                code_start: 0,
                code_len: 4,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::HostCall {
                    dst: None,
                    import: 0,
                    args: vec![1],
                },
                Instruction::Const {
                    dst: 2,
                    constant: 1,
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        let vm = Vm::with_host(
            verify(artifact).unwrap(),
            ["diagnostic"],
            MockHost {
                diagnostic_fault: Some("broken pipe".into()),
                ..MockHost::default()
            },
        )
        .unwrap();

        assert_eq!(
            vm.run(0, vec![]),
            Err(RuntimeError::HostFault(HostFault::new("broken pipe")))
        );
    }

    #[test]
    fn shared_and_unique_multishot_resumes_reuse_the_pristine_snapshot() {
        for receiver_mode in [0, 1] {
            let mut types = Type::predefined();
            types.push(Type::Resumption {
                input_type: I64,
                output_type: I64,
                effect_signature: Signature {
                    params: vec![],
                    result: I64,
                    outward_protocols: vec![],
                },
                lower_uses: 2,
                upper_uses: Some(2),
                identity_name: "twice".into(),
                copy: true,
            });
            let protocol = Protocol {
                display_name: "Twice".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "yield".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    terminal: false,
                    resumption_lower: 2,
                    resumption_upper: Some(2),
                }],
            };
            let artifact = Artifact {
                types,
                constants: vec![],
                protocols: vec![protocol],
                reference_return_contracts: vec![],
                functions: vec![
                    Function {
                        flags: 0,
                        name: "captured".into(),
                        params: vec![],
                        return_type: I64,
                        outward_protocols: vec![0],
                        receiver_mode: None,
                        register_types: vec![UNIT, I64],
                        code_start: 0,
                        code_len: 2,
                        label_slot_count: 0,
                    },
                    Function {
                        flags: 0,
                        name: "resume_twice".into(),
                        params: vec![19, I64, I64],
                        return_type: I64,
                        outward_protocols: vec![],
                        receiver_mode: None,
                        register_types: vec![UNIT, 19, I64, I64, I64, I64, I64],
                        code_start: 2,
                        code_len: 4,
                        label_slot_count: 0,
                    },
                ],
                code: vec![
                    Instruction::Perform {
                        dst: Some(1),
                        protocol: 0,
                        operation: 0,
                        payloads: vec![],
                    },
                    Instruction::Return { src: Some(1) },
                    Instruction::Resume {
                        dst: 4,
                        resumption: 1,
                        receiver_mode,
                        value: 2,
                    },
                    Instruction::Resume {
                        dst: 5,
                        resumption: 1,
                        receiver_mode: 2,
                        value: 3,
                    },
                    Instruction::Primitive {
                        dst: 6,
                        op: Primitive::IntCheckedAdd,
                        args: vec![4, 5],
                    },
                    Instruction::Return { src: Some(6) },
                ],
                required_features: 1 | (1 << 3) | (1 << 4),
                ..Artifact::default()
            };
            let captured = Value::Resumption(ControlHandle::new(Some(ResumptionValue {
                resumption_type: 19,
                frames: vec![RuntimeFrame {
                    function: 0,
                    pc: 1,
                    registers: vec![Some(Value::Unit), None],
                    return_dst: None,
                    delimiter: None,
                    guards: vec![],
                    deferred_frames: vec![],
                    labels: vec![],
                }],
            })));
            assert_eq!(
                Vm::from_artifact(artifact)
                    .unwrap()
                    .run(1, vec![captured, Value::I64(20), Value::I64(22)])
                    .unwrap(),
                Value::I64(42)
            );
        }
    }

    #[test]
    fn tail_resume_replaces_the_current_frame_and_returns_to_its_caller() {
        let mut types = Type::predefined();
        let resumption_type = types.len() as u32;
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: Some(1),
            identity_name: "tail continuation".into(),
            copy: false,
        });
        let artifact = Artifact {
            types,
            protocols: vec![Protocol {
                display_name: "Tail".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "yield".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    terminal: false,
                    resumption_lower: 1,
                    resumption_upper: Some(1),
                }],
            }],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "captured".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![0],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "tail_resume".into(),
                    params: vec![resumption_type, I64],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, resumption_type, I64],
                    code_start: 2,
                    code_len: 1,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Perform {
                    dst: Some(1),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Return { src: Some(1) },
                Instruction::TailResume {
                    resumption: 1,
                    receiver_mode: 2,
                    value: 2,
                },
            ],
            required_features: 1 | (1 << 3),
            ..Artifact::default()
        };
        let captured = Value::Resumption(ControlHandle::new(Some(ResumptionValue {
            resumption_type,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 1,
                registers: vec![Some(Value::Unit), None],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
        })));

        let mut borrowed_one_shot = artifact.clone();
        let Instruction::TailResume { receiver_mode, .. } = &mut borrowed_one_shot.code[2] else {
            unreachable!()
        };
        *receiver_mode = 0;
        assert!(verify(borrowed_one_shot).is_err());

        let mut wrong_tail_result = artifact.clone();
        wrong_tail_result.functions[1].return_type = UNIT;
        assert!(verify(wrong_tail_result).is_err());

        assert_eq!(
            Vm::from_artifact(artifact)
                .unwrap()
                .run(1, vec![captured, Value::I64(42)])
                .unwrap(),
            Value::I64(42)
        );
    }

    #[test]
    fn tail_resume_transfers_deferred_reference_owners_to_the_resumed_frame() {
        let artifact = Artifact {
            functions: vec![Function {
                flags: 0,
                name: "deferred_owner".into(),
                params: vec![I64],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Drop { register: 1 },
                Instruction::Return { src: None },
            ],
            ..Artifact::default()
        };
        let vm = Vm::new(verify(artifact).unwrap());
        let owner = vm.slots.insert(Some(Value::I64(42))).unwrap();
        let mut current = RuntimeFrame {
            function: 0,
            pc: 1,
            registers: vec![Some(Value::Unit), None],
            return_dst: None,
            delimiter: None,
            guards: vec![],
            deferred_frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![Some(Value::Unit), Some(Value::Place(owner.clone()))],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
            labels: vec![],
        };
        let mut resumed = RuntimeFrame {
            function: 0,
            pc: 1,
            registers: vec![Some(Value::Unit), None],
            return_dst: None,
            delimiter: None,
            guards: vec![],
            deferred_frames: vec![],
            labels: vec![],
        };

        transfer_tail_resume_deferred_frames(&mut current, &mut resumed);
        vm.destroy_frame(current).unwrap();
        assert_eq!(owner.get(), Ok(Value::I64(42)));
        assert_eq!(resumed.deferred_frames.len(), 1);

        vm.destroy_frame(resumed).unwrap();
        assert!(owner.get().is_err());
    }

    #[test]
    fn copied_multishot_resumptions_are_independent_pristine_snapshots() {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: Some(2),
            identity_name: "copyable continuation".into(),
            copy: true,
        });
        let artifact = Artifact {
            types,
            protocols: vec![Protocol {
                display_name: "Copyable".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "yield".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    terminal: false,
                    resumption_lower: 1,
                    resumption_upper: Some(2),
                }],
            }],
            reference_return_contracts: vec![],
            functions: vec![
                Function {
                    flags: 0,
                    name: "captured".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![0],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "copy_and_resume".into(),
                    params: vec![19, I64, I64],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, I64, I64, 19, I64, I64, I64],
                    code_start: 2,
                    code_len: 5,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Perform {
                    dst: Some(1),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Return { src: Some(1) },
                Instruction::Copy { dst: 4, src: 1 },
                Instruction::Resume {
                    dst: 5,
                    resumption: 1,
                    receiver_mode: 2,
                    value: 2,
                },
                Instruction::Resume {
                    dst: 6,
                    resumption: 4,
                    receiver_mode: 2,
                    value: 3,
                },
                Instruction::Primitive {
                    dst: 7,
                    op: Primitive::IntCheckedAdd,
                    args: vec![5, 6],
                },
                Instruction::Return { src: Some(7) },
            ],
            required_features: 1 | (1 << 3) | (1 << 4),
            ..Artifact::default()
        };
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        let captured = Value::Resumption(ControlHandle::new(Some(ResumptionValue {
            resumption_type: 19,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 1,
                registers: vec![Some(Value::Unit), None],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
        })));
        assert_eq!(
            Vm::from_artifact(decoded)
                .unwrap()
                .run(1, vec![captured, Value::I64(20), Value::I64(22)])
                .unwrap(),
            Value::I64(42)
        );
    }

    #[test]
    fn handler_snapshot_preserves_shared_environment_identity_per_replay() {
        let mut types = Type::predefined();
        types.extend([
            Type::Tuple {
                fields: vec![I64],
                copy: false,
            },
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: 19,
                receiver_mode: 0,
                identity_name: "resumptive clause".into(),
                copy: true,
                zero_use_allowed: true,
            },
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: 19,
                receiver_mode: 2,
                identity_name: "terminal clause".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Tuple {
                fields: vec![20, 21],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 22,
                identity_name: "mixed handler".into(),
            },
        ]);
        let artifact = Artifact {
            types,
            reference_return_contracts: vec![],
            functions: vec![Function {
                flags: 0,
                name: "captured".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            }],
            code: vec![Instruction::Return { src: None }],
            ..Artifact::default()
        };
        let shared = ArenaObject::new(Some(Value::aggregate(19, [Value::I64(7)])));
        let callable = |callable_type, function| {
            Some(Value::Callable(ControlHandle::new(CallableValue {
                callable_type,
                function,
                capture: shared.clone(),
            })))
        };
        let handler = Value::Handler(ControlHandle::new(HandlerValue {
            handler_type: 23,
            handler_def: 0,
            clauses: vec![callable(20, 0), callable(21, 0)],
        }));
        let source = ResumptionValue {
            resumption_type: UNIT,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![Some(Value::Unit)],
                return_dst: None,
                delimiter: Some(handler),
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
        };

        let first = clone_resumption_snapshot(&image(artifact.clone()), &source).unwrap();
        let second = clone_resumption_snapshot(&image(artifact.clone()), &source).unwrap();
        let captures = |snapshot: &ResumptionValue| {
            let Value::Handler(handler) = snapshot.frames[0].delimiter.as_ref().unwrap() else {
                panic!("snapshot delimiter is not a handler")
            };
            let handler = handler.borrow();
            let capture = |index: usize| {
                let Value::Callable(callable) =
                    handler.clauses[index].as_ref().expect("live clause")
                else {
                    panic!("handler clause is not callable")
                };
                callable.capture()
            };
            (capture(0), capture(1))
        };
        let (first_resumptive, first_terminal) = captures(&first);
        let (second_resumptive, second_terminal) = captures(&second);

        assert!(ArenaObject::ptr_eq(&first_resumptive, &first_terminal));
        assert!(ArenaObject::ptr_eq(&second_resumptive, &second_terminal));
        assert!(!ArenaObject::ptr_eq(&first_resumptive, &second_resumptive));
        assert!(!ArenaObject::ptr_eq(&first_resumptive, &shared));

        *first_resumptive.borrow_mut() = Some(Value::aggregate(19, [Value::I64(99)]));
        let second_value = second_resumptive.borrow();
        let Some(Value::Aggregate(environment)) = second_value.as_ref() else {
            panic!("second replay lost its environment")
        };
        assert!(matches!(
            environment.borrow().fields[0],
            Some(Value::I64(7))
        ));
    }

    #[test]
    fn snapshot_clone_keeps_array_and_aggregate_mutations_independent() {
        let mut artifact = Artifact::default();
        artifact.types.push(Type::Array { element: I64 });
        artifact.types.push(Type::Struct {
            name: "BoxedArray".into(),
            fields: vec![Field {
                name: "items".into(),
                ty: 19,
            }],
            copy: false,
        });
        artifact.functions.push(Function {
            flags: 0,
            name: "snapshot".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 20, I64],
            code_start: 0,
            code_len: 1,
            label_slot_count: 0,
        });
        let array = Value::Array(ArenaObject::new(ArrayValue {
            element_type: I64,
            slots: vec![None, Some(Value::I64(1))],
            logical_capacity: 2,
        }));
        let aggregate = Value::aggregate(20, [array]);
        let ended_borrow_place = SlotStore::default().insert(Some(Value::I64(7))).unwrap();
        let source = ResumptionValue {
            resumption_type: UNIT,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![
                    Some(Value::Unit),
                    Some(aggregate),
                    Some(Value::Place(ended_borrow_place)),
                ],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
        };
        let first = clone_resumption_snapshot(&image(artifact.clone()), &source).unwrap();
        let second = clone_resumption_snapshot(&image(artifact.clone()), &source).unwrap();
        let Some(Value::Place(first_place)) = &first.frames[0].registers[2] else {
            panic!("first cloned place")
        };
        let Some(Value::Place(second_place)) = &second.frames[0].registers[2] else {
            panic!("second cloned place")
        };
        assert_eq!(first_place.get(), Ok(Value::I64(7)));
        assert_eq!(second_place.get(), Ok(Value::I64(7)));
        assert_ne!(first_place, second_place);
        let Value::Aggregate(first_aggregate) = first.frames[0].registers[1].as_ref().unwrap()
        else {
            panic!("aggregate clone")
        };
        let Value::Array(first_array) =
            first_aggregate.borrow().fields[0].as_ref().unwrap().clone()
        else {
            panic!("array clone")
        };
        assert_eq!(first_array.borrow().slots[0], None);
        first_array.borrow_mut().slots[1] = Some(Value::I64(99));
        let Value::Aggregate(second_aggregate) = second.frames[0].registers[1].as_ref().unwrap()
        else {
            panic!("aggregate clone")
        };
        let second_aggregate = second_aggregate.borrow();
        let Value::Array(second_array) = second_aggregate.fields[0].as_ref().unwrap() else {
            panic!("array clone")
        };
        assert_eq!(second_array.borrow().slots[0], None);
        assert_eq!(second_array.borrow().slots[1], Some(Value::I64(1)));
    }

    #[test]
    fn snapshot_clone_remaps_internal_shared_aliases_and_retains_external_targets() {
        let mut artifact = Artifact::default();
        artifact.types.push(Type::RefShared { referent: I64 });
        artifact.types.push(Type::Struct {
            name: "Pair".into(),
            fields: vec![
                Field {
                    name: "left".into(),
                    ty: I64,
                },
                Field {
                    name: "right".into(),
                    ty: I64,
                },
            ],
            copy: false,
        });
        artifact.types.push(Type::Struct {
            name: "SharedEnvelope".into(),
            fields: vec![Field {
                name: "reference".into(),
                ty: 19,
            }],
            copy: true,
        });
        artifact.functions.push(Function {
            flags: 0,
            name: "snapshot_aliases".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, I64, 19, 19, 20, 19, 19, 21],
            code_start: 0,
            code_len: 1,
            label_slot_count: 0,
        });

        let slots = SlotStore::default();
        let owner = slots.insert(Some(Value::I64(40))).unwrap();
        let aggregate = match Value::aggregate(20, [Value::I64(41), Value::I64(0)]) {
            Value::Aggregate(aggregate) => aggregate,
            _ => unreachable!(),
        };
        let external = slots.insert(Some(Value::I64(42))).unwrap();
        let shared = |target| Value::Reference {
            referent_type: I64,
            unique: false,
            target,
        };
        let source = ResumptionValue {
            resumption_type: UNIT,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![
                    Some(Value::Unit),
                    Some(Value::Place(owner.clone())),
                    Some(shared(ReferenceTarget::WholePlace(owner.clone()))),
                    Some(shared(ReferenceTarget::WholePlace(owner.clone()))),
                    Some(Value::Aggregate(aggregate.clone())),
                    Some(shared(ReferenceTarget::AggregateField {
                        aggregate: aggregate.clone(),
                        field: 0,
                    })),
                    Some(shared(ReferenceTarget::WholePlace(external.clone()))),
                    Some(Value::aggregate(
                        21,
                        [shared(ReferenceTarget::WholePlace(owner.clone()))],
                    )),
                ],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
        };

        let first = clone_resumption_snapshot(&image(artifact.clone()), &source).unwrap();
        let second = clone_resumption_snapshot(&image(artifact.clone()), &source).unwrap();
        let first_registers = &first.frames[0].registers;
        let second_registers = &second.frames[0].registers;
        let Some(Value::Place(first_owner)) = &first_registers[1] else {
            panic!("first owner place")
        };
        let Some(Value::Place(second_owner)) = &second_registers[1] else {
            panic!("second owner place")
        };
        assert_ne!(first_owner, &owner);
        assert_ne!(first_owner, second_owner);
        for register in [2, 3] {
            let Some(Value::Reference {
                target: ReferenceTarget::WholePlace(target),
                ..
            }) = &first_registers[register]
            else {
                panic!("whole shared alias")
            };
            assert_eq!(target, first_owner);
        }
        let Some(Value::Aggregate(first_aggregate)) = &first_registers[4] else {
            panic!("first aggregate")
        };
        let Some(Value::Reference {
            target:
                ReferenceTarget::AggregateField {
                    aggregate: target,
                    field: 0,
                },
            ..
        }) = &first_registers[5]
        else {
            panic!("projected shared alias")
        };
        assert!(ArenaObject::ptr_eq(target, first_aggregate));
        let Some(Value::Reference {
            target: ReferenceTarget::WholePlace(target),
            ..
        }) = &first_registers[6]
        else {
            panic!("external shared alias")
        };
        assert_eq!(target, &external);
        let Some(Value::Aggregate(envelope)) = &first_registers[7] else {
            panic!("shared-reference envelope")
        };
        let envelope = envelope.borrow();
        let Some(Value::Reference {
            target: ReferenceTarget::WholePlace(target),
            ..
        }) = &envelope.fields[0]
        else {
            panic!("nested shared alias")
        };
        assert_eq!(target, first_owner);

        assert_eq!(first_owner.take(), Ok(Value::I64(40)));
        first_owner.put(Value::I64(99)).unwrap();
        assert_eq!(second_owner.get(), Ok(Value::I64(40)));
        assert_eq!(owner.get(), Ok(Value::I64(40)));
    }

    #[test]
    fn snapshot_clone_remaps_references_into_deferred_terminal_frames() {
        let mut artifact = Artifact::default();
        artifact.types.push(Type::RefShared { referent: I64 });
        artifact.functions.push(Function {
            flags: 0,
            name: "terminal_clause".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 19],
            code_start: 0,
            code_len: 1,
            label_slot_count: 0,
        });
        artifact.functions.push(Function {
            flags: 0,
            name: "abandoned_body".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, I64],
            code_start: 0,
            code_len: 1,
            label_slot_count: 0,
        });

        let owner = SlotStore::default().insert(Some(Value::I64(42))).unwrap();
        let source = ResumptionValue {
            resumption_type: UNIT,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![
                    Some(Value::Unit),
                    Some(Value::Reference {
                        referent_type: I64,
                        unique: false,
                        target: ReferenceTarget::WholePlace(owner.clone()),
                    }),
                ],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![RuntimeFrame {
                    function: 1,
                    pc: 0,
                    registers: vec![Some(Value::Unit), Some(Value::Place(owner.clone()))],
                    return_dst: None,
                    delimiter: None,
                    guards: vec![],
                    deferred_frames: vec![],
                    labels: vec![],
                }],
                labels: vec![],
            }],
        };

        let first = clone_resumption_snapshot(&image(artifact.clone()), &source).unwrap();
        let second = clone_resumption_snapshot(&image(artifact), &source).unwrap();
        let cloned_owner = |snapshot: &ResumptionValue| {
            let Some(Value::Place(owner)) = &snapshot.frames[0].deferred_frames[0].registers[1]
            else {
                panic!("deferred owner place")
            };
            owner.clone()
        };
        let cloned_target = |snapshot: &ResumptionValue| {
            let Some(Value::Reference {
                target: ReferenceTarget::WholePlace(target),
                ..
            }) = &snapshot.frames[0].registers[1]
            else {
                panic!("terminal payload reference")
            };
            target.clone()
        };
        assert_eq!(cloned_target(&first), cloned_owner(&first));
        assert_eq!(cloned_target(&second), cloned_owner(&second));
        assert_ne!(cloned_owner(&first), cloned_owner(&second));
        assert_ne!(cloned_owner(&first), owner);
        assert_eq!(cloned_owner(&first).get(), Ok(Value::I64(42)));
        assert_eq!(cloned_owner(&second).get(), Ok(Value::I64(42)));
    }

    #[test]
    fn multishot_validation_recurses_into_deferred_cleanup_frames() {
        let mut artifact = Artifact::default();
        let shared = artifact.types.len() as TypeId;
        artifact.types.push(Type::RefShared { referent: I64 });
        let unique = artifact.types.len() as TypeId;
        artifact.types.push(Type::RefUnique { referent: I64 });
        artifact.functions.extend([
            Function {
                flags: 0,
                name: "captured_clause".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, shared],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "deferred_owner".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, unique],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            },
        ]);
        artifact.code.push(Instruction::Return { src: None });
        let image = image(artifact);
        let slots = SlotStore::default();
        let owner = slots.insert(Some(Value::I64(42))).unwrap();
        let unique_target = slots.insert(Some(Value::I64(7))).unwrap();
        let frame = |unique_reference| RuntimeFrame {
            function: 0,
            pc: 0,
            registers: vec![
                Some(Value::Unit),
                Some(Value::Reference {
                    referent_type: I64,
                    unique: false,
                    target: ReferenceTarget::WholePlace(owner.clone()),
                }),
            ],
            return_dst: None,
            delimiter: None,
            guards: vec![],
            deferred_frames: vec![RuntimeFrame {
                function: 1,
                pc: 0,
                registers: vec![
                    Some(Value::Unit),
                    Some(Value::Place(owner.clone())),
                    unique_reference,
                ],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
            labels: vec![],
        };

        let copy_safe = frame(None);
        SnapshotValidationContext::default()
            .validate_frame(&image, &copy_safe)
            .unwrap();
        assert_eq!(owner.get(), Ok(Value::I64(42)));

        let not_copy_safe = frame(Some(Value::Reference {
            referent_type: I64,
            unique: true,
            target: ReferenceTarget::WholePlace(unique_target),
        }));
        assert!(matches!(
            SnapshotValidationContext::default().validate_frame(&image, &not_copy_safe),
            Err(RuntimeError::TypeConfusion)
        ));
        assert_eq!(owner.get(), Ok(Value::I64(42)));
    }

    #[test]
    fn snapshot_clone_rejects_unique_references() {
        let mut artifact = Artifact::default();
        artifact.types.push(Type::RefUnique { referent: I64 });
        artifact.functions.push(Function {
            flags: 0,
            name: "snapshot_unique".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 19],
            code_start: 0,
            code_len: 1,
            label_slot_count: 0,
        });
        let target = SlotStore::default().insert(Some(Value::I64(1))).unwrap();
        let source = ResumptionValue {
            resumption_type: UNIT,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![
                    Some(Value::Unit),
                    Some(Value::Reference {
                        referent_type: I64,
                        unique: true,
                        target: ReferenceTarget::WholePlace(target),
                    }),
                ],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
        };
        assert!(matches!(
            clone_resumption_snapshot(&image(artifact.clone()), &source),
            Err(RuntimeError::TypeConfusion)
        ));
    }
}
