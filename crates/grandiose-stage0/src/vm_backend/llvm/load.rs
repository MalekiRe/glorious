use super::{
    LlvmError, LlvmExecutionProfile, LlvmIrProgram, NativeContext, VmExecutionLimits, VmType,
};
use std::sync::Arc;
use std::{
    ffi::{CStr, CString, c_char, c_int, c_void},
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

/// Tool invocation is an explicit output action, separate from pure IR
/// construction. No library search or host-capability authority comes from
/// source spelling or from a serialized native address.
#[derive(Clone, Debug)]
pub struct LlvmCompileOptions {
    pub clang: PathBuf,
    pub optimization: u8,
}
impl Default for LlvmCompileOptions {
    fn default() -> Self {
        Self {
            clang: PathBuf::from("clang"),
            optimization: 2,
        }
    }
}

struct OutputDirectory {
    path: PathBuf,
}
impl OutputDirectory {
    fn create() -> Result<Self, LlvmError> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        for _ in 0..256 {
            let path = std::env::temp_dir().join(format!(
                "grandiose-llvm-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let mut builder = std::fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt;
                builder.mode(0o700);
            }
            match builder.create(&path) {
                Ok(()) => return Ok(Self { path }),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error.into()),
            }
        }
        Err(LlvmError::Tool(
            "cannot create a private native output directory".into(),
        ))
    }
}
impl Drop for OutputDirectory {
    fn drop(&mut self) {
        // Only the two exact files created in this exclusively owned directory
        // are removed. Never recursively delete an ambient path or a symlink.
        let _ = std::fs::remove_file(self.path.join("program.ll"));
        let _ = std::fs::remove_file(self.path.join("program.so"));
        let _ = std::fs::remove_dir(&self.path);
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[link(name = "dl")]
unsafe extern "C" {
    fn dlopen(path: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn dlclose(handle: *mut c_void) -> c_int;
    fn dlerror() -> *const c_char;
}

struct Library {
    handle: *mut c_void,
    _directory: OutputDirectory,
}
// SAFETY: this handle owns only our immutable compiler-generated object. Its
// entries take all mutable execution state through per-call context/slots;
// the object has no mutable globals or retained callback state. The final Arc
// closes the handle only after every module/entry invocation has finished.
unsafe impl Send for Library {}
unsafe impl Sync for Library {}
impl Library {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    fn open(directory: OutputDirectory) -> Result<Self, LlvmError> {
        use std::os::unix::ffi::OsStrExt;
        let path = CString::new(directory.path.join("program.so").as_os_str().as_bytes())
            .map_err(|_| LlvmError::Tool("native output path contains NUL".into()))?;
        // SAFETY: this is only the locally compiled output of our immutable IR
        // plan. RTLD_NOW|RTLD_LOCAL performs eager linking without publishing
        // symbols into unrelated execution domains.
        let handle = unsafe { dlopen(path.as_ptr(), 2) };
        if handle.is_null() {
            return Err(loader_error());
        }
        Ok(Self {
            handle,
            _directory: directory,
        })
    }
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    fn open(_: OutputDirectory) -> Result<Self, LlvmError> {
        Err(LlvmError::UnsupportedTarget(
            "native loader requires x86_64 Linux".into(),
        ))
    }

    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    fn symbol(&self, name: &CStr) -> Result<*mut c_void, LlvmError> {
        // SAFETY: the library remains loaded until all typed entries are gone.
        let symbol = unsafe { dlsym(self.handle, name.as_ptr()) };
        if symbol.is_null() {
            return Err(loader_error());
        }
        Ok(symbol)
    }
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    fn symbol(&self, _: &CStr) -> Result<*mut c_void, LlvmError> {
        Err(LlvmError::UnsupportedTarget(
            "native loader requires x86_64 Linux".into(),
        ))
    }
}
impl Drop for Library {
    fn drop(&mut self) {
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        // SAFETY: no entry/callback can outlive the owning native module.
        unsafe {
            dlclose(self.handle);
        }
    }
}
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn loader_error() -> LlvmError {
    // SAFETY: the loader owns a NUL-terminated diagnostic until the next call.
    let message = unsafe { dlerror() };
    LlvmError::Tool(if message.is_null() {
        "native dynamic loader failed".into()
    } else {
        unsafe { CStr::from_ptr(message) }
            .to_string_lossy()
            .into_owned()
    })
}

type Entry = unsafe extern "C" fn(*mut NativeContext, *const *const u8, *mut u8) -> u32;

/// Actual CPU code generated from Glorious. Its owning library, immutable
/// code/ABI descriptor, and typed entry addresses have one shared lifetime.
#[derive(Clone)]
pub struct LlvmNativeModule {
    plan: LlvmIrProgram,
    entries: Vec<Entry>,
    _library: Arc<Library>,
}

impl LlvmIrProgram {
    /// # Safety
    /// The selected LLVM compiler/linker and its runtime libraries must be
    /// trusted to implement this exact IR and ABI. An arbitrary executable
    /// called `clang` or a malicious native object is not source verification.
    pub unsafe fn compile(
        &self,
        options: &LlvmCompileOptions,
    ) -> Result<LlvmNativeModule, LlvmError> {
        self.validate_abi(self.abi())?;
        if options.optimization > 3 {
            return Err(LlvmError::Tool(
                "LLVM optimization must be between 0 and 3".into(),
            ));
        }
        let directory = OutputDirectory::create()?;
        let source = directory.path.join("program.ll");
        let output = directory.path.join("program.so");
        std::fs::write(&source, self.ir())?;
        compile_shared(
            &options.clang,
            options.optimization,
            &self.abi().target.triple,
            &source,
            &output,
        )?;
        let library = Library::open(directory)?;
        let identity = library.symbol(c"g1_native_abi")?;
        // SAFETY: the exact generated global is a 32-byte constant. Checking
        // its complete descriptor happens before invoking any generated entry.
        let emitted = unsafe { std::slice::from_raw_parts(identity.cast::<u8>(), 32) };
        if emitted != self.abi().fingerprint().as_bytes() {
            return Err(LlvmError::AbiMismatch(
                "compiled native object has a different ABI witness",
            ));
        }
        let entries = self
            .functions
            .iter()
            .enumerate()
            .map(|(index, _)| {
                let name =
                    CString::new(format!("g1_export_{index}")).expect("numeric generated symbol");
                let pointer = library.symbol(&name)?;
                // SAFETY: the compiler generates only this exact C ABI for named
                // entry symbols, and the complete object ABI was checked above.
                Ok(unsafe { std::mem::transmute::<*mut c_void, Entry>(pointer) })
            })
            .collect::<Result<Vec<_>, LlvmError>>()?;
        Ok(LlvmNativeModule {
            plan: self.clone(),
            entries,
            _library: Arc::new(library),
        })
    }
}

fn compile_shared(
    clang: &Path,
    optimization: u8,
    target: &str,
    source: &Path,
    output: &Path,
) -> Result<(), LlvmError> {
    let outcome = Command::new(clang)
        .args([
            "-x",
            "ir",
            "-shared",
            "-fPIC",
            "-Werror",
            "-Wl,-z,defs",
            "-ffp-contract=off",
            "-target",
            target,
        ])
        .arg(format!("-O{optimization}"))
        .arg(source)
        .arg("-o")
        .arg(output)
        .arg("-lm")
        .output()
        .map_err(|error| {
            LlvmError::Tool(format!(
                "cannot invoke LLVM compiler {}: {error}",
                clang.display()
            ))
        })?;
    if !outcome.status.success() {
        let diagnostics = String::from_utf8_lossy(&outcome.stderr);
        return Err(LlvmError::Tool(format!(
            "LLVM compilation failed ({}): {}",
            outcome.status,
            diagnostics.chars().take(16_384).collect::<String>()
        )));
    }
    Ok(())
}

impl LlvmNativeModule {
    pub(in crate::vm_backend) fn plan(&self) -> &LlvmIrProgram {
        &self.plan
    }

    pub(in crate::vm_backend) unsafe fn invoke_native(
        &self,
        index: usize,
        context: &mut NativeContext,
        arguments: *const *const u8,
        result: *mut u8,
    ) -> u32 {
        // SAFETY: only the closed generated-code bridge calls this with the
        // exact compiler-owned slot plans and owning library kept alive.
        unsafe { (self.entries[index])(context, arguments, result) }
    }
    pub fn abi(&self) -> &super::LlvmAbiDescriptor {
        self.plan.abi()
    }
    pub fn run_i64_with_limits(&self, limits: VmExecutionLimits) -> Result<i64, LlvmError> {
        if self
            .plan
            .program
            .program
            .functions
            .values()
            .any(|function| function.unsafe_execution)
        {
            return Err(LlvmError::Runtime(
                super::VmArtifactError::UnsafeExecutionRequiresUnsafeApi,
            ));
        }
        if !self.plan.vm_functions.is_empty() {
            // SAFETY: only compiler-generated bindings of this exact sealed
            // safe source graph are installed; no external adapter is added.
            return unsafe { self.run_i64_mixed_with_unsafe(limits) };
        }
        // SAFETY: the native graph contains no admitted programmer-owned
        // unsafe operation. The empty entry contract is checked below.
        unsafe { self.run_i64_profiled(limits) }.map(|(value, _)| value)
    }

    /// # Safety
    /// Uphold the original source closure's unsafe contracts. Native execution
    /// shares real process memory and is not an in-process unsafe-code sandbox.
    pub unsafe fn run_i64_with_unsafe(&self, limits: VmExecutionLimits) -> Result<i64, LlvmError> {
        if !self.plan.vm_functions.is_empty() {
            return unsafe { self.run_i64_mixed_with_unsafe(limits) };
        }
        unsafe { self.run_i64_profiled(limits) }.map(|(value, _)| value)
    }

    /// Execute the chosen VM/LLVM partition over one source graph and one
    /// allocation domain. Ordinary crossings use real native ABI slots.
    ///
    /// # Safety
    /// Uphold the original source graph's unsafe memory contracts and the
    /// trusted compiler/linker obligations of the owning native module.
    pub unsafe fn run_i64_mixed_with_unsafe(
        &self,
        limits: VmExecutionLimits,
    ) -> Result<i64, LlvmError> {
        unsafe { crate::vm_backend::native_bridge::generated::run(self.clone(), limits) }
    }

    /// Execute actual generated machine code and report the bounded dispatcher
    /// depth/tail count; no VM execution is used to obtain the answer.
    ///
    /// # Safety
    /// The same source-memory obligations as `run_i64_with_unsafe` apply.
    pub unsafe fn run_i64_profiled(
        &self,
        limits: VmExecutionLimits,
    ) -> Result<(i64, LlvmExecutionProfile), LlvmError> {
        self.plan.validate_abi(self.abi())?;
        if !self.plan.vm_functions.is_empty() {
            return Err(LlvmError::AbiMismatch(
                "mixed partition requires the shared VM/native runner",
            ));
        }
        let entry = self.plan.program.program.entry;
        let function = &self.plan.program.program.functions[&entry];
        if function.parameters != 0
            || !matches!(
                function.instructions.first(),
                Some(crate::VmInstruction::DeclareResult {
                    result: VmType::I64,
                    ..
                })
            )
        {
            return Err(LlvmError::AbiMismatch(
                "native i64 runner requires a zero-argument i64 entry",
            ));
        }
        let index = self
            .plan
            .functions
            .iter()
            .position(|key| *key == entry)
            .expect("planned entry");
        let mut context = NativeContext::new(limits);
        let mut result = std::mem::MaybeUninit::<i64>::uninit();
        // SAFETY: the module owns its entry, no arguments are expected, and
        // the result points at correctly aligned uninitialized i64 storage.
        let status = unsafe {
            (self.entries[index])(&mut context, std::ptr::null(), result.as_mut_ptr().cast())
        };
        context.result(status)?;
        if context.depth != 0 || context.live_bytes != 0 {
            return Err(LlvmError::InvalidNativeGraph(
                "native dispatcher did not discharge its activation accounting".into(),
            ));
        }
        Ok((
            unsafe { result.assume_init() },
            LlvmExecutionProfile {
                instructions: context.instructions,
                peak_call_depth: context.peak_depth,
                recycled_tail_calls: context.tail_calls,
            },
        ))
    }
}
