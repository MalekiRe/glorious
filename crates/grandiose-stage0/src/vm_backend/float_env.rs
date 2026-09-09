//! Per-invocation machine environment shared by bytecode and native execution.
//! The C bridge uses the host's fenv_t and FE_DFL_ENV, never a guessed libc
//! layout. Source arithmetic, parsing, formatting and conversion policy do
//! not live here. WebAssembly's scalar instructions already fix this profile.

use super::VmArtifactError;

#[cfg(not(any(target_arch = "wasm32", target_arch = "wasm64")))]
const ERROR: &str = "cannot establish or restore the floating-point environment";

#[cfg(not(any(target_arch = "wasm32", target_arch = "wasm64")))]
mod selected {
    // These are storage bounds, not a frozen C layout. float_env.c checks
    // both against the actual target headers at compilation time.
    #[repr(C, align(64))]
    pub(super) struct Environment([u8; 512]);

    unsafe extern "C" {
        fn grandiose_float_env_capture(storage: *mut Environment) -> std::ffi::c_int;
        fn grandiose_float_env_default() -> std::ffi::c_int;
        fn grandiose_float_env_restore(storage: *const Environment) -> std::ffi::c_int;
    }

    impl Environment {
        pub(super) fn capture() -> Option<Self> {
            let mut saved = Self([0; 512]);
            // SAFETY: the target-compiled bridge checks the opaque buffer's
            // size/alignment against fenv_t; no source pointer enters here.
            (unsafe { grandiose_float_env_capture(&mut saved) } == 0).then_some(saved)
        }
        pub(super) fn install_default() -> bool {
            // SAFETY: the C bridge owns the target's FE_DFL_ENV convention.
            unsafe { grandiose_float_env_default() == 0 }
        }
        pub(super) fn restore(&self) -> bool {
            // SAFETY: restore this thread's captured control/status state.
            unsafe { grandiose_float_env_restore(self) == 0 }
        }
    }
}

pub(super) struct FloatEnvironment {
    #[cfg(not(any(target_arch = "wasm32", target_arch = "wasm64")))]
    saved: Option<selected::Environment>,
    // Floating-point controls are thread-local, including while unwinding.
    _thread: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl FloatEnvironment {
    pub(super) fn enter() -> Result<Self, VmArtifactError> {
        #[cfg(not(any(target_arch = "wasm32", target_arch = "wasm64")))]
        {
            let saved = selected::Environment::capture().ok_or_else(Self::error)?;
            let guard = Self {
                saved: Some(saved),
                _thread: std::marker::PhantomData,
            };
            if !selected::Environment::install_default() {
                return Err(Self::error());
            }
            Ok(guard)
        }
        #[cfg(any(target_arch = "wasm32", target_arch = "wasm64"))]
        Ok(Self {
            _thread: std::marker::PhantomData,
        })
    }

    pub(super) fn restore(self) -> Result<(), VmArtifactError> {
        #[cfg(not(any(target_arch = "wasm32", target_arch = "wasm64")))]
        {
            let mut guard = self;
            if guard.saved.as_ref().is_none_or(|saved| !saved.restore()) {
                return Err(Self::error());
            }
            guard.saved = None;
        }
        Ok(())
    }

    #[cfg(not(any(target_arch = "wasm32", target_arch = "wasm64")))]
    fn error() -> VmArtifactError {
        VmArtifactError::NativeAbi { message: ERROR }
    }
}

impl Drop for FloatEnvironment {
    fn drop(&mut self) {
        #[cfg(not(any(target_arch = "wasm32", target_arch = "wasm64")))]
        if let Some(saved) = &self.saved {
            // Ordinary return checks restoration; this also handles unwind
            // and failure while establishing the requested environment.
            let _ = saved.restore();
        }
    }
}

pub(super) fn with_profile<T>(
    body: impl FnOnce() -> Result<T, VmArtifactError>,
) -> Result<T, VmArtifactError> {
    let environment = FloatEnvironment::enter()?;
    let result = body();
    environment.restore()?;
    result
}
