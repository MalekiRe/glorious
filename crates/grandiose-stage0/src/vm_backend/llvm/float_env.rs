//! Thread-local machine environment for the selected native target profile.
//!
//! LLVM's explicit nearest-rounding metadata does not install MXCSR on x86.
//! Embedders may use another rounding mode or flush subnormals. A generated
//! invocation must establish the language profile and restore the caller's
//! complete control/status environment, including on an error or unwind.

use super::{LlvmError, VmArtifactError};

const ERROR: &str = "cannot establish or restore the native floating-point environment";

#[cfg(all(target_os = "linux", target_env = "gnu", target_arch = "x86_64"))]
mod selected {
    // The x86_64 GNU C ABI's fenv_t is the 28-byte x87 environment followed
    // by the 4-byte MXCSR word. It is deliberately opaque: no host-private
    // field interpretation leaks into source values or portable bytecode.
    #[repr(C, align(4))]
    pub(super) struct Environment([u8; 32]);

    #[link(name = "m")]
    unsafe extern "C" {
        fn fegetenv(environment: *mut Environment) -> std::ffi::c_int;
        fn fesetenv(environment: *const Environment) -> std::ffi::c_int;
    }

    impl Environment {
        pub(super) fn capture() -> Option<Self> {
            let mut saved = Self([0; 32]);
            // SAFETY: size/alignment match fenv_t in the selected GNU ABI.
            (unsafe { fegetenv(&mut saved) } == 0).then_some(saved)
        }

        pub(super) fn install_default() -> bool {
            // SAFETY: GNU FE_DFL_ENV is the reserved -1 pointer, not a
            // dereferenceable address. It selects nearest-even rounding,
            // gradual underflow, and masked exceptions for x87 and SSE.
            unsafe { fesetenv(std::ptr::without_provenance(usize::MAX)) == 0 }
        }

        pub(super) fn restore(&self) -> bool {
            // SAFETY: this exact environment was captured on this thread.
            unsafe { fesetenv(self) == 0 }
        }
    }
}

pub(in crate::vm_backend) struct NativeFloatEnvironment {
    #[cfg(all(target_os = "linux", target_env = "gnu", target_arch = "x86_64"))]
    saved: Option<selected::Environment>,
    // Restoration is thread-local. Do not permit moving this guard to a
    // different worker or sharing it while an invocation is active.
    _thread: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl NativeFloatEnvironment {
    pub(in crate::vm_backend) fn enter() -> Result<Self, LlvmError> {
        #[cfg(all(target_os = "linux", target_env = "gnu", target_arch = "x86_64"))]
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
        #[cfg(not(all(target_os = "linux", target_env = "gnu", target_arch = "x86_64")))]
        Err(Self::error())
    }

    pub(in crate::vm_backend) fn restore(mut self) -> Result<(), LlvmError> {
        #[cfg(all(target_os = "linux", target_env = "gnu", target_arch = "x86_64"))]
        {
            if self.saved.as_ref().is_none_or(|saved| !saved.restore()) {
                return Err(Self::error());
            }
            self.saved = None;
            Ok(())
        }
        #[cfg(not(all(target_os = "linux", target_env = "gnu", target_arch = "x86_64")))]
        Err(Self::error())
    }

    fn error() -> LlvmError {
        LlvmError::Runtime(VmArtifactError::NativeAbi { message: ERROR })
    }
}

impl Drop for NativeFloatEnvironment {
    fn drop(&mut self) {
        #[cfg(all(target_os = "linux", target_env = "gnu", target_arch = "x86_64"))]
        if let Some(saved) = &self.saved {
            // The ordinary return path checks restoration explicitly. This
            // fallback also restores the environment on unwinding/early Err.
            let _ = saved.restore();
        }
    }
}
