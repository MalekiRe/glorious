/* Machine environment only; no source arithmetic or conversion policy. */
#include <fenv.h>

/* Rust supplies an opaque stack buffer, not a libc-specific struct layout.
 * These assertions bind its capacity/alignment to the host's actual fenv_t.
 * Changing either bound requires changing Environment in float_env.rs too. */
_Static_assert(sizeof(fenv_t) <= 512, "floating-point environment exceeds opaque storage");
_Static_assert(64 % _Alignof(fenv_t) == 0, "floating-point environment exceeds opaque alignment");

int grandiose_float_env_capture(void *storage) {
    return fegetenv((fenv_t *)storage);
}

int grandiose_float_env_default(void) {
    if (fesetenv(FE_DFL_ENV) != 0) {
        return -1;
    }
    return fesetround(FE_TONEAREST);
}

int grandiose_float_env_restore(const void *storage) {
    return fesetenv((const fenv_t *)storage);
}
