fn main() {
    println!("cargo:rerun-if-changed=src/vm_backend/float_env.c");
    let architecture = std::env::var("CARGO_CFG_TARGET_ARCH").expect("Cargo target architecture");
    if matches!(architecture.as_str(), "wasm32" | "wasm64") {
        // WebAssembly scalar operations have fixed nearest-even/non-stop
        // semantics and expose no mutable floating-point environment.
        return;
    }
    cc::Build::new()
        .file("src/vm_backend/float_env.c")
        .std("c11")
        .compile("grandiose_float_env");
    if std::env::var("CARGO_CFG_TARGET_FAMILY").as_deref() == Ok("unix") {
        println!("cargo:rustc-link-lib=m");
    }
}
