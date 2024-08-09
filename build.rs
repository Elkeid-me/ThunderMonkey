fn main() {
    if cfg!(target_env = "msvc") {
        println!("cargo::rustc-link-arg-bins=/STACK:{}", 128 * 1024 * 1024);
    }
    println!("cargo::rerun-if-changed=build.rs");
}
