fn main() {
    if cfg!(target_env = "msvc") {
        println!("cargo::rustc-link-arg-bins=/STACK:{}", 256 * 1024 * 1024);
    }
    println!("cargo::rerun-if-changed=build.rs");
}
