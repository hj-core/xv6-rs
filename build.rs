use std::env;
use std::path::PathBuf;

fn main() {
    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    if arch != "riscv64" {
        return;
    }

    let link_ld = &PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("link.ld");
    println!("cargo::rustc-link-arg=-T{}", link_ld.display());
    println!("cargo::rerun-if-changed={}", link_ld.display());
}
