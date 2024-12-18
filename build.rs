use std::env;
use std::path::PathBuf;

fn main() {
    let link_ld = &PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("link.ld");
    println!("cargo::rustc-link-arg=-T{}", link_ld.display());
    println!("cargo::rerun-if-changed={}", link_ld.display());
}
