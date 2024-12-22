mod uart;

mod lock;

#[cfg(target_arch = "riscv64")]
pub fn main() {
    uart::initialize();
    uart::busy_print("Hello World!");
}
