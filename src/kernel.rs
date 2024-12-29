mod lock;
mod uart;

#[cfg(target_arch = "riscv64")]
pub fn main() {
    uart::initialize();
    uart::busy_print_str("Hello World!\n");
}
