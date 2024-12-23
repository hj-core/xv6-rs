mod spinlock;
mod uart;

pub fn main() {
    uart::initialize();
    uart::busy_print("Hello World!");
}
