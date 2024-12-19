use core::arch::asm;

pub fn main() {
    unsafe { asm!("li a1, 1", "li a2, 2", "add a3, a1, a2", "mul a4, a2, a3") }
}
