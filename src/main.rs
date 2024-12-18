#![no_std]
#![no_main]

use core::arch::asm;
use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn _start() -> ! {
    unsafe { asm!("li s2, 5", "li s3, 7", "add s4, s2, s3", "mul s5, s3, s4",) }
    loop {}
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
