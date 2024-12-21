// The virt machine supports a NS16550 compatible UART.
// See http://byterunner.com/16550.html for technical data.

// The memory map address and size of UART0
const VIRT_UART0_MEM_BASE: u64 = 0x1000_0000;

pub struct Register {
    relative_addr: u64, // Relative to the base address
}

impl Register {
    pub fn read(&self) -> u8 {
        unsafe { *self.raw_ptr() }
    }

    fn raw_ptr(&self) -> *mut u8 {
        (VIRT_UART0_MEM_BASE + self.relative_addr) as *mut u8
    }

    pub fn write(&self, value: u8) {
        unsafe { *self.raw_ptr() = value }
    }
}

// The relative addresses of UART control registers.
// Some addresses have different meanings depending on whether they are read or written.

/// \[READ] Receive Holding Register
pub const RHR: Register = Register { relative_addr: 0 };

/// \[WRITE] Transmit Holding Register, or LSB of Divisor Latch when enabled
pub const THR: Register = Register { relative_addr: 0 };

/// \[WRITE] Interrupt Enable Register, or MSB of Divisor Latch when enabled
pub const IER: Register = Register { relative_addr: 1 };

/// \[WRITE] FIFO control Register
pub const FCR: Register = Register { relative_addr: 2 };

/// \[READ] Interrupt Status Register
pub const ISR: Register = Register { relative_addr: 2 };

/// \[WRITE] Line Control Register
pub const LCR: Register = Register { relative_addr: 3 };

/// \[WRITE] Modem Control Register
pub const MCR: Register = Register { relative_addr: 4 };

/// \[WRITE] Line Status Register
pub const LSR: Register = Register { relative_addr: 5 };

/// \[READ] Modem Status Register
pub const MSR: Register = Register { relative_addr: 6 };

/// \[READ] Scratchpad Register Read, or \[WRITE MODE] Scratchpad Register Write
pub const SPR: Register = Register { relative_addr: 7 };
