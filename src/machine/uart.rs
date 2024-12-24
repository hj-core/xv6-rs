// 'virt' machine supports a NS16550 compatible UART.

// The memory map address of UART0
const VIRT_UART0_MEMMAP_BASE: u64 = 0x1000_0000;

pub struct Register {
    relative_addr: u64, // Relative to the base address
}

impl Register {
    pub fn read(&self) -> u8 {
        unsafe { *self.raw_ptr() }
    }

    fn raw_ptr(&self) -> *mut u8 {
        (VIRT_UART0_MEMMAP_BASE + self.relative_addr) as *mut u8
    }

    pub fn write(&self, value: u8) {
        unsafe { *self.raw_ptr() = value }
    }
}

// Relative addresses of UART accessible registers.
// Some addresses have different meanings depending on whether they are read or written.
//
// Ref:
// TECHNICAL DATA ON 16550
// http://byterunner.com/16550.html

/// \[READ] Receive Holding Register
pub const RHR: Register = Register { relative_addr: 0 };

/// \[WRITE] Transmit Holding Register, or LSB of Divisor Latch when enabled
pub const THR: Register = Register { relative_addr: 0 };

/// \[WRITE] Interrupt Enable Register, or MSB of Divisor Latch when enabled
pub const IER: Register = Register { relative_addr: 1 };
pub const IER_RECEIVER_READY_INTERRUPT_ENABLE: u8 = 0x01;
pub const IER_TRANSMITTER_EMPTY_INTERRUPT_ENABLE: u8 = 0x02;

/// \[WRITE] FIFO control Register
pub const FCR: Register = Register { relative_addr: 2 };
pub const FCR_FIFO_ENABLE: u8 = 0x01;
pub const FCR_RECEIVE_FIFO_RESET: u8 = 0x02;
pub const FCR_TRANSMIT_FIFO_RESET: u8 = 0x04;

/// \[READ] Interrupt Status Register
pub const ISR: Register = Register { relative_addr: 2 };

/// \[WRITE] Line Control Register
pub const LCR: Register = Register { relative_addr: 3 };
pub const LCR_DIVISOR_LATCH_ENABLE: u8 = 0x40;
pub const LCR_8BIT_WORD_LENGTH: u8 = 0x03;

/// \[WRITE] Modem Control Register
pub const MCR: Register = Register { relative_addr: 4 };

/// \[WRITE] Line Status Register
pub const LSR: Register = Register { relative_addr: 5 };
pub const LSR_TRANSMIT_HOLDING_EMPTY: u8 = 0x20;

/// \[READ] Modem Status Register
pub const MSR: Register = Register { relative_addr: 6 };

/// \[READ] Scratchpad Register Read, or \[WRITE MODE] Scratchpad Register Write
pub const SPR: Register = Register { relative_addr: 7 };
