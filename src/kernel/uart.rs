use crate::machine::uart;

pub fn initialize() {
    disable_all_interrupts();
    configure_lcr();
    reset_and_enable_fifo();
    enable_transmitter_and_receiver_interrupts_only();
}

fn disable_all_interrupts() {
    uart::IER.write(0x00)
}

fn configure_lcr() {
    // Enable the Divisor Latch and set baud rate to 38_400
    const LCR_DIVISOR_LATCH_ENABLE: u8 = 0x40;
    uart::LCR.write(LCR_DIVISOR_LATCH_ENABLE);
    uart::THR.write(0x03);
    uart::IER.write(0x00);
    // Disable the Divisor Latch; set the word length to 8 bits with no parity
    const LCR_8BIT_WORD_LENGTH: u8 = 0x03;
    uart::LCR.write(LCR_8BIT_WORD_LENGTH);
}

fn reset_and_enable_fifo() {
    const FCR_FIFO_ENABLE: u8 = 0x01;
    const FCR_RECEIVE_FIFO_RESET: u8 = 0x02;
    const FCR_TRANSMIT_FIFO_RESET: u8 = 0x04;
    uart::FCR.write(FCR_FIFO_ENABLE | FCR_RECEIVE_FIFO_RESET | FCR_TRANSMIT_FIFO_RESET);
}

fn enable_transmitter_and_receiver_interrupts_only() {
    const IER_RECEIVER_READY_INTERRUPT_ENABLE: u8 = 0x01;
    const IER_TRANSMITTER_EMPTY_INTERRUPT_ENABLE: u8 = 0x02;
    uart::IER.write(IER_RECEIVER_READY_INTERRUPT_ENABLE | IER_TRANSMITTER_EMPTY_INTERRUPT_ENABLE);
}

pub fn busy_print(str: &str) {
    for &byte in str.as_bytes() {
        while is_thr_full() {}
        uart::THR.write(byte);
    }
}

fn is_thr_full() -> bool {
    const LSR_TRANSMIT_HOLDING_EMPTY: u8 = 0x20;
    uart::LSR.read() & LSR_TRANSMIT_HOLDING_EMPTY == 0
}
