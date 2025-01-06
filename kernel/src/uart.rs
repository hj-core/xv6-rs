use crate::lock::Spinlock;
use hw::uart;
use hw::uart::{
    FCR_FIFO_ENABLE, FCR_RECEIVE_FIFO_RESET, FCR_TRANSMIT_FIFO_RESET,
    IER_RECEIVER_READY_INTERRUPT_ENABLE, IER_TRANSMITTER_EMPTY_INTERRUPT_ENABLE,
    LCR_8BIT_WORD_LENGTH, LCR_DIVISOR_LATCH_ENABLE, LSR_TRANSMIT_HOLDING_EMPTY,
};

static UART_LOCK: Spinlock = Spinlock::new();

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
    uart::LCR.write(LCR_DIVISOR_LATCH_ENABLE);
    uart::THR.write(0x03);
    uart::IER.write(0x00);
    // Disable the Divisor Latch; set the word length to 8 bits with no parity
    uart::LCR.write(LCR_8BIT_WORD_LENGTH);
}

fn reset_and_enable_fifo() {
    uart::FCR.write(FCR_FIFO_ENABLE | FCR_RECEIVE_FIFO_RESET | FCR_TRANSMIT_FIFO_RESET);
}

fn enable_transmitter_and_receiver_interrupts_only() {
    uart::IER.write(IER_RECEIVER_READY_INTERRUPT_ENABLE | IER_TRANSMITTER_EMPTY_INTERRUPT_ENABLE);
}

fn print_byte(byte: u8) {
    while is_thr_full() {}
    uart::THR.write(byte);
}

fn is_thr_full() -> bool {
    uart::LSR.read() & LSR_TRANSMIT_HOLDING_EMPTY == 0
}

pub fn busy_print_byte(byte: u8) {
    UART_LOCK.lock();
    print_byte(byte);
    UART_LOCK.unlock();
}

pub fn busy_print_str(str: &str) {
    UART_LOCK.lock();
    for &byte in str.as_bytes() {
        print_byte(byte);
    }
    UART_LOCK.unlock();
}
