qemu-system-riscv64 -s -S -machine virt -bios none -kernel target/riscv64gc-unknown-none-elf/debug/xv6-rs -m 128M -smp 1 -nographic -global virtio-mmio.force-legacy=false
