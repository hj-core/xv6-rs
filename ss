#!/usr/bin/env python3
import subprocess
import sys


def main():
    shortcuts = [shortcut0, shortcut1, shortcut2, shortcut3, shortcut4, shortcut5]
    match len(sys.argv):
        case 1:
            shortcuts[0]()
        case 2:
            index = int(sys.argv[1])
            if index in range(len(shortcuts)) and shortcuts[index]:
                shortcuts[index]()
        case _:
            exit(1)


def shortcut0():
    if cargo_build_debug() or cargo_objdump_debug() or qemu_gdb_boot() or remove_dump():
        exit(1)


def shortcut1():
    if cargo_test():
        exit(1)


def shortcut2():
    if cargo_build_debug() or cargo_objdump_debug() or qemu_gdb_boot(smp=4) or remove_dump():
        exit(1)


def shortcut3():
    if cargo_build_release() or cargo_objdump_release() or qemu_gdb_boot(profile="release") or remove_dump():
        exit(1)


def shortcut4():
    if cargo_build_release() or cargo_objdump_release() or qemu_gdb_boot(profile="release", smp=4) or remove_dump():
        exit(1)


def shortcut5():
    if miri_test():
        exit(1)


def echo_cmd(cmd: str):
    print(f"Prompt> {cmd}")


def cargo_build_debug() -> int:
    cmd = "cargo build"
    echo_cmd(cmd)
    return subprocess.run(cmd, shell=True).returncode


def cargo_build_release() -> int:
    cmd = "cargo build --release"
    echo_cmd(cmd)
    return subprocess.run(cmd, shell=True).returncode


def cargo_objdump_debug() -> int:
    cmd = "cargo objdump -- -d > dump.txt"
    echo_cmd(cmd)
    return subprocess.run(cmd, shell=True).returncode


def cargo_objdump_release() -> int:
    cmd = "cargo objdump --release -- -d > dump.txt"
    echo_cmd(cmd)
    return subprocess.run(cmd, shell=True).returncode


def cargo_test() -> int:
    cmd = "cargo test --target x86_64-unknown-linux-gnu"
    echo_cmd(cmd)
    return subprocess.run(cmd, shell=True).returncode


def miri_test() -> int:
    cmd = "cargo +nightly miri test --target x86_64-unknown-linux-gnu"
    echo_cmd(cmd)
    return subprocess.run(cmd, shell=True).returncode


def qemu_gdb_boot(profile: str = "debug", smp: int = 1, mem_in_mb: int = 128) -> int:
    cmd = f"qemu-system-riscv64 -s -S -machine virt -bios none -kernel target/riscv64gc-unknown-none-elf/{profile}/kernel -m {mem_in_mb}M -smp {smp} -nographic -global virtio-mmio.force-legacy=false"
    echo_cmd(cmd)
    return subprocess.run(cmd, shell=True).returncode


def remove_dump() -> int:
    cmd = "rm dump.txt"
    echo_cmd(cmd)
    return subprocess.run(cmd, shell=True).returncode


if __name__ == "__main__":
    main()
