ENTRY(_entry)

SECTIONS {
  . = 0x80000000; /* Address where qemu's -kernel jumps. */

  .text : {
    *(.text.entry.must_at_0x80000000)
    *(.text .text.*)

    . = ALIGN(0x1000);
    link_text_end = .;
  }

  .rodata : {
    . = ALIGN(16);
    *(.srodata .srodata.*) /* do not need to distinguish this from .rodata */

    . = ALIGN(16);
    *(.rodata .rodata.*)
  }

  .data : {
    . = ALIGN(16);
    *(.sdata .sdata.*) /* do not need to distinguish this from .data */

    . = ALIGN(16);
    *(.data .data.*)
  }

  .bss : {
    . = ALIGN(16);
    *(.sbss .sbss.*) /* do not need to distinguish this from .bss */

    . = ALIGN(16);
    *(.bss .bss.*)
  }

  link_end = .;
}
