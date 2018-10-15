	.text
	.align 	2
	.globl	min_caml_print_byte
min_caml_print_byte:
  li s11 0x10000
  sb a0, 0(s11)
  jr ra
  .text
  .align  2
  .globl min_caml_print_int
min_caml_print_int:
  li s11 0x10000
  sb a0, 0(s11)
  srli a0, a0, 2
  sb a0, 0(s11)
  srli a0, a0, 2
  sb a0, 0(s11)
  srli a0, a0, 2
  sb a0, 0(s11)
  jr ra
