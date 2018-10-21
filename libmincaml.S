	.text
	.align 	2
	.globl	min_caml_print_byte
min_caml_print_char:
  li s11, 65540
  sb a0, 0(s11)
  jr ra
div10.1:
	add	sp, sp, -48
	sw	ra, 40(sp)
	sub	a3, a2, a1
	li	s10, 1
	bgt	a3, s10, ble_else.32
	mv	a0, a1
	j	div10.1_end
ble_else.32:
	add	a3, a1, a2
	srli	a3, a3, 1
  slli t1, a3, 1
  slli a4, a3, 3
	add	a4, a4, t1
	bgt	a4, a0, ble_else.33
	add	a1, a3, 0
	call	div10.1
	j	div10.1_end
ble_else.33:
	add	a2, a3, 0
	call	div10.1
	j	div10.1_end
div10.1_end:
	lw	ra, 40(sp)
	add	sp, sp, 48
	jr	ra
min_caml_print_int:
	add	sp, sp, -40
	sw	ra, 32(sp)
	li	s10, 0
	bne	a0, s10, beq_else.34
	li	s10, 0
	bne	a1, s10, beq_else.35
	nop
	j	min_caml_print_int_end
beq_else.35:
	li	a0, 48
	call	min_caml_print_char
	j	min_caml_print_int_end
beq_else.34:
	li	a1, 0
	li	a2, 2147483647
	sw	a0, 0(sp)
	call	div10.1
	li	a1, 0
	sw	a0, 4(sp)
	call	min_caml_print_int
	lw	a0, 4(sp)
	lw	a1, 0(sp)
  slli  t1, a0,  1
  slli  a0, a0,  3
  add   a0, a0, t1
	sub	a0, a1, a0
	add	a0, a0, 48
	call	min_caml_print_char
	j	min_caml_print_int_end
min_caml_print_int_end:
	lw	ra, 32(sp)
	add	sp, sp, 40
	jr	ra
