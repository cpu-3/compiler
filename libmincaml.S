# print_char
min_caml_print_char:
  li s11, 131076
  sb a0, 0(s11)
  ret

# input_char
min_caml_input_char:
  li s11, 131072
  lb a0, 0(s11)
  ret

# read_float
min_caml_read_float:
	add	sp, sp, -12
	sw	ra, 8(sp)
	sw  s2, 4(sp)
	li s2, 0
	call min_caml_input_char
	add s2, s2, a0
	slli s2, s2, 8
	call min_caml_input_char
	add s2, s2, a0
	slli s2, s2, 8
	call min_caml_input_char
	add s2, s2, a0
	slli s2, s2, 8
	call min_caml_input_char
	add s2, s2, a0
	sw  s2, 0(sp)
	flw f0, 0(sp)
read_float_end:
	lw  ra, 8(sp)
	lw  s2, 4(sp)
	add	sp, sp, 12
	ret

min_caml_read_int:
	add	sp, sp, -12
	sw	ra, 8(sp)
	sw  s2, 4(sp)
	li s2, 0
	call min_caml_input_char
	add s2, s2, a0
	slli s2, s2, 8
	call min_caml_input_char
	add s2, s2, a0
	slli s2, s2, 8
	call min_caml_input_char
	add s2, s2, a0
	slli s2, s2, 8
	call min_caml_input_char
	add s2, s2, a0
    mv a0, s2
read_int_end:
	lw  ra, 8(sp)
	lw  s2, 4(sp)
	add	sp, sp, 12
	ret

# print_newline
min_caml_print_newline:
  li a0, 10
  j min_caml_print_char

#	create_array
min_caml_create_array:
  mv  t1, a0
  mv  a0, hp
create_array_loop:
	bne t1, zero, create_array_cont
  ret
create_array_cont:
	sw  a1, 0(hp)
	sub t1, t1, 1
	add hp, hp, 4
	j create_array_loop

#	create_float_array
min_caml_create_float_array:
  mv  t1, a0
  mv  a0, hp
create_float_array_loop:
	bne t1, zero, create_float_array_cont
	ret
create_float_array_cont:
	fsw  f0, 0(hp)
	sub t1, t1, 1
	add hp, hp, 4
	j create_float_array_loop


min_caml_fless:
	flt.s a0, f0, f1
	ret

fsqrt_24:	 # 1.500000
	.word	1069547520
fsqrt_23:	 # 0.500000
	.word	1056964608
fsqrt_123:	 # 1.000000
	.word	1065353216
min_caml_sqrt:
	add	sp, sp, -4
	li	t1, fsqrt_23
	flw	f1, 0(t1)
	fmul.s	f1, f0, f1

	fsw f0, 0(sp)
	lw  t2, 0(sp)

	srli t2, t2, 1
	li t3, 1597463007
	sub t2, t3, t2

	sw  t2, 0(sp)
	flw f0, 0(sp)

	li	t1, fsqrt_24
	flw	f2, 0(t1)
	fmul.s	f3, f1, f0
	fmul.s	f3, f3, f0
	fsub.s	f3, f2, f3
	fmul.s	f0, f0, f3

	fmul.s	f3, f1, f0
	fmul.s	f3, f3, f0
	fsub.s	f3, f2, f3
	fmul.s	f0, f0, f3

	li	t1, fsqrt_123
	flw	f2, 0(t1)
	fdiv.s f0, f2, f0

	add	sp, sp, 4
	ret
min_caml_union_ftoi:
	fsw f0, -4(sp)
	lw a0, -4(sp)
	ret
min_caml_union_itof:
	sw a0, -4(sp)
	flw f0, -4(sp)
	ret
itof_l86:	 # 0.500000
	.word	1056964608
itof_l82:	 # 0.000000
	.word	0
itof_l78:	 # 8388608.000000
	.word	1258291200
itof_kern.1:
	add	sp, sp, -4
	sw	ra, 0(sp)
	li	a1, 1258291200
	add	a0, a0, a1
	call	min_caml_union_itof
	li	t1, itof_l78
	flw	f1, 0(t1)
	fsub.s	f0, f0, f1
	lw	ra, 0(sp)
	add	sp, sp, 4
	ret
itof2.3:
	li	a1, 8388608
	bgt	a1, a0, ble_else.98
	li	a1, 8388608
	sub	a0, a0, a1
	li	t1, itof_l78
	flw	f1, 0(t1)
	fadd.s	f0, f1, f0
	j	itof2.3
ble_else.98:
	mv	a1, hp
	ret
min_caml_itof:
	add	sp, sp, -12
	sw	ra, 8(sp)
	li	t1, 0
	blt	a0, t1, bge_else.99
	mv	a1, a0
	j	bge_cont.100
bge_else.99:
	sub	a1, zero, a0
bge_cont.100:
	li	t1, itof_l82
	flw	f0, 0(t1)
	sw	a0, 0(sp)
	mv	a0, a1
	call	itof2.3
	fsw	f0, 4(sp)
	call	itof_kern.1
	flw	f1, 4(sp)
	fadd.s	f0, f0, f1
	lw	a0, 0(sp)
	li	t1, 0
	blt	a0, t1, bge_else.101
	lw	ra, 8(sp)
	add	sp, sp, 12
	ret
bge_else.101:
	fneg.s	f0, f0
	lw	ra, 8(sp)
	add	sp, sp, 12
	ret
ftoi_kern.8:
	add	sp, sp, -4
	sw	ra, 0(sp)
	li	t1, itof_l78
	flw	f1, 0(t1)
	fadd.s	f0, f0, f1
	call	min_caml_union_ftoi
	li	a1, 1258291200
	sub	a0, a0, a1
	lw	ra, 0(sp)
	add	sp, sp, 4
	ret
ftoi2.10:
	li	t1, itof_l78
	flw	f1, 0(t1)
	fle.s	t1, f1, f0
	beq	t1, zero, fle.s_else.102
	li	t1, itof_l78
	flw	f1, 0(t1)
	fsub.s	f0, f0, f1
	li	a1, 8388608
	add	a0, a0, a1
	j	ftoi2.10
fle.s_else.102:
	ret
min_caml_ftoi:
	add	sp, sp, -12
	sw	ra, 8(sp)
	li	t1, itof_l82
	flw	f1, 0(t1)
	fle.s	t1, f1, f0
	beq	t1, zero, fle.s_else.103
	fmv.s	f1, f0
	j	fle.s_cont.104
fle.s_else.103:
	fneg.s	f1, f0
fle.s_cont.104:
	li	t1, itof_l86
	flw	f2, 0(t1)
	fle.s	t1, f2, f1
	beq	t1, zero, fle.s_else.105
	li	t1, itof_l86
	flw	f2, 0(t1)
	fsub.s	f1, f1, f2
	li	a0, 0
	fsw	f0, 0(sp)
	fmv.s	f0, f1
	call	ftoi2.10
	mv a1, a0
	sw	a1, 4(sp)
	call	ftoi_kern.8
	lw	a1, 4(sp)
	add	a0, a0, a1
	li	t1, itof_l82
	flw	f0, 0(t1)
	flw	f1, 0(sp)
	fle.s	t1, f0, f1
	beq	t1, zero, fle.s_else.106
	lw	ra, 8(sp)
	add	sp, sp, 12
	ret
fle.s_else.106:
	sub	a0, zero, a0
	lw	ra, 8(sp)
	add	sp, sp, 12
	ret
fle.s_else.105:
	li	a0, 0
	lw	ra, 8(sp)
	add	sp, sp, 12
	ret
