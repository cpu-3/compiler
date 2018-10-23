# print_char
min_caml_print_char:
  li s11, 65540
  sb a0, 0(s11)
  ret

# print_newline
min_caml_print_newline:
  li a0, 10
  j min_caml_print_char

# print_int
div10.1:
	add	sp, sp, -4
	sw	ra, 0(sp)
	sub	a3, a2, a1
	li	t1, 1
	bgt	a3, t1, ble_else.44
	mv	a0, a1
	j	div10.1_end
ble_else.44:
	sub	a3, a2, a1
  srli a3, a3, 1
	add	a3, a1, a3
  slli t1, a3, 1
  slli a4, a3, 3
	add	a4, a4, t1
	bgt	a4, a0, ble_else.45
	add	a1, a3, 0
	call	div10.1
	j	div10.1_end
ble_else.45:
	add	a2, a3, 0
	call	div10.1
	j	div10.1_end
div10.1_end:
	lw	ra, 0(sp)
	add	sp, sp, 4
	ret
print_int2.5:
	add	sp, sp, -12
	sw	ra, 8(sp)
	bne	a0, zero, beq_else.46
	bne	a1, zero, beq_else.47
	nop
	j	print_int2.5_end
beq_else.47:
	li	a0, 48
	call	min_caml_print_char
	j	print_int2.5_end
beq_else.46:
	li	a1, 0
	li	a2, 214748365
	sw	a0, 0(sp)
	call	div10.1
	li	a1, 0
	sw	a0, 4(sp)
	call	print_int2.5
	lw	a0, 4(sp)
	lw	a1, 0(sp)
  slli t1, a0, 1
  slli a0, a0, 3
  add a0, a0, t1
	sub	a0, a1, a0
	add	a0, a0, 48
	call	min_caml_print_char
	j	print_int2.5_end
print_int2.5_end:
	lw	ra, 8(sp)
	add	sp, sp, 12
	ret
min_caml_print_int:
	add	sp, sp, -8
	sw	ra, 4(sp)
	blt	a0, zero, bge_else.49
	li	a1, 1
	call	print_int2.5
	j	min_caml_print_int_end
bge_else.49:
	li	a1, 45
	sw	a0, 0(sp)
	add	a0, a1, 0
	call	min_caml_print_char
	lw	a0, 0(sp)
	sub	a0, zero, a0
	li	a1, 1
	call	print_int2.5
	j	min_caml_print_int_end
min_caml_print_int_end:
	lw	ra, 4(sp)
	add	sp, sp, 8
	ret

#	create_array
min_caml_create_array:
  mv  t1, a0
  mv  a0, hp
create_array_loop:
	bne t1, zero, create_array_cont
	j create_array_end
create_array_cont:
	sw  a1, 0(hp)
	sub t1, t1, 1
	add hp, hp, 4
	j create_array_loop
create_array_end:
	ret

#	create_float_array
min_caml_create_float_array:
  mv  t1, a0
  mv  a0, hp
create_float_array_loop:
	bne t1, zero, create_float_array_cont
	j create_float_array_end
create_float_array_cont:
	fsw  f0, 0(hp)
	sub t1, t1, 1
	add hp, hp, 4
	j create_float_array_loop
create_float_array_end:
	ret

# truncate (float -> int)
min_caml_truncate:
  fcvt.w.s a0, f0
  ret

# int_of_float (float -> int)
min_caml_int_of_float:
  j min_caml_truncate

# float_of_int (int -> float)
min_caml_float_of_int:
  fcvt.s.w f0, a0
  ret

# abs_float
min_caml_abs_float:
	add sp, sp, -4
	sw	f1, 0(sp)
  li t1, neg_float
  fcvt.s.w f1, zero
  fle.s f0, f1, t1
  j min_caml_abs_float_end
neg_float:
  fneg.s f0, f0
  j min_caml_abs_float_end
min_caml_abs_float_end:
	lw	f1, 0(sp)
  add sp, sp, 4
  ret

# cos, sin
l.154:	 # 3.141593
	.word	1078530011
l.141:	 # 0.785398
	.word	1061752795
l.140:	 # 1.570796
	.word	1070141403
l.133:	 # 0.001370
	.word	984842502
l.132:	 # 0.041664
	.word	1026205577
l.131:	 # 0.500000
	.word	1056964608
l.130:	 # 0.000196
	.word	961373366
l.129:	 # 0.008333
	.word	1007191654
l.128:	 # 0.166667
	.word	1042983596
l.127:	 # 1.000000
	.word	1065353216
l.126:	 # 6.283185
	.word	1086918619
l.125:	 # 2.000000
	.word	1073741824
l.124:	 # -1.000000
	.word	-1082130432
l.123:	 # 0.000000
	.word	0
flag.2:
	add	sp, sp, -4
	sw	ra, 0(sp)
	li	t1, l.123
	flw	f1, 0(t1)
	fle.s	f1, f0, t1
	li	a0, 1
	j	flag.2_end
fgt_else.203:
	li	a0, 0
	j	flag.2_end
flag.2_end:
	lw	ra, 0(sp)
	add	sp, sp, 4
	ret
inner.105:
	add	sp, sp, -4
	sw	ra, 0(sp)
	fle.s	f1, f0, t1
	fmv.s	f0, f1
	j	inner.105_end
fgt_else.205:
	li	t1, l.125
	flw	f2, 0(t1)
	fmul.s	f1, f1, f2
	call	inner.105
	j	inner.105_end
inner.105_end:
	lw	ra, 0(sp)
	add	sp, sp, 4
	ret
inner.109:
	add	sp, sp, -4
	sw	ra, 0(sp)
	li	t1, l.126
	flw	f2, 0(t1)
	fle.s	f2, f0, t1
	j	inner.109_end
fgt_else.206:
	fle.s	f1, f0, t1
	j	fgt_cont.208
fgt_else.207:
	fsub.s	f0, f0, f1
fgt_cont.208:
	li	t1, l.125
	flw	f2, 0(t1)
	fdiv.s	f1, f1, f2
	call	inner.109
	j	inner.109_end
inner.109_end:
	lw	ra, 0(sp)
	add	sp, sp, 4
	ret
reduction2pi.6:
	add	sp, sp, -8
	sw	ra, 4(sp)
	li	t1, l.126
	flw	f1, 0(t1)
	fsw	f0, 0(sp)
	call	inner.105
	fmv.s	f1, f0
	flw	f0, 0(sp)
	call	inner.109
	j	reduction2pi.6_end
reduction2pi.6_end:
	lw	ra, 4(sp)
	add	sp, sp, 8
	ret
reverse.8:
	add	sp, sp, -4
	sw	ra, 0(sp)
	li	t1, 0
	bne	a0, t1, beq_else.209
	li	a0, 1
	j	reverse.8_end
beq_else.209:
	li	a0, 0
	j	reverse.8_end
reverse.8_end:
	lw	ra, 0(sp)
	add	sp, sp, 4
	ret
add_sign.10:
	add	sp, sp, -4
	sw	ra, 0(sp)
	li	t1, 0
	bne	a0, t1, beq_else.210
	j	add_sign.10_end
beq_else.210:
	li	t1, l.124
	flw	f1, 0(t1)
	fmul.s	f0, f1, f0
	j	add_sign.10_end
add_sign.10_end:
	lw	ra, 0(sp)
	add	sp, sp, 4
	ret
pow.13:
	add	sp, sp, -8
	sw	ra, 4(sp)
	li	t1, 0
	bne	a0, t1, beq_else.211
	li	t1, l.127
	flw	f0, 0(t1)
	j	pow.13_end
beq_else.211:
	sub	a0, a0, 1
	fsw	f0, 0(sp)
	call	pow.13
	flw	f1, 0(sp)
	fmul.s	f0, f1, f0
	j	pow.13_end
pow.13_end:
	lw	ra, 4(sp)
	add	sp, sp, 8
	ret
kernel_sin.16:
	add	sp, sp, -28
	sw	ra, 24(sp)
	li	t1, l.128
	flw	f1, 0(t1)
	li	a0, 3
	fsw	f0, 0(sp)
	fsw	f1, 4(sp)
	call	pow.13
	flw	f1, 4(sp)
	fmul.s	f0, f1, f0
	flw	f1, 0(sp)
	fsub.s	f0, f1, f0
	li	t1, l.129
	flw	f2, 0(t1)
	li	a0, 5
	fsw	f0, 8(sp)
	fsw	f2, 12(sp)
	fmv.s	f0, f1
	call	pow.13
	flw	f1, 12(sp)
	fmul.s	f0, f1, f0
	flw	f1, 8(sp)
	fadd.s	f0, f1, f0
	li	t1, l.130
	flw	f1, 0(t1)
	li	a0, 7
	flw	f2, 0(sp)
	fsw	f0, 16(sp)
	fsw	f1, 20(sp)
	fmv.s	f0, f2
	call	pow.13
	flw	f1, 20(sp)
	fmul.s	f0, f1, f0
	flw	f1, 16(sp)
	fsub.s	f0, f1, f0
	j	kernel_sin.16_end
kernel_sin.16_end:
	lw	ra, 24(sp)
	add	sp, sp, 28
	ret
kernel_cos.18:
	add	sp, sp, -32
	sw	ra, 28(sp)
	li	t1, l.127
	flw	f1, 0(t1)
	li	t1, l.131
	flw	f2, 0(t1)
	li	a0, 2
	fsw	f0, 0(sp)
	fsw	f1, 4(sp)
	fsw	f2, 8(sp)
	call	pow.13
	flw	f1, 8(sp)
	fmul.s	f0, f1, f0
	flw	f1, 4(sp)
	fsub.s	f0, f1, f0
	li	t1, l.132
	flw	f1, 0(t1)
	li	a0, 4
	flw	f2, 0(sp)
	fsw	f0, 12(sp)
	fsw	f1, 16(sp)
	fmv.s	f0, f2
	call	pow.13
	flw	f1, 16(sp)
	fmul.s	f0, f1, f0
	flw	f1, 12(sp)
	fadd.s	f0, f1, f0
	li	t1, l.133
	flw	f1, 0(t1)
	li	a0, 6
	flw	f2, 0(sp)
	fsw	f0, 20(sp)
	fsw	f1, 24(sp)
	fmv.s	f0, f2
	call	pow.13
	flw	f1, 24(sp)
	fmul.s	f0, f1, f0
	flw	f1, 20(sp)
	fsub.s	f0, f1, f0
	j	kernel_cos.18_end
kernel_cos.18_end:
	lw	ra, 28(sp)
	add	sp, sp, 32
	ret
fsin.20:
	add	sp, sp, -24
	sw	ra, 20(sp)
	flw	f1, 8(s11)
	fsw	f1, 0(sp)
	fsw	f0, 4(sp)
	call	flag.2
	flw	f0, 4(sp)
	sw	a0, 8(sp)
	call	min_caml_abs_float
	call	reduction2pi.6
	flw	f1, 0(sp)
	fle.s	f1, f0, t1
	mv	a0, hp
	add	hp, hp, 8
	lw	a1, 8(sp)
	sw	a1, 4(a0)
	fsw	f0, 0(a0)
	j	fgt_cont.213
fgt_else.212:
	fsub.s	f0, f0, f1
	lw	a0, 8(sp)
	fsw	f0, 12(sp)
	call	reverse.8
	mv	a1, hp
	add	hp, hp, 8
	sw	a0, 4(a1)
	flw	f0, 12(sp)
	fsw	f0, 0(a1)
	mv	a0, a1
fgt_cont.213:
	lw	a1, 4(a0)
	flw	f0, 0(a0)
	li	t1, l.140
	flw	f1, 0(t1)
	fle.s	f1, f0, t1
	j	fgt_cont.215
fgt_else.214:
	flw	f1, 0(sp)
	fsub.s	f0, f1, f0
fgt_cont.215:
	li	t1, l.141
	flw	f1, 0(t1)
	sw	a1, 16(sp)
	fle.s	f0, f1, t1
	li	t1, l.140
	flw	f1, 0(t1)
	fsub.s	f0, f1, f0
	call	kernel_cos.18
	j	fgt_cont.217
fgt_else.216:
	call	kernel_sin.16
fgt_cont.217:
	lw	a0, 16(sp)
	call	add_sign.10
	j	fsin.20_end
fsin.20_end:
	lw	ra, 20(sp)
	add	sp, sp, 24
	ret
fcos.22:
	add	sp, sp, -24
	sw	ra, 20(sp)
	flw	f1, 8(s11)
	li	a0, 0
	sw	a0, 0(sp)
	fsw	f1, 4(sp)
	call	min_caml_abs_floa;
	call	reduction2pi.6
	flw	f1, 4(sp)
	fle.s	f1, f0, t1
	mv	a0, hp
	add	hp, hp, 8
	lw	a1, 0(sp)
	sw	a1, 4(a0)
	fsw	f0, 0(a0)
	j	fgt_cont.219
fgt_else.218:
	fsub.s	f0, f0, f1
	lw	a0, 0(sp)
	fsw	f0, 8(sp)
	call	reverse.8
	mv	a1, hp
	add	hp, hp, 8
	sw	a0, 4(a1)
	flw	f0, 8(sp)
	fsw	f0, 0(a1)
	mv	a0, a1
fgt_cont.219:
	lw	a1, 4(a0)
	flw	f0, 0(a0)
	li	t1, l.140
	flw	f1, 0(t1)
	fle.s	f1, f0, t1
	mv	a0, hp
	add	hp, hp, 8
	sw	a1, 4(a0)
	fsw	f0, 0(a0)
	j	fgt_cont.221
fgt_else.220:
	flw	f1, 4(sp)
	fsub.s	f0, f1, f0
	fsw	f0, 12(sp)
	mv	a0, a1
	call	reverse.8
	mv	a1, hp
	add	hp, hp, 8
	sw	a0, 4(a1)
	flw	f0, 12(sp)
	fsw	f0, 0(a1)
	mv	a0, a1
fgt_cont.221:
	lw	a1, 4(a0)
	flw	f0, 0(a0)
	li	t1, l.141
	flw	f1, 0(t1)
	sw	a1, 16(sp)
	fle.s	f0, f1, t1
	li	t1, l.140
	flw	f1, 0(t1)
	fsub.s	f0, f1, f0
	call	kernel_sin.16
	j	fgt_cont.223
fgt_else.222:
	call	kernel_cos.18
fgt_cont.223:
	lw	a0, 16(sp)
	call	add_sign.10
	j	fcos.22_end
fcos.22_end:
	lw	ra, 20(sp)
	add	sp, sp, 24
	ret

min_caml_sin:
	add sp, sp, -8
	sw	ra, 0(sp)
	fsw	f1, 4(sp)
	li	t1, l.154
	flw	f1, 0(t1)
	mv	s11, hp
	add	hp, hp, 16
	li	a0, fsin.20
	sw	a0, 0(s11)
	fsw	f0, 8(s11)
	jrl	a0
	lw	ra, 0(sp)
	flw	f1, 4(sp)
  add sp, sp, 8
  ret

min_caml_cos:
	add sp, sp, -8
	sw	ra, 0(sp)
	fsw	f1, 4(sp)
	li	t1, l.154
	flw	f1, 0(t1)
	mv	s11, hp
	add	hp, hp, 16
	li	a0, fcos.22
	sw	a0, 0(s11)
	fsw	f0, 8(s11)
	jrl	a0
	lw	ra, 0(sp)
	flw	f1, 4(sp)
  add sp, sp, 8
  ret
