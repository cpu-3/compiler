# print_char
min_caml_print_char:
  li s11, 65540
  sb a0, 0(s11)
  ret

# input_char
min_caml_input_char:
  li s11, 65536
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

# truncate (float -> int)
min_caml_truncate:
	j min_caml_ftoi

# int_of_float (float -> int)
min_caml_int_of_float:
	j min_caml_truncate


# float_of_int (int -> float)
min_caml_float_of_int:
	j min_caml_itof



# abs_float
min_caml_abs_float_9:	 # -1.000000
	.word	-1082130432
min_caml_abs_float_8:	 # 0.000000
	.word	0
min_caml_abs_float:
	li	t1, min_caml_abs_float_8
	flw	f1, 0(t1)
	fle.s	t1, f1, f0
	beq	t1, zero, min_caml_abs_fle.s_else.12
    ret
min_caml_abs_fle.s_else.12:
	li	t1, min_caml_abs_float_9
	flw	f1, 0(t1)
	fmul.s	f0, f1, f0
    ret

min_caml_fabs:
	j min_caml_abs_float

min_caml_fless:
	flt.s a0, f0, f1
	ret

# cos, sin
l.150:	 # 3.141593
	.word	1078530011
l.137:	 # 0.785398
	.word	1061752795
l.136:	 # 1.570796
	.word	1070141403
l.129:	 # 0.001370
	.word	984842502
l.128:	 # 0.041664
	.word	1026205577
l.127:	 # 0.500000
	.word	1056964608
l.126:	 # 0.000196
	.word	961373366
l.125:	 # 0.008333
	.word	1007191654
l.124:	 # 0.166667
	.word	1042983596
l.123:	 # 1.000000
	.word	1065353216
l.122:	 # -1.000000
	.word	-1082130432
l.121:	 # 6.283185
	.word	1086918619
l.120:	 # 2.000000
	.word	1073741824
l.119:	 # 0.000000
	.word	0
flag.2:
	li	t1, l.119
	flw	f1, 0(t1)
	fle.s	t1, f1, f0
	beq	t1, zero, fle.s_else.199
	li	a0, 0
    ret
fle.s_else.199:
	li	a0, 1
    ret
inner.103:
	fle.s	t1, f1, f0
	beq	t1, zero, fle.s_else.200
	li	t1, l.120
	flw	f2, 0(t1)
	fmul.s	f1, f1, f2
	j	inner.103
fle.s_else.200:
	fmv.s	f0, f1
    ret
inner.107:
	li	t1, l.121
	flw	f2, 0(t1)
	fle.s	t1, f2, f0
	beq	t1, zero, fle.s_else.201
	fle.s	t1, f1, f0
	beq	t1, zero, fle.s_cont.203
	fsub.s	f0, f0, f1
fle.s_cont.203:
	li	t1, l.120
	flw	f2, 0(t1)
	fdiv.s	f1, f1, f2
	j	inner.107
fle.s_else.201:
	ret
reduction2pi.4:
	add	sp, sp, -8
	sw	ra, 4(sp)
	li	t1, l.121
	flw	f1, 0(t1)
	fsw	f0, 0(sp)
	call	inner.103
	fmv.s	f1, f0
	flw	f0, 0(sp)
	lw	ra, 4(sp)
	add	sp, sp, 8
	j	inner.107
reverse.6:
	li	t1, 0
	bne	a0, t1, beq_else.204
	li	a0, 1
    ret
beq_else.204:
	li	a0, 0
    ret
add_sign.8:
	li	t1, 0
	bne	a0, t1, beq_else.205
    ret
beq_else.205:
	li	t1, l.122
	flw	f1, 0(t1)
	fmul.s	f0, f1, f0
    ret
pow.11:
	add	sp, sp, -8
	sw	ra, 4(sp)
	li	t1, 0
	bne	a0, t1, beq_else.206
	li	t1, l.123
	flw	f0, 0(t1)
	j	pow.11_end
beq_else.206:
	sub	a0, a0, 1
	fsw	f0, 0(sp)
	call	pow.11
	flw	f1, 0(sp)
	fmul.s	f0, f1, f0
	j	pow.11_end
pow.11_end:
	lw	ra, 4(sp)
	add	sp, sp, 8
	ret
kernel_sin.14:
	add	sp, sp, -28
	sw	ra, 24(sp)
	li	t1, l.124
	flw	f1, 0(t1)
	li	a0, 3
	fsw	f0, 0(sp)
	fsw	f1, 4(sp)
	call	pow.11
	flw	f1, 4(sp)
	fmul.s	f0, f1, f0
	flw	f1, 0(sp)
	fsub.s	f0, f1, f0
	li	t1, l.125
	flw	f2, 0(t1)
	li	a0, 5
	fsw	f0, 8(sp)
	fsw	f2, 12(sp)
	fmv.s	f0, f1
	call	pow.11
	flw	f1, 12(sp)
	fmul.s	f0, f1, f0
	flw	f1, 8(sp)
	fadd.s	f0, f1, f0
	li	t1, l.126
	flw	f1, 0(t1)
	li	a0, 7
	flw	f2, 0(sp)
	fsw	f0, 16(sp)
	fsw	f1, 20(sp)
	fmv.s	f0, f2
	call	pow.11
	flw	f1, 20(sp)
	fmul.s	f0, f1, f0
	flw	f1, 16(sp)
	lw	ra, 24(sp)
	fsub.s	f0, f1, f0
	add	sp, sp, 28
	ret
kernel_cos.16:
	add	sp, sp, -32
	sw	ra, 28(sp)
	li	t1, l.123
	flw	f1, 0(t1)
	li	t1, l.127
	flw	f2, 0(t1)
	li	a0, 2
	fsw	f0, 0(sp)
	fsw	f1, 4(sp)
	fsw	f2, 8(sp)
	call	pow.11
	flw	f1, 8(sp)
	fmul.s	f0, f1, f0
	flw	f1, 4(sp)
	fsub.s	f0, f1, f0
	li	t1, l.128
	flw	f1, 0(t1)
	li	a0, 4
	flw	f2, 0(sp)
	fsw	f0, 12(sp)
	fsw	f1, 16(sp)
	fmv.s	f0, f2
	call	pow.11
	flw	f1, 16(sp)
	fmul.s	f0, f1, f0
	flw	f1, 12(sp)
	fadd.s	f0, f1, f0
	li	t1, l.129
	flw	f1, 0(t1)
	li	a0, 6
	flw	f2, 0(sp)
	fsw	f0, 20(sp)
	fsw	f1, 24(sp)
	fmv.s	f0, f2
	call	pow.11
	flw	f1, 24(sp)
	fmul.s	f0, f1, f0
	flw	f1, 20(sp)
	lw	ra, 28(sp)
	fsub.s	f0, f1, f0
	add	sp, sp, 32
	ret
fsin.18:
	add	sp, sp, -24
	sw	ra, 20(sp)
	flw	f1, 8(s11)
	fsw	f1, 0(sp)
	fsw	f0, 4(sp)
	call	flag.2
	flw	f0, 4(sp)
	sw	a0, 8(sp)
	call	min_caml_abs_float
	call	reduction2pi.4
	flw	f1, 0(sp)
	fle.s	t1, f1, f0
	beq	t1, zero, fle.s_else.207
	fsub.s	f0, f0, f1
	lw	a0, 8(sp)
	fsw	f0, 12(sp)
	call	reverse.6
	mv	a1, hp
	add	hp, hp, 8
	sw	a0, 4(a1)
	flw	f0, 12(sp)
	fsw	f0, 0(a1)
	mv	a0, a1
	j	fle.s_cont.208
fle.s_else.207:
	mv	a0, hp
	add	hp, hp, 8
	lw	a1, 8(sp)
	sw	a1, 4(a0)
	fsw	f0, 0(a0)
fle.s_cont.208:
	lw	a1, 4(a0)
	flw	f0, 0(a0)
	li	t1, l.136
	flw	f1, 0(t1)
	fle.s	t1, f1, f0
	beq	t1, zero, fle.s_cont.210
	flw	f1, 0(sp)
	fsub.s	f0, f1, f0
fle.s_cont.210:
	li	t1, l.137
	flw	f1, 0(t1)
	sw	a1, 16(sp)
	fle.s	t1, f0, f1
	beq	t1, zero, fle.s_else.211
	call	kernel_sin.14
	j	fle.s_cont.212
fle.s_else.211:
	li	t1, l.136
	flw	f1, 0(t1)
	fsub.s	f0, f1, f0
	call	kernel_cos.16
fle.s_cont.212:
	lw	a0, 16(sp)
	lw	ra, 20(sp)
	add	sp, sp, 24
	j	add_sign.8
fcos.20:
	add	sp, sp, -24
	sw	ra, 20(sp)
	flw	f1, 8(s11)
	li	a0, 0
	sw	a0, 0(sp)
	fsw	f1, 4(sp)
	call	min_caml_abs_float
	call	reduction2pi.4
	flw	f1, 4(sp)
	fle.s	t1, f1, f0
	beq	t1, zero, fle.s_else.213
	fsub.s	f0, f0, f1
	lw	a0, 0(sp)
	fsw	f0, 8(sp)
	call	reverse.6
	mv	a1, hp
	add	hp, hp, 8
	sw	a0, 4(a1)
	flw	f0, 8(sp)
	fsw	f0, 0(a1)
	mv	a0, a1
	j	fle.s_cont.214
fle.s_else.213:
	mv	a0, hp
	add	hp, hp, 8
	lw	a1, 0(sp)
	sw	a1, 4(a0)
	fsw	f0, 0(a0)
fle.s_cont.214:
	lw	a1, 4(a0)
	flw	f0, 0(a0)
	li	t1, l.136
	flw	f1, 0(t1)
	fle.s	t1, f1, f0
	beq	t1, zero, fle.s_else.215
	flw	f1, 4(sp)
	fsub.s	f0, f1, f0
	fsw	f0, 12(sp)
	mv	a0, a1
	call	reverse.6
	mv	a1, hp
	add	hp, hp, 8
	sw	a0, 4(a1)
	flw	f0, 12(sp)
	fsw	f0, 0(a1)
	mv	a0, a1
	j	fle.s_cont.216
fle.s_else.215:
	mv	a0, hp
	add	hp, hp, 8
	sw	a1, 4(a0)
	fsw	f0, 0(a0)
fle.s_cont.216:
	lw	a1, 4(a0)
	flw	f0, 0(a0)
	li	t1, l.137
	flw	f1, 0(t1)
	sw	a1, 16(sp)
	fle.s	t1, f0, f1
	beq	t1, zero, fle.s_else.217
	call	kernel_cos.16
	j	fle.s_cont.218
fle.s_else.217:
	li	t1, l.136
	flw	f1, 0(t1)
	fsub.s	f0, f1, f0
	call	kernel_sin.14
fle.s_cont.218:
	lw	a0, 16(sp)
	lw	ra, 20(sp)
	add	sp, sp, 24
	j	add_sign.8
min_caml_sin:
	add sp, sp, -8
	sw	ra, 0(sp)
	fsw	f1, 4(sp)
	li	t1, l.150
	flw	f1, 0(t1)
	mv	s11, hp
	add	hp, hp, 16
	li	a0, fsin.18
	sw	a0, 0(s11)
	fsw	f1, 8(s11)
	lw	t1, 0(s11)
	jrl	t1
	lw	ra, 0(sp)
	flw	f1, 4(sp)
  add sp, sp, 8
  ret

min_caml_cos:
	add sp, sp, -8
	sw	ra, 0(sp)
	fsw	f1, 4(sp)
	li	t1, l.150
	flw	f1, 0(t1)
	mv	s11, hp
	add	hp, hp, 16
	li	a0, fcos.20
	sw	a0, 0(s11)
	fsw	f1, 8(s11)
	lw	t1, 0(s11)
	jrl	t1
	lw	ra, 0(sp)
	flw	f1, 4(sp)
  add sp, sp, 8
  ret

atan_l73:	 # 1.570796
	.word	1070141403
atan_l72:	 # 0.785398
	.word	1061752795
atan_l71:	 # 2.437500
	.word	1075576832
atan_l70:	 # 0.437500
	.word	1054867456
atan_l66:	 # 1.000000
	.word	1065353216
atan_l62:	 # -1.000000
	.word	-1082130432
atan_l61:	 # 0.000000
	.word	0
atan_l60:	 # 0.060035
	.word	1031137221
atan_l59:	 # 0.089764
	.word	1035458158
atan_l58:	 # 0.111111
	.word	1038323256
atan_l57:	 # 0.142857
	.word	1041385765
atan_l56:	 # 0.200000
	.word	1045220557
atan_l55:	 # 0.333333
	.word	1051372202
kernel_atan.1:
	add	sp, sp, -4
	sw	ra, 0(sp)
	fmul.s	f1, f0, f0
	fmul.s	f2, f1, f0
	fmul.s	f3, f2, f1
	fmul.s	f4, f3, f1
	fmul.s	f5, f4, f1
	fmul.s	f6, f5, f1
	fmul.s	f1, f6, f1
	li	t1, atan_l55
	flw	f7, 0(t1)
	fmul.s	f2, f7, f2
	fsub.s	f0, f0, f2
	li	t1, atan_l56
	flw	f2, 0(t1)
	fmul.s	f2, f2, f3
	fadd.s	f0, f0, f2
	li	t1, atan_l57
	flw	f2, 0(t1)
	fmul.s	f2, f2, f4
	fsub.s	f0, f0, f2
	li	t1, atan_l58
	flw	f2, 0(t1)
	fmul.s	f2, f2, f5
	fadd.s	f0, f0, f2
	li	t1, atan_l59
	flw	f2, 0(t1)
	fmul.s	f2, f2, f6
	fsub.s	f0, f0, f2
	li	t1, atan_l60
	flw	f2, 0(t1)
	fmul.s	f1, f2, f1
	fadd.s	f0, f0, f1
	j	kernel_atan.1_end
kernel_atan.1_end:
	lw	ra, 0(sp)
	add	sp, sp, 4
	ret
min_caml_atan:
	add	sp, sp, -16
	sw	ra, 12(sp)
	li	t1, atan_l61
	flw	f1, 0(t1)
	fle.s	t1, f1, f0
	beq	t1, zero, atan_fle.s_else.79
	li	t1, atan_l66
	flw	f1, 0(t1)
	mv	a0, hp
	add	hp, hp, 16
	fsw	f1, 8(a0)
	fsw	f0, 0(a0)
	j	atan_fle.s_cont.80
atan_fle.s_else.79:
	li	t1, atan_l62
	flw	f1, 0(t1)
	fmul.s	f1, f1, f0
	li	t1, atan_l62
	flw	f2, 0(t1)
	mv	a0, hp
	add	hp, hp, 16
	fsw	f2, 8(a0)
	fsw	f1, 0(a0)
atan_fle.s_cont.80:
	flw	f1, 8(a0)
	flw	f2, 0(a0)
	li	t1, atan_l70
	flw	f3, 0(t1)
	fle.s	t1, f3, f2
	beq	t1, zero, atan_fle.s_else.81
	li	t1, atan_l71
	flw	f0, 0(t1)
	fle.s	t1, f0, f2
	beq	t1, zero, atan_fle.s_else.82
	li	t1, atan_l73
	flw	f0, 0(t1)
	li	t1, atan_l66
	flw	f3, 0(t1)
	fdiv.s	f2, f3, f2
	fsw	f1, 0(sp)
	fsw	f0, 4(sp)
	fmv.s	f0, f2
	call	kernel_atan.1
	flw	f1, 4(sp)
	fsub.s	f0, f1, f0
	flw	f1, 0(sp)
	fmul.s	f0, f1, f0
	j	min_caml_atan.3_end
atan_fle.s_else.82:
	li	t1, atan_l72
	flw	f0, 0(t1)
	li	t1, atan_l66
	flw	f3, 0(t1)
	fsub.s	f3, f2, f3
	li	t1, atan_l66
	flw	f4, 0(t1)
	fadd.s	f2, f2, f4
	fdiv.s	f2, f3, f2
	fsw	f1, 0(sp)
	fsw	f0, 8(sp)
	fmv.s	f0, f2
	call	kernel_atan.1
	flw	f1, 8(sp)
	fadd.s	f0, f1, f0
	flw	f1, 0(sp)
	fmul.s	f0, f1, f0
	j	min_caml_atan.3_end
atan_fle.s_else.81:
	call	kernel_atan.1
	j	min_caml_atan.3_end
min_caml_atan.3_end:
	lw	ra, 12(sp)
	add	sp, sp, 16
	ret

# fiszero
min_caml_fiszero:
	li	t1, l.119
	flw	f1, 0(t1)
	feq.s	t1, f0, f1
	beq	t1, zero, feq.s_else.9
	li	a0, 1
    ret
feq.s_else.9:
	li	a0, 0
	ret

# fispos
min_caml_fispos:
	li	t1, l.119
	flw	f1, 0(t1)
	fle.s	t1, f0, f1
	beq	t1, zero, fis_pos_fle.s_else.9
	li	a0, 0
    ret
fis_pos_fle.s_else.9:
	li	a0, 1
    ret

# fisneg
min_caml_fisneg:
	li	t1, l.119
	flw	f1, 0(t1)
	fle.s	t1, f1, f0
	beq	t1, zero, fisneg_fle.s_else.9
	li	a0, 0
    ret
fisneg_fle.s_else.9:
	li	a0, 1
    ret

# fsqr
min_caml_fsqr:
	fmul.s	f0, f0, f0
    ret

# fhalf
min_caml_fhalf:
	li	t1, l.127
	flw	f1, 0(t1)
	fmul.s	f0, f0, f1
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
floor_l53:	 # 1.000000
	.word	1065353216
floor_l52:	 # 0.000000
	.word	0
min_caml_floor:
	add	sp, sp, -8
	sw	ra, 4(sp)
	fsw	f0, 0(sp)
	call	min_caml_int_of_float
	call	min_caml_float_of_int
	li	t1, floor_l52
	flw	f1, 0(t1)
	flw	f2, 0(sp)
	fle.s	t1, f1, f2
	beq	t1, zero, floor_fle.s_else.65
	lw	ra, 4(sp)
	add	sp, sp, 8
	ret
floor_fle.s_else.65:
	li	t1, floor_l53
	flw	f1, 0(t1)
	fsub.s	f0, f0, f1
	lw	ra, 4(sp)
	add	sp, sp, 8
	ret
