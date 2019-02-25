let rec abs_float x =
  if x < 0.0 then (-1.0) *. x
  else x
in
let rec fabs x = abs_float x in
let rec truncate x = ftoi x in
let rec int_of_float x = truncate x in
let rec float_of_int x = itof x in
let rec fsqr x = x *. x in
let rec fhalf x = x *. 0.5 in

let rec fiszero x = x = 0.0 in
let rec fispos x = x >= 0.0 in
let rec fisneg x = 0.0 >= x in
let rec kernel_atan x =
  let x2 = x *. x in
  let x3 = x2 *. x in
  let x5 = x3 *. x2 in
  let x7 = x5 *. x2 in
  let x9 = x7 *. x2 in
  let x11 = x9 *. x2 in
  let x13 = x11 *. x2 in
  x -. 0.3333333 *. x3
  +. 0.2 *. x5
  -. 0.142857142 *. x7
  +. 0.111111104 *. x9
  -. 0.08976446 *. x11
  +. 0.060035485 *. x13
in
let rec atan y =
  let (x, f) = if y < 0.0 then (-1.0 *. y, -1.0) else (y, 1.0) in
  if x < 0.4375 then kernel_atan y else
  if x < 2.4375 then
    f *. (0.7853981633974483 +. (kernel_atan ((x -. 1.0) /. (x  +.
                                                             1.0))))
  else
    f *. (1.5707963267948966 -. (kernel_atan (1.0 /.
                                              x)))
in
let rec floor x =
    let y = int_of_float x in
      let y = float_of_int y in
      if x < 0.0 then y -. 1.0 else y
in
let rec flag x = if x < 0.0 then -1.0 else 1.0
in
let rec reduction2pi x =
  let pi = 3.14159265358979 in
  let p = pi *. 2.0 in
  let rec inner x p =
    if x >= p then
       inner x (p *. 2.0)
    else
      p
  in
  let p = inner x p in
  let rec inner x p =
    if x >= (pi *. 2.0) then
      inner (if x >= p then x -. p else x) (p /. 2.0)
    else
      x
  in
  inner x p in

let rec reverse flg = -1.0 *. flg in

let rec add_sign flg x =
  flg *. x
in
let rec pow x n =
  if n = 0 then
    1.0
  else
    x *. (pow x (n - 1)) in

let rec kernel_sin x =
  x -. 0.16666668 *. (pow x 3)
   +. 0.008332824 *. (pow x 5)
   -. 0.00019587841  *. (pow x 7) in

let rec kernel_cos x =
  1.0 -. 0.5 *. (pow x 2)
   +. 0.04166368 *. (pow x 4)
   -. 0.0013695068 *. (pow x 6) in

let rec fsin x =
  let pi = 3.14159265358979 in
  let flg = flag x in
  let x = abs_float x in
  let x = reduction2pi x in

  let flg = if x >= pi then reverse flg else flg in
  let x = if x >= pi then x -. pi else x in

  let x = if x >= (pi /. 2.0) then pi -. x else x in
  add_sign flg (
    if x <= (pi /. 4.0)
    then kernel_sin x
    else kernel_cos (pi/.2.0 -. x)) in
let rec fcos x =
  let pi = 3.14159265358979 in
  let flg = 1.0 in
  let x = abs_float x in
  let x = reduction2pi x in

  let flg = if x >= pi then reverse flg else flg in
  let x = if x >= pi then x -. pi else x in

  let flg = if x >= (pi *.0.5) then reverse flg else flg in
  let x = if x >= (pi *. 0.5) then pi -. x else x in

  add_sign flg (
    if x <= (pi /. 4.0)
    then kernel_cos x
    else kernel_sin (pi/.2.0 -. x))
in
let rec sin x = fsin x in
let rec cos x = fcos x in

let rec div10 lb ub target =
  if (ub - lb) <= 1 then
    lb
  else
  let mb = (ub + lb) / 2 in
  let mb8 = mb * 8 in
  let mb10 = mb8 + mb + mb in
  if mb10 > target then
    div10 lb mb target
  else
    div10 mb ub target
in
let rec print_int_inner x =
  if x = 0 then
    ()
  else
    let d = (div10 0 x x) in
    let d8 = d * 8 in
    let d10 = d8 + d + d in
    let _ = print_int_inner d in
    print_char (48 + (x - d10))
in
let rec print_int x =
  if x > 0 then
    print_int_inner x
  else if x = 0 then
    print_char 48
  else
    (print_char 45;
    print_int_inner (-x))
in
