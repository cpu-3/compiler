let rec min_caml_abs_float x =
  if x < 0.0 then (-1.0) *. x
  else x
in
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
let rec min_caml_atan y =
  let (x, f) = if y < 0.0 then (-1.0 *. y, -1.0) else (y, 1.0) in
  if x < 0.4375 then kernel_atan y else
  if x < 2.4375 then
    f *. (0.7853981633974483 +. (kernel_atan ((x -. 1.0) /. (x  +.
                                                             1.0))))
  else
    f *. (1.5707963267948966 -. (kernel_atan (1.0 /.
                                              x)))
in
let rec min_caml_floor x =
    let y = int_of_float x in
      let y = float_of_int y in
      if x < 0.0 then y -. 1.0 else y
in




let pi = 3.14159265358979
in
let rec flag x = if x < 0.0 then -1.0 else 1.0
in
let rec reduction2pi x =
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
  let flg = flag x in
  let x = abs_float x in
  let x = reduction2pi x in
  let (x, flg) =
    if x >= pi then
      (x -. pi, reverse flg)
    else
      (x, flg) in
  let x = if x >= (pi /. 2.0) then pi -. x else x in
  add_sign flg (
    if x <= (pi /. 4.0)
    then kernel_sin x
    else kernel_cos (pi/.2.0 -. x)) in
let rec fcos x =
  let flg = 1.0 in
  let x = abs_float x in
  let x = reduction2pi x in
  let (x, flg) =
    if x >= pi then
      (x -. pi, reverse flg)
    else
      (x, flg) in
  let (x, flg) =
    if x >= (pi /. 2.0) then
      (pi -. x, reverse flg)
    else
      (x, flg)
  in
  add_sign flg (
    if x <= (pi /. 4.0)
    then kernel_cos x
    else kernel_sin (pi/.2.0 -. x)) in

