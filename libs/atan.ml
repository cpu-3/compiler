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
    f *. (0.7853981633974483 +. (kernel_atan ((x -. 1.0) /. (x  +. 1.0))))
  else
    f *. (1.5707963267948966 -. (kernel_atan (1.0 /. x)))
in
(*let rec loop x ub dx =
  let _ = Printf.printf "%f: %f\n" x ((atan x) -. (min_caml_atan x)) in
  if x > ub then () else (loop (x +. dx) ub dx)
in
loop (-1.0) 1.0 0.1
*)
print_int (int_of_float (min_caml_atan 1.0))
