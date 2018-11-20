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
(*let rec test_sin x =
  (if x > 3.14 then
    ()
  else
    (let a = sin x in
    let b = fsin x in
    let c = a -. b in
    ((Printf.printf "%f - %f = %f\n" a b c);
     test_sin (x +. 0.05))))
in
let _ = test_sin 0.0 in
let rec test_cos x =
  (if x > 3.14 then
    ()
  else
    (let a = cos x in
    let b = fcos x in
    let c = a -. b in
    ((Printf.printf "%f - %f = %f\n" a b c);
     test_cos (x +. 0.05))))
in
test_cos 0.0*)
(* print_int (truncate (fsin 0.0 +. fcos 0.0)) *)
print_int (int_of_float ((fsin (-9.0) *. -999.518)))
