let rec itof_kern x =
  let y = x + 1258291200 in
  let z = union_itof y in
  z -. 8388608.0
in
let rec itof2 x y =
  if x < 8388608 then
    (x, y)
  else
    itof2 (x - 8388608) (8388608.0 +. y)
in
let rec min_caml_itof x =
  let xd = if x < 0 then -x else x in
  let (xd, y) = itof2 xd 0.0 in
  let z = (itof_kern xd) +. y in
  if x < 0 then -.z else z
in
let rec ftoi_kern x =
  let y = x +. 8388608.0 in
  let z = union_ftoi y in
  z - 1258291200
in
let rec ftoi2 x y =
  if x < 8388608.0 then
    (x, y)
  else
    ftoi2 (x -. 8388608.0) (y + 8388608)
in
let rec min_caml_ftoi x =
  let xd = if x < 0.0 then -.x else x in
  if xd < 0.5 then 0
  else
    let xd = xd -. 0.5 in
    let (xd, y) = ftoi2 xd 0 in
    let z = (ftoi_kern xd) + y in
    if x < 0.0 then -z else z
in
print_int (1000);
print_int (min_caml_ftoi (min_caml_itof (-10)));
print_int (min_caml_ftoi (-5.1));
print_int (min_caml_ftoi (0.01));
print_int (min_caml_ftoi (0.54));
print_int (floor (-0.54));
print_int (floor (3.9));
print_int (floor (0.1))
