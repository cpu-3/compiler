let rec loop x ub dx =
  let _ = print_int (int_of_float ((cos x) *. 1000.0)) in
  let _ = print_newline () in
  if x > ub then () else (loop (x +. dx) ub dx)
in
loop (-10.0) (10.0) 0.1
