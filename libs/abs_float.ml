let rec min_caml_abs_float x =
  if x < 0.0 then (-1.0) *. x
  else x
in
print_int (int_of_float (min_caml_abs_float (-5.3)))
