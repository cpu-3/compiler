let rec min_caml_floord x =
  let y = int_of_float x in
  let y = float_of_int y in
  if x < 0.0 then y -. 1.0 else y
in
(*print_int*) (int_of_float (min_caml_floord (-5.9)));
print_newline ();
(*print_int*) (int_of_float (min_caml_floord (-5.1)));
print_newline ();
(*print_int*) (int_of_float (min_caml_floord (5.9)));
print_newline ();
(*print_int*) (int_of_float (min_caml_floord (5.2)));
print_newline ();
(*print_int*) (int_of_float (min_caml_floord (-0.4)));
print_newline ();
(*print_int*) (int_of_float (min_caml_floord (-0.1)));
print_newline ();
(*print_int*) (int_of_float (min_caml_floord (-0.01)));
print_newline ();
(*print_int*) (int_of_float (min_caml_floord (0.1)));
print_newline ();
(*print_int*) (int_of_float (min_caml_floord (0.2)));
(*print_int*) (int_of_float (min_caml_floord (-5.9)))
