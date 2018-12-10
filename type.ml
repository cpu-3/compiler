type t = (* MinCamlの型を表現するデータ型 (caml2html: type_t) *)
  | Unit
  | Bool
  | Int
  | Float
  | Fun of t list * t (* arguments are uncurried *)
  | Tuple of t list
  | Array of t
  | Var of t option ref

let gentyp () = Var(ref None) (* 新しい型変数を作る *)

let rec print_t = function
  | Unit -> print_string "Unit"
  | Bool -> print_string "Bool"
  | Int -> print_string "Int"
  | Float -> print_string "Float"
  | Fun (t1::ts, t) (* arguments are uncurried *) ->
      (print_string "Fun (";
       print_t t1;
       List.iter (fun t' -> print_string ", "; print_t t') ts;
       print_string ") -> ";
       print_t t)
  | Tuple _ -> print_string "Tuple"
  | Array t -> (print_string "Array (";
                print_t t;
                print_string ")")
  | Var ({ contents = Some(t) }) ->
      (print_string "Var (";
       print_t t;
       print_string ")")
  | Var _ -> print_string "Var"
