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

let print_t = function
  | Unit -> print_string "Unit"
  | Bool -> print_string "Bool"
  | Int -> print_string "Int"
  | Float -> print_string "Float"
  | Fun (_, _) (* arguments are uncurried *) -> print_string "Fun"
  | Tuple _ -> print_string "Tuple"
  | Array _ -> print_string "Array"
  | Var _ -> print_string "Var"
