type t = (* MinCamlの構文を表現するデータ型 (caml2html: syntax_t) *)
  | Unit
  | Bool of bool
  | Int of int
  | Float of float
  | Not of t
  | Neg of t
  | Add of t * t
  | Sub of t * t
  | Mul of t * t
  | Div of t * t
  | FNeg of t
  | FAdd of t * t
  | FSub of t * t
  | FMul of t * t
  | FDiv of t * t
  | Eq of t * t
  | LE of t * t
  | If of t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of t * t list
  | Tuple of t list
  | LetTuple of (Id.t * Type.t) list * t * t
  | Array of t * t
  | Get of t * t
  | Put of t * t * t
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let rec print_t stx =
    match stx with
    | Unit -> print_string "UNIT"
    | Bool b -> print_string ("BOOL " ^ (string_of_bool b))
    | Int i -> (print_string "INT ";
                print_int i)
    | Float x -> (print_string "FLOAT ";
                  print_float x)
    | Not t -> (print_string "NOT ";
                print_t t)
    | Neg t -> (print_string "NEG ";
                print_t t)
    | FNeg t -> (print_string "FNEG ";
                 print_t t)
    | Add (t1, t2) -> (print_t t1;
                       print_string " + ";
                       print_t t2)
    | Sub (t1, t2) -> (print_t t1;
                   print_string " - ";
                   print_t t2)
    | Mul (t1, t2) -> (print_t t1;
                       print_string " * ";
                       print_t t2)
    | Div (t1, t2) -> (print_t t1;
                   print_string " / ";
                   print_t t2)
    | FAdd (t1, t2) -> (print_t t1;
                   print_string " +. ";
                   print_t t2)
    | FSub (t1, t2) -> (print_t t1;
                   print_string " -. ";
                   print_t t2)
    | FMul (t1, t2) -> (print_t t1;
                   print_string " *. ";
                   print_t t2)
    | FDiv (t1, t2) -> (print_t t1;
                   print_string " /. ";
                   print_t t2)
    | Eq (t1, t2) -> (print_t t1;
                      print_string " = ";
                      print_t t2)
    | LE (t1, t2) -> (print_t t1;
                   print_string " <= ";
                   print_t t2)
    | If (t1, t2, t3) -> (print_string "IF ";
                          print_t t1;
                          print_string " THEN ";
                          print_t t2;
                          print_string " ELSE ";
                          print_t t3)
    | Let ((s, _), t2, t3) -> (print_string ("LET " ^ s ^ " = ");
                               print_t t2;
                               print_string " IN ";
                               print_t t3)
    | Var s -> print_string ("VAR " ^ s)
    | LetRec (fd, t) -> (print_string ("LET REC " ^ (fst fd.name) ^ "(" ^ (fst (List.hd fd.args)));
                         List.iter (fun (s, _) ->
                            print_string (", " ^ s)) (List.tl fd.args);
                         print_string ") = ";
                         print_t fd.body;
                         print_string " IN ";
                         print_t t)
    | App (t1, t2::ts) -> (print_t t1;
                           print_string "(";
                           print_t t2;
                           List.iter (fun t' ->
                               print_string ", ";
                               print_t t') ts;
                           print_string ")")
    | Tuple (t::ts) -> (print_string "[";
                        print_t t;
                        List.iter (fun t' ->
                            print_string ", ";
                            print_t t') ts;
                        print_string "]")
    | LetTuple (s::ss, t1, t2) -> (print_string ("LET (" ^ (fst s));
                                   List.iter (fun (s', _) ->
                                       print_string (", " ^ s')) ss;
                                   print_string ") = ";
                                   print_t t1;
                                   print_string " IN ";
                                   print_t t2)
    | Array (t1, t2) -> (print_string "ARRAY_CREATE ";
                         print_t t1;
                         print_t t2)
    | Get (t1, t2) -> (print_t t1;
                       print_string " . (";
                       print_t t2;
                       print_string ")")
    | Put (t1, t2, t3) -> (print_t t1;
                           print_string " . (";
                           print_t t2;
                           print_string ") <-";
                           print_t t3)
