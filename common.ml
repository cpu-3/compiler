open KNormal

module MK =
  Map.Make
    (struct
      type t = KNormal.t
      let compare = compare
    end)
include M

(* 最後に副作用があったタイミング *)
let point = ref 0

let rec effect = function
  | Let(_, e1, e2) -> effect e1
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> effect e1 || effect e2
  | LetRec(_, e) (*| LetTuple(_, _, e)*) -> effect e
  | App _ | Put _ | ExtFunApp _ | PutE _ -> true
  | _ -> false

let rec h x env =
  if effect x then
    point := !point + 1;

  match x with
  | LetRec (d, x) ->
    LetRec({name = d.name;
            args = d.args;
            body = h d.body env},
           h x env)
  | LetTuple (l, id, x) ->
    LetTuple(l, id, h x env)
  | IfEq (a, b, x, y) ->
    IfEq (a, b, h x env, h y env)
  | IfLE (a, b, x, y) ->
    IfLE (a, b, h x env, h y env)
  | Let ((id, t), a, b) ->
    (match a with
    | Get _ | GetE _ ->
      (try (
        let (id', p) = MK.find a env in
        let _ = print_t a in
        let _ = Printf.printf "\t %d %d\n" p !point in
        if p = !point then
          Let ((id, t), Var id', h b env)
        else
          Let ((id, t), a, h b (MK.add a (id, !point) env)))
       with Not_found ->
         Let ((id, t), a, h b (MK.add a (id, !point) env)))
    | _ -> Let ((id, t), a, h b env)
    )
  | v -> v




let rec g x env = match x with
  | Let ((id, t), a, b) ->
    (match a with
    | Int _ | Float _
    | Neg _ (*| Xor _*) | Add _ | Sub _ (*| Mul _
    | Div _*) | FNeg _ | FAdd _ | FSub _ | FMul _
    | FDiv _
    ->
      (try (
        let id' = MK.find a env in
        Let ((id, t), Var id', g b env)
      )
      (* A正規形であることを仮定している *)
      with Not_found ->
        Let ((id, t), a, g b (MK.add a id env)))
    | _ -> Let ((id, t), a, g b env)
    )
  | LetRec (d, x) ->
    LetRec({name = d.name;
            args = d.args;
            body = g d.body env},
           g x env)
  | LetTuple (l, id, x) ->
    LetTuple(l, id, g x env)
  | IfEq (a, b, x, y) ->
    IfEq (a, b, g x env, g y env)
  | IfLE (a, b, x, y) ->
    IfLE (a, b, g x env, g y env)
  | v -> v


let f x = point := 0; (h (g x MK.empty) MK.empty)

