open KNormal

module MK =
  Map.Make
    (struct
      type t = KNormal.t
      let compare = compare
    end)
include M

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


let f x = x(*g x MK.empty*)

