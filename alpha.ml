(* rename identifiers to make them unique (alpha-conversion) *)

open KNormal

let find x env = try M.find x env with Not_found -> x

(* 共通部分式削除 *)
let rec g' e emap =
  try if Elim.effect e then raise Not_found else let x = List.assoc e emap in Var(x)
  with Not_found ->
    match e with
    | IfEq(x, y, e1, e2) -> IfEq(x, y, g' e1 emap, g' e2 emap)
    | IfLE(x, y, e1, e2) -> IfLE(x, y, g' e1 emap, g' e2 emap)
    | Let((x, t), e1, e2) ->
        let e1' = g' e1 emap in
        let emap' = match e1' with
                      | Var(_) -> emap
                      | _ -> (e1, x)::emap; in
        Let((x, t), e1', g' e2 emap')
    | LetRec(fd, e) -> LetRec(fd, g' e emap)
    | LetTuple(xts, y, e) -> LetTuple(xts, y, g' e emap)
    | _ -> e

let rec g env = function (* α変換ルーチン本体 (caml2html: alpha_g) *)
  | Unit -> Unit
  | Int(i) -> Int(i)
  | Float(d) -> Float(d)
  | Neg(x) -> Neg(find x env)
  | Xor(x, y) -> Xor(find x env, find y env)
  | Add(x, y) -> Add(find x env, find y env)
  | Sub(x, y) -> Sub(find x env, find y env)
  | Mul(x, y) -> Mul(find x env, find y env)
  | Div(x, y) -> Div(find x env, find y env)
  | FNeg(x) -> FNeg(find x env)
  | FAdd(x, y) -> FAdd(find x env, find y env)
  | FSub(x, y) -> FSub(find x env, find y env)
  | FMul(x, y) -> FMul(find x env, find y env)
  | FAddF(x, y) -> FAddF(find x env, y)
  | FSubFL(x, y) -> FSubFL(find x env, y)
  | FSubFR(x, y) -> FSubFR(find x env, y)
  | FMulF(x, y) -> FMulF(find x env, y)
  | FDiv(x, y) -> FDiv(find x env, find y env)
  | IfEq(x, y, e1, e2) -> IfEq(find x env, find y env, g env e1, g env e2)
  | IfLE(x, y, e1, e2) -> IfLE(find x env, find y env, g env e1, g env e2)
  | Let((x, t), e1, e2) -> (* letのα変換 (caml2html: alpha_let) *)
      let x' = Id.genid x in
      Let((x', t), g env e1, g (M.add x x' env) e2)
  | Var(x) -> Var(find x env)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let recのα変換 (caml2html: alpha_letrec) *)
      let env = M.add x (Id.genid x) env in
      let ys = List.map fst yts in
      let env' = M.add_list2 ys (List.map Id.genid ys) env in
      LetRec({ name = (find x env, t);
               args = List.map (fun (y, t) -> (find y env', t)) yts;
               body = g env' e1 },
             g env e2)
  | App(x, ys) -> App(find x env, List.map (fun y -> find y env) ys)
  | Tuple(xs, y) -> Tuple(List.map (fun x -> find x env) xs, y)
  | LetTuple(xts, y, e) -> (* LetTupleのα変換 (caml2html: alpha_lettuple) *)
      let xs = List.map fst xts in
      let env' = M.add_list2 xs (List.map Id.genid xs) env in
      LetTuple(List.map (fun (x, t) -> (find x env', t)) xts,
               find y env,
               g env' e)
  | Get(x, y) -> Get(find x env, find y env)
  | Put(x, y, z) -> Put(find x env, find y env, find z env)
  | GetE(x, y, t) -> GetE(x, find y env, t)
  | PutE(x, y, z, t) -> PutE(x, find y env, find z env, t)
  | ExtArray(x, t) -> ExtArray(x, t)
  | ExtTuple(x, t) -> ExtTuple(x, t)
  | ExtFunApp(x, ys) -> ExtFunApp(x, List.map (fun y -> find y env) ys)

let f e = g' (g M.empty e) []
