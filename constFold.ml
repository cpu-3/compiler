open KNormal
open List

let memi x env =
  try (match M.find x env with Int(_) -> true | _ -> false)
  with Not_found -> false
let memf x env =
  try (match M.find x env with Float(_) -> true | _ -> false)
  with Not_found -> false
let memt x env =
  try (match M.find x env with Tuple(_) -> true | _ -> false)
  with Not_found -> false

let rec tuplesize x =
  match x with
  | Type.Tuple xs -> fold_right (+) (map tuplesize xs) 0
  | _ -> 1

let findi x env = (match M.find x env with Int(i) -> i | _ -> raise Not_found)
let findf x env = (match M.find x env with Float(d) -> d | _ -> raise Not_found)
let findt x env = (match M.find x env with
                   | Tuple(ys, Type.Tuple(xs)) ->
                       let l = map tuplesize xs in
                       let size = fold_right (+) l 0 in
                       let indexlist = fold_right (fun i (a::r) -> (a-i)::a::r) l [size] in
                       map (fun i -> nth ys i) (rev (tl (rev indexlist)))
                   | Tuple(ys, _) -> ys
                   | _ -> raise Not_found)


let rec g env = function (* 定数畳み込みルーチン本体 (caml2html: constfold_g) *)
  | Var(x) when memi x env -> Int(findi x env)
  (* | Var(x) when memf x env -> Float(findf x env) *)
  (* | Var(x) when memt x env -> Tuple(findt x env) *)
  | Neg(x) when memi x env -> Int(-(findi x env))
  | Add(x, y) when memi x env && memi y env -> Int(findi x env + findi y env) (* 足し算のケース (caml2html: constfold_add) *)
  | Add(x, y) when memi x env && findi x env = 0 -> Var(y)
  | Add(x, y) when memi y env && findi y env = 0 -> Var(x)
  | Sub(x, y) when memi x env && memi y env -> Int(findi x env - findi y env)
  | Sub(x, y) when memi y env && findi y env = 0 -> Var(x)
  | FNeg(x) when memf x env -> Float(-.(findf x env))
  | FAdd(x, y) when memf x env && memf y env -> Float(findf x env +. findf y env)
  | FSub(x, y) when memf x env && memf y env -> Float(findf x env -. findf y env)
  | FMul(x, y) when memf x env && memf y env -> Float(findf x env *. findf y env)
  | FDiv(x, y) when memf x env && memf y env -> Float(findf x env /. findf y env)
  | FAdd(x, y) when memf x env && Asm.is_famous_fval (findf x env) ->
    FAddF(y, (findf x env))
  | FSub(x, y) when memf x env && Asm.is_famous_fval (findf x env) ->
    FSubFL (y, (findf x env))
  | FMul(x, y) when memf x env && Asm.is_famous_fval (findf x env) ->
    FMulF(y, (findf x env))
  | FAdd(x, y) when memf y env && Asm.is_famous_fval (findf y env) ->
    FAddF(x, (findf y env))
  | FSub(x, y) when memf y env && Asm.is_famous_fval (findf y env) ->
    FSubFR (x, (findf y env))
  | FMul(x, y) when memf y env && Asm.is_famous_fval (findf y env) ->
    FMulF(x, (findf y env))
  | IfEq(x, y, e1, e2) when memi x env && memi y env -> if findi x env = findi y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) when memf x env && memf y env -> if findf x env = findf y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env e1, g env e2)
  | IfLE(x, y, e1, e2) when memi x env && memi y env -> if findi x env <= findi y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) when memf x env && memf y env -> if findf x env <= findf y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env e1, g env e2)
  | Let((x, t), e1, e2) -> (* letのケース (caml2html: constfold_let) *)
      let e1' = g env e1 in
      let e2' = g (M.add x e1' env) e2 in
      Let((x, t), e1', e2')
  | LetRec({ name = x; args = ys; body = e1 }, e2) ->
      LetRec({ name = x; args = ys; body = g env e1 }, g env e2)
  | LetTuple(xts, y, e) when memt y env ->
      fold_left2
        (fun e' xt z -> Let(xt, Var(z), e'))
        (g env e)
        xts
        (findt y env)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env e)
  | e -> e

let f = g M.empty
