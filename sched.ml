open Asm

type ty = (Id.t * Type.t) * exp

type node = {child: node list ref;
             parents: node list ref;
             score: int ref;
             exp: ty ref}

let gen_node exp = {
  child=ref [];
  parents=ref [];
  score=ref 0;
  exp=ref exp}

let rec g cmds = match cmds with
  | Ans e ->
    cmds
  | Let((id, t), exp, cmds) ->
    let (env, toplevels, cmds) = tot cmds M.empty [] in
    let cont = g cmds in
    schedule env toplevels cont
and tot cmds env toplevels = match cmds with
    | Let ((id, ty), e, cmds) ->
      let node = gen_node ((id, ty), e) in let env = M.add id node env in
      gen_graph node e env toplevels cmds
    | Ans e ->
      (env, toplevels, cmds)
and search_and_add node x env =
  (* 見つからなければ現在見ているまとまりの中には
   * 依存関係がない、よってtoplevel *)
  try
    let par = M.find x env in
    par.child := node :: !(par.child);
    par.parents := par :: !(par.parents);
  with
  | Not_found -> ()
and gen_graph node exp env toplevels next =
  let _ = (match exp with
  | Nop | Li(_) | FLi(_) | SetL(_) | Comment(_) ->
    ()
  | Mv(x) | Neg (x) | FMv(x) | FNeg(x) | FSqrt(x) | Restore(x) ->
    search_and_add node x env
  | Add(x, y) | Sub(x, y) | Mul(x, y) | Div(x, y) | Sll(x, y)
  | Lw(x, y) | Lfd(x, y) ->
    let _ = search_and_add node x env in
    (match y with
    | V(y') ->
      search_and_add node y' env
    | C(_) ->
      ())
  | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Save(x, y) ->
    let _ = search_and_add node x env in
    search_and_add node y env
  | Sw(x, y, z) | Stfd(x, y, z) ->
    let _ = search_and_add node x env in
    let _ = search_and_add node y env in
    (match z with
    | V(y') ->
      search_and_add node y' env
    | C(_) ->
      ())
  | IfEq (x, y, a, b) | IfLE (x, y, a, b) | IfGE(x, y, a, b) ->
    let _ = search_and_add node x env in
    let _ = (match y with
    | V(y') ->
      search_and_add node y' env
    | C(_) ->
      ()) in
    let a' = g a in
    let b' = g b in
    let exp = (match exp with
    | IfEq(_) -> IfEq(x, y, a', b')
    | IfLE(_) -> IfLE(x, y, a', b')
    | IfGE(_) -> IfGE(x, y, a', b')
    | x -> failwith "fail") in
    let ((id, t), _) = !(node.exp) in
    node.exp := ((id, t), exp)
  | IfFEq(x, y, a, b) | IfFLE(x, y, a, b) ->
    let _ = search_and_add node x env in
    let _ = search_and_add node y env in
    let a' = g a in
    let b' = g b in
    let exp = (match exp with
    | IfFEq(_) -> IfFEq(x, y, a', b')
    | IfFLE(_) -> IfFLE(x, y, a', b')
    | x -> failwith "fail") in
    let ((id, t), _) = !(node.exp) in
    node.exp := ((id, t), exp)
  | CallCls (x, b, c) ->
    let _ = search_and_add node x env in
    let rec loop l = match l with
      | [] -> ()
      | x::xs ->
        let _ = search_and_add node x env in
        loop xs
    in
    (loop b; loop c)
  | CallDir (_, b, c) ->
    let rec loop l = match l with
      | [] -> ()
      | x::xs ->
        let _ = search_and_add node x env in
        loop xs
    in
    (loop b; loop c)
  ) in
  let toplevels =
    (* 依存関係0 *)
    if List.length !(node.parents) = 0 then
      node:: toplevels
    else
      toplevels
  in
  match exp with
  | IfEq(_) | IfLE(_) | IfGE(_) | IfFEq(_) | IfFLE(_) ->
    (env, toplevels, next)
  | _ ->
    match next with
    | Ans(_) -> (env, toplevels, next)
    | Let(_) -> tot next env toplevels
and find_minimum toplevels mn node rem = match toplevels with
  | [] -> (node, rem)
  | x::xs ->
    let (mn, node, rem) =
      if !(x.score) < mn then (!(x.score), x, node::rem) else (mn, node, x::rem) in
    find_minimum xs mn node rem

and schedule env toplevels cont = match toplevels with
  | [] -> cont
  | x::xs ->
    let (node, toplevels) = find_minimum xs !(x.score) x [] in
    let rec loop nodes toplevels = match nodes with
      | [] -> toplevels
      | x::xs ->
        x.score := !(node.score) + 1;
        loop xs (x::toplevels)
    in
    let toplevels = loop !(node.child) toplevels in
    let cont = schedule env toplevels cont in
    let ((id, t), exp) = !(node.exp) in
    Let((id, t), exp, cont)

let rec f' fundefs result = match fundefs with
  | [] -> result
  | x::xs ->
    let body = g x.body in
    let fundef = {name=x.name;
                args=x.args; fargs=x.fargs;
                body=body;
                ret=x.ret}
    in
    f' xs (fundef::result)
let f prog =
  let Prog(l, fundef, main) = prog in
  let main = g main in
  let fundefs = f' fundef []  in
  Prog(l, fundefs, main)
