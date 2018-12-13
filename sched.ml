open Asm

type ty = (Id.t * Type.t) * exp

type node = {child: node list ref;
             parents: node list ref;
             score: int ref;
             subscore: int ref;
             count: int ref;
             exp: ty ref}

let gen_node exp = {
  count=ref 0;
  child=ref [];
  parents=ref [];
  score=ref 0;
  subscore=ref 0;
  exp=ref exp}

(* 副作用に使うkey *)
let side_effects_key= "!side_effects!"

let rec g cmds' =
  match cmds' with
  | Ans e ->
    let g2 a b =
      let a' = g a in
      let b' = g b in
      (a', b')
    in
    (match e with
     | IfEq(x, y, t1, t2) ->
       let (t1, t2) = g2 t1 t2 in
       Ans(IfEq(x, y, t1, t2))
     | IfLE(x, y, t1, t2) ->
       let (t1, t2) = g2 t1 t2 in
       Ans(IfLE(x, y, t1, t2))
     | IfGE(x, y, t1, t2) ->
       let (t1, t2) = g2 t1 t2 in
       Ans(IfGE(x, y, t1, t2))
     | IfFEq(x, y, t1, t2) ->
       let (t1, t2) = g2 t1 t2 in
       Ans(IfFEq(x, y, t1, t2))
     | IfFLE(x, y, t1, t2) ->
       let (t1, t2) = g2 t1 t2 in
       Ans(IfFLE(x, y, t1, t2))
     | _ -> cmds'
    )
  | Let(_) ->
    let (env, toplevels, cmds) = tot cmds' M.empty [] in
    let cont = g cmds in
    schedule env toplevels cont
and find_dependencies x env =
  try
    let (_, l) = M.find x env in
    l
  with
  |Not_found -> []
and tot cmds env toplevels = match cmds with
    | Let ((id, ty), e, cmds) ->
      let node = gen_node ((id, ty), e) in
      (* まず、すでに使われている変数ならば、
       * すでに使われた場所に対する依存関係を追加*)
      (try
        let (r, dependencies) = M.find id env in
        add_multi node env [r];
        add_multi node env dependencies
      with
      |Not_found -> ());
      (* 次に、レジスタが書き換わるので、環境の
       * idのnodeをリセット *)
      let env = M.add id (node, []) env in
      gen_graph node e env toplevels cmds
    | Ans e ->
      (env, toplevels, cmds)
and search_and_add node x env =
  (* 見つからなければ現在見ているまとまりの中には
   * 依存関係がない、よってtoplevel *)
  try
    let (r, deps) = M.find x env in
    add_multi node env [r];
    M.add x (r, node::deps) env
  with
  |Not_found -> env
and add_depenency node x env =
  try
    let (r, deps) = M.find x env in
    M.add x (r, node::deps) env
  with
  |Not_found ->
    M.add x (node, [node]) env
and search_and_add_multi node env l = match l with
  | [] -> env
  | x::xs ->
    let env = search_and_add node x env in
    search_and_add_multi node env xs
and add_multi node env l = match l with
  | [] -> ()
  | par::xs ->
    par.child := node :: !(par.child);
    node.parents := par :: !(node.parents);
    add_multi node env xs
and gen_graph node exp env toplevels next =
  let env = (match exp with
  | Nop | Li(_) | SetL(_) | Comment(_) ->
    env
  | FLi(_) ->
    add_depenency node side_effects_key env
  | Mv(x) | Neg (x) | FMv(x) | FNeg(x) | FSqrt(x) | Restore(x) ->
    search_and_add node x env
  | Add(x, y) | Sub(x, y) | Mul(x, y) | Div(x, y) | Sll(x, y) ->
    let env = search_and_add node x env in
    (match y with
    | V(y') ->
      search_and_add node y' env
    | C(_) ->
      env)
  | Lw(x, y) | Lfd(x, y) ->
    let env = add_depenency node side_effects_key env in
    let env = search_and_add node x env in
    (match y with
    | V(y') ->
      search_and_add node y' env
    | C(_) ->
      env)
  | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Save(x, y) ->
    let env = search_and_add node x env in
    search_and_add node y env
  | Sw(x, y, z) | Stfd(x, y, z) ->
    let deps = find_dependencies side_effects_key env in
    add_multi node env deps;
    let env = M.add side_effects_key (node, [node]) env in
    let env = search_and_add node x env in
    let env = search_and_add node y env in
    (match z with
    | V(y') ->
      search_and_add node y' env
    | C(_) ->
      env)
  | IfEq (x, y, a, b) | IfLE (x, y, a, b) | IfGE(x, y, a, b) ->
    let env = search_and_add node x env in
    let env = (match y with
    | V(y') ->
      search_and_add node y' env
    | C(_) ->
      env) in
    let a' = g a in
    let b' = g b in
    let exp = (match exp with
    | IfEq(_) -> IfEq(x, y, a', b')
    | IfLE(_) -> IfLE(x, y, a', b')
    | IfGE(_) -> IfGE(x, y, a', b')
    | x -> failwith "fail") in
    let ((id, t), _) = !(node.exp) in
    node.exp := ((id, t), exp);
    env
  | IfFEq(x, y, a, b) | IfFLE(x, y, a, b) ->
    let env = search_and_add node x env in
    let env = search_and_add node y env in
    let a' = g a in
    let b' = g b in
    let exp = (match exp with
    | IfFEq(_) -> IfFEq(x, y, a', b')
    | IfFLE(_) -> IfFLE(x, y, a', b')
    | x -> failwith "fail") in
    let ((id, t), _) = !(node.exp) in
    node.exp := ((id, t), exp);
    env
  | CallCls (x, b, c) ->
    let deps = find_dependencies side_effects_key env in
    add_multi node env deps;
    let env = M.add side_effects_key (node, [node]) env in
    let _ = search_and_add node x env in
    (* handle side effects *)
    let env = search_and_add_multi node env b in
    search_and_add_multi node env c
  | CallDir (_, b, c) ->
    let deps = find_dependencies side_effects_key env in
    add_multi node env deps;
    let env = M.add side_effects_key (node, [node]) env in
    let env = search_and_add_multi node env b in
    search_and_add_multi node env c
  ) in
  let toplevels =
    print_exp exp;
    print_newline ();
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
      if !(x.score) < mn then (!(x.score), x, node::rem)
      else if !(x.score) > mn then  (mn, node, x::rem)
      else (
        let (_, exp) = !(node.exp) in
        node.subscore := -(latency exp);
        let (_, exp) = !(x.exp) in
        x.subscore := -(latency exp);
        if !(x.subscore) < !(node.subscore) then (!(x.score), x, node::rem)
        else (mn, node, x::rem)
      )
    in
    find_minimum xs mn node rem
and find_maximum toplevels mx node rem = match toplevels with
  | [] -> (node, rem)
  | x::xs ->
    let (mx, node, rem) =
      if !(x.score) > mx then (!(x.score), x, node::rem) else (mx, node, x::rem) in
    find_minimum xs mx node rem
and latency_sched env toplevels cont =  match toplevels with
  | [] -> cont
  | x::xs ->
    let (node, toplevels) = find_minimum xs !(x.score) x [] in
    let max x y = if x > y then x else y in
    let rec update toplevels = match toplevels with
      | [] -> ()
      | x::xs ->
        x.score := max (!(x.score) - 1) 0;
        update xs
    in
    update toplevels;
    let rec loop nodes toplevels = match nodes with
      | [] -> toplevels
      | x::xs ->
        (*x.score := !(node.score) + 1;*)
        let (_, exp) = !(node.exp) in
        x.score := latency exp;
        x.count := !(x.count) + 1;
        if !(x.count) =( List.length !(x.parents)) then
          loop xs (x::toplevels)
        else
          loop xs toplevels
    in
    let toplevels = loop !(node.child) toplevels in
    let cont = schedule env toplevels cont in
    let ((id, t), exp) = !(node.exp) in
    Let((id, t), exp, cont)
and resource_sched env toplevels cont = match toplevels with
  | [] -> cont
  | x::xs ->
    let (node, toplevels) = find_maximum xs !(x.score) x [] in
    let rec loop nodes toplevels = match nodes with
      | [] -> toplevels
      | x::xs ->
        (*x.score := !(node.score) + 1;*)
        let (_, exp) = !(node.exp) in
        x.score := latency exp;
        x.count := !(x.count) + 1;
        if !(x.count) =( List.length !(x.parents)) then
          loop xs (x::toplevels)
        else
          loop xs toplevels
    in
    let toplevels = loop !(node.child) toplevels in
    let cont = schedule env toplevels cont in
    let ((id, t), exp) = !(node.exp) in
    Let((id, t), exp, cont)
and schedule env toplevels cont =
  latency_sched env toplevels cont
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
