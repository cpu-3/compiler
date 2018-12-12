open Asm

type ty =
  | AnsN of exp
  | LetN of (Id.t * Type.t) * exp

type node = {child: node list ref;
             parents: node list ref;
             count: int ref;
             exp: ty ref}

let gen_node exp = {
  child=ref [];
  parents=ref [];
  count=ref 0;
  exp=ref exp}

let rec tot cmds env toplevels = match cmds with
    | Let ((id, ty), e, cmds) ->
      let node = gen_node (LetN((id, ty), e)) in
      let env = M.add id node env in
      env, tops, cont = gen_graph node e env toplevels (Some cmds) in
    | Ans e ->
      let node = gen_node (AnsN e) in
      gen_graph node e env toplevels None
and search_and_add node x env toplevels =
  (* 見つからなければ現在見ているまとまりの中には
   * 依存関係がない、よってtoplevel *)
  try
    let par = M.find x env in
    par.child := node :: !(par.child);
    par.parents := par :: !(par.parents);
    toplevels
  with
  | Not_found -> node :: toplevels
and gen_graph node exp env toplevels next =
  let toplevels = (match exp with
  | Nop | Li(_) | FLi(_) | SetL(_) | Comment(_) ->
    toplevels
  | Mv(x) | Neg (x) | FMv(x) | FNeg(x) | FSqrt(x) | Restore(x) ->
    search_and_add node x env toplevels
  | Add(x, y) | Sub(x, y) | Mul(x, y) | Div(x, y) | Sll(x, y)
  | Lw(x, y) | Lfd(x, y) ->
    let toplevels = search_and_add node x env toplevels in
    (match y with
    | V(y') ->
      search_and_add node y' env toplevels
    | C(_) ->
      toplevels)
  | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Save(x, y) ->
    let toplevels = search_and_add node x env toplevels in
    search_and_add node y env toplevels
  | Sw(x, y, z) | Stfd(x, y, z) ->
    let toplevels = search_and_add node x env toplevels in
    let toplevels = search_and_add node y env toplevels in
    (match z with
    | V(y') ->
      search_and_add node y' env toplevels
    | C(_) ->
      toplevels)
  | IfEq (x, y, a, b) | IfLE (x, y, a, b) | IfGE(x, y, a, b) ->
    let toplevels = search_and_add node x env toplevels in
    let toplevels = (match y with
    | V(y') ->
      search_and_add node y' env toplevels
    | C(_) ->
      toplevels) in
    let (env', top') = tot a M.empty [] in
    let a' = schedule env' top' in
    let (env', top') = tot b M.empty [] in
    let b' = schedule env' top' in
    let exp = (match exp with
    | IfEq(_) -> IfEq(x, y, a', b')
    | IfLE(_) -> IfLE(x, y, a', b')
    | IfGE(_) -> IfGE(x, y, a', b')
    | x -> failwith "fail") in
    let _ = (match !(node.exp) with
     | LetN((id, t), _) ->
       node.exp := LetN((id, t), exp)
     | AnsN(e) ->
       node.exp := AnsN(exp)
    )in
    toplevels
  | IfFEq(x, y, a, b) | IfFLE(x, y, a, b) ->
    let toplevels = search_and_add node x env toplevels in
    let toplevels = search_and_add node y env toplevels in
    let (env', top') = tot a M.empty [] in
    let a' = schedule env' top' in
    let (env', top') = tot b M.empty [] in
    let b' = schedule env' top' in
    let exp = (match exp with
    | IfFEq(_) -> IfFEq(x, y, a', b')
    | IfFLE(_) -> IfFLE(x, y, a', b')
    | x -> failwith "fail") in
    let _ = (match !(node.exp) with
     | LetN((id, t), _) ->
       node.exp := LetN((id, t), exp)
     | AnsN(e) ->
       node.exp := AnsN(exp)
    )in
    toplevels
  | CallCls (x, b, c) ->
    let toplevels = search_and_add node x env toplevels in
    let rec loop l top = match l with
      | [] -> top
      | x::xs ->
        let top = search_and_add node x env top in
        loop xs top
    in
    loop c (loop b toplevels)
  | CallDir (_, b, c) ->
    let rec loop l top = match l with
      | [] -> top
      | x::xs ->
        let top = search_and_add node x env top in
        loop xs top
    in
    loop c (loop b toplevels)
  ) in
  match next with
  | Some (cmds) ->
    tot cmds env toplevels
  | None ->
    (env, toplevels)
and schedule env toplevels = match toplevels with
  | [] -> failwith "program error"
  | [x] -> match !(x.exp) with
    | AnsN of e ->
      Ans(e)
    | LetN((id, t), exp) ->
      let rec loop children tops = match children with
        | [] -> tops
        | x::xs ->
