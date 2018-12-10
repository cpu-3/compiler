open Closure
(* closure.progに対し型検査を行う *)

exception TypeError of Id.t

let tyenv = ref M.empty (* Id.t * Type.t *)

let updateenv x t =
  match M.find_opt x !tyenv with
  | Some(t') -> Typing.unify t t'
  | None -> tyenv := M.add x t !tyenv

(* Closure.t -> Type.t *)
let rec h = function
  | Unit -> Type.Unit
  | Int(_) -> Type.Int
  | Float(_) -> Type.Float
  | Neg x -> updateenv x Type.Int; Type.Int
  | Add (s1, s2) -> updateenv s1 Type.Int; updateenv s2 Type.Int; Type.Int
  | Sub (s1, s2) -> updateenv s1 Type.Int; updateenv s2 Type.Int; Type.Int
  | Mul (s1, s2) -> updateenv s1 Type.Int; updateenv s2 Type.Int; Type.Int
  | Div (s1, s2) -> updateenv s1 Type.Int; updateenv s2 Type.Int; Type.Int
  | FNeg x -> updateenv x Type.Float; Type.Float
  | FAdd (s1, s2) -> updateenv s1 Type.Float; updateenv s2 Type.Float; Type.Float
  | FSub (s1, s2) -> updateenv s1 Type.Float; updateenv s2 Type.Float; Type.Float
  | FMul (s1, s2) -> updateenv s1 Type.Float; updateenv s2 Type.Float; Type.Float
  | FDiv (s1, s2) -> updateenv s1 Type.Float; updateenv s2 Type.Float; Type.Float
  | FSqrt x -> updateenv x Type.Float; Type.Float
  | IfEq (x, y, t1, t2) | IfLE (x, y, t1, t2) ->
      Typing.unify (M.find x !tyenv) (M.find y !tyenv);
      let t1' = h t1 in
      let t2' = h t2 in
      Typing.unify t1' t2'; t1'
  | Let ((x, t), t1, t2) -> let t1' = h t1 in
                            Typing.unify t1' t;
                            tyenv := M.add x t !tyenv;
                            h t2
  | Var(x) -> M.find x !tyenv
  | MakeCls ((x, t), cl, t') -> updateenv x t; h t'
  | AppCls (x, xs) -> (match M.find x !tyenv with
                      | Type.Fun(ts, t) -> List.map2 (fun x t -> updateenv x t) xs ts; t
                      | _ -> raise (TypeError(x)))
  | AppDir (L(l), xs) when (String.length l > 9 && String.equal (String.sub l 0 9) "min_caml_") ->
      (match M.find_opt (String.sub l 9 (String.length l - 9)) !Typing.extenv with
      | Some(Type.Fun(ts, t)) -> List.map2 (fun x t -> updateenv x t) xs ts; t
      | None -> Type.gentyp ()
      | _ -> raise (TypeError(l)))
  | AppDir (L(l), xs) ->
      (match M.find_opt l !tyenv with
      | Some(Type.Fun(ts, t)) -> List.map2 (fun x t -> updateenv x t) xs ts; t
      | None -> Type.gentyp ()
      | _ -> raise (TypeError(l)))
  | Tuple xs -> Type.Tuple(List.map (fun x -> M.find x !tyenv) xs)
  | LetTuple (xs, x, t) -> updateenv x (Type.Tuple(List.map snd xs)); List.iter (fun (x', t') -> updateenv x' t') xs; h t
  | Get (x, y) -> let t = Type.gentyp () in updateenv x (Type.Array(t)); updateenv y Type.Int; t
  | Put (x, y, z) -> updateenv x (Type.Array(M.find z !tyenv)); updateenv y Type.Int; Type.Unit
  | ExtArray (L(x)) -> M.find x !Typing.extenv
  | ExtTuple (L(x)) -> M.find x !Typing.extenv

(* Closure.fundef -> () *)
let g { Closure.name = (Id.L(x), t); Closure.args = yts; Closure.formal_fv = zts; Closure.body = e } =
  tyenv := M.add x t !tyenv;
  tyenv := List.fold_right (fun (x', t') env -> M.add x' t' env) yts !tyenv;
  tyenv := List.fold_right (fun (x', t') env -> M.add x' t' env) zts !tyenv;
  h e; ()

(* Closure.prog -> Closure.prog *)
let f (Prog (fndefs, e)) =
  List.iter g fndefs;
  h e; Prog (fndefs, e)
