(* give names to intermediate values (K-normalization) *)

(* Label or Register *)
type label = L of Id.t | R of Id.t

type t = (* K正規化後の式 (caml2html: knormal_t) *)
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Xor of Id.t * Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | Mul of Id.t * Id.t
  | Div of Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | FAddF of Id.t * float (* fadd with famous value *)
  | FSubFL of Id.t * float (* fsub with famous value at left *)
  | FSubFR of Id.t * float (* fsub with famous value at right *)
  | FMulF of Id.t * float
  | IfEq of Id.t * Id.t * t * t (* 比較 + 分岐 (caml2html: knormal_branch) *)
  | IfLE of Id.t * Id.t * t * t (* 比較 + 分岐 *)
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list * Type.t (* 要素のリスト(平坦化あり), 型(平坦化なし) *)
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | GetE of Id.t * Id.t * Type.t
  | PutE of Id.t * Id.t * Id.t * Type.t
  | ExtArray of Id.t * Type.t
  | ExtTuple of Id.t * (Type.t list)
  | ExtFunApp of Id.t * Id.t list
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let rec fv = function (* 式に出現する（自由な）変数 (caml2html: knormal_fv) *)
  | Unit | Int(_) | Float(_) | ExtArray(_) | ExtTuple(_) -> S.empty
  | Neg(x) | FNeg(x) | GetE(_, x, _) | FAddF(x, _) | FSubFL(x, _) | FSubFR(x, _) | FMulF(x, _) -> S.singleton x
  | Xor(x, y) | Add(x, y) | Sub(x, y) | Mul(x, y) | Div(x, y) | FAdd(x, y) |
    FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) | PutE(_, x, y, _) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2) | IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
      let zs = S.diff (fv e1) (S.of_list (List.map fst yts)) in
      S.diff (S.union zs (fv e2)) (S.singleton x)
  | App(x, ys) -> S.of_list (x :: ys)
  | Tuple(xs, _) | ExtFunApp(_, xs) -> S.of_list xs
  | Put(x, y, z) -> S.of_list [x; y; z]
  | LetTuple(xs, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xs)))

let insert_let (e, t) k = (* letを挿入する補助関数 (caml2html: knormal_insert) *)
  match e with
  | Var(x) -> k x
  | _ ->
      let x = Id.gentmp t in
      let e', t' = k x in
      Let((x, t), e, e'), t'

let rec g env expr tplty = (* K正規化ルーチン本体 (caml2html: knormal_g) *)
  match expr with
  | Syntax.Unit -> Unit, Type.Unit
  | Syntax.Bool(b) -> Int(if b then 1 else 0), Type.Int (* 論理値true, falseを整数1, 0に変換 (caml2html: knormal_bool) *)
  | Syntax.Int(i) -> Int(i), Type.Int
  | Syntax.Float(d) -> Float(d), Type.Float
  | Syntax.Not(e) -> g env (Syntax.If(e, Syntax.Bool(false), Syntax.Bool(true))) tplty
  | Syntax.Neg(e) ->
      insert_let (g env e tplty)
        (fun x -> Neg(x), Type.Int)
  | Syntax.Add(e1, e2) -> (* 足し算のK正規化 (caml2html: knormal_add) *)
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y -> Add(x, y), Type.Int))
  | Syntax.Sub(e1, e2) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y -> Sub(x, y), Type.Int))
  | Syntax.Mul(e1, e2) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y -> Mul(x, y), Type.Int))
  | Syntax.Div(e1, e2) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y -> Div(x, y), Type.Int))
  | Syntax.FNeg(e) ->
      insert_let (g env e tplty)
        (fun x -> FNeg(x), Type.Float)
  | Syntax.FAdd(e1, e2) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y -> FAdd(x, y), Type.Float))
  | Syntax.FSub(e1, e2) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y -> FSub(x, y), Type.Float))
  | Syntax.FMul(e1, e2) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y -> FMul(x, y), Type.Float))
  | Syntax.FDiv(e1, e2) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y -> FDiv(x, y), Type.Float))
  | Syntax.Eq _ | Syntax.LE _ as cmp ->
      g env (Syntax.If(cmp, Syntax.Bool(true), Syntax.Bool(false))) tplty
  | Syntax.If(Syntax.Not(e1), e2, e3) -> g env (Syntax.If(e1, e3, e2)) tplty (* notによる分岐を変換 (caml2html: knormal_not) *)
  | Syntax.If(Syntax.Eq(e1, e2), e3, e4) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y ->
              let e3', t3 = g env e3 tplty in
              let e4', t4 = g env e4 tplty in
              IfEq(x, y, e3', e4'), t3))
  | Syntax.If(Syntax.LE(e1, e2), e3, e4) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y ->
              let e3', t3 = g env e3 tplty in
              let e4', t4 = g env e4 tplty in
              IfLE(x, y, e3', e4'), t3))
  | Syntax.If(e1, e2, e3) -> g env (Syntax.If(Syntax.Eq(e1, Syntax.Bool(false)), e3, e2)) tplty (* 比較のない分岐を変換 (caml2html: knormal_if) *)
  | Syntax.Let((x, t), e1, e2) ->
      let rec flatten x = (* syntax.t -> [syntax.t] *)
        match x with
        | Syntax.Tuple(xs) -> List.concat (List.map flatten xs)
        | _ -> [x] in
      let e1', t1 = g env e1 tplty in
      let e1', t1 =
        match e1 with
        | Syntax.Tuple(xs) -> g env (Syntax.Tuple (flatten e1)) t1
        | _ -> e1', t1 in
      let e2', t2 = g (M.add x t env) e2 tplty in
      Let((x, t), e1', e2'), t2
  | Syntax.Var(x) when M.mem x env -> Var(x), M.find x env
  | Syntax.Var(x) -> (* 外部配列の参照 (caml2html: knormal_extarray) *)
      (match M.find x !Typing.extenv with
      | Type.Array(s) as t -> ExtArray (x, s), t
      | Type.Tuple(s) as t -> ExtTuple (x, s), t
      | _ -> failwith (Printf.sprintf "external variable %s does not have an array type" x))
  | Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2) ->
      let env' = M.add x t env in
      let e2', t2 = g env' e2 tplty in
      let e1', t1 = g (M.add_list yts env') e1 tplty in
      LetRec({ name = (x, t); args = yts; body = e1' }, e2'), t2
  | Syntax.App(Syntax.Var(f), e2s) when not (M.mem f env) -> (* 外部関数の呼び出し (caml2html: knormal_extfunapp) *)
      (match M.find f !Typing.extenv with
      | Type.Fun(_, t) ->
          let rec bind xs = function (* "xs" are identifiers for the arguments *)
            | [] -> ExtFunApp(f, xs), t
            | e2 :: e2s ->
                insert_let (g env e2 tplty)
                  (fun x -> bind (xs @ [x]) e2s) in
          bind [] e2s (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.App(Syntax.Var("xor"), [e1;e2]) ->
      insert_let (g env e1 tplty)
        (fun x -> insert_let (g env e2 tplty)
            (fun y -> Xor(x, y), Type.Int))
  | Syntax.App(e1, e2s) ->
      (match g env e1 tplty with
      | _, Type.Fun(_, t) as g_e1 ->
          insert_let g_e1
            (fun f ->
              let rec bind xs = function (* "xs" are identifiers for the arguments *)
                | [] -> App(f, xs), t
                | e2 :: e2s ->
                    insert_let (g env e2 tplty)
                      (fun x -> bind (xs @ [x]) e2s) in
              bind [] e2s) (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.Tuple(es) ->
      let rec bind xs ts = function (* "xs" and "ts" are identifiers and types for the elements *)
        | [] -> Tuple(xs, tplty), Type.Tuple(ts)
        | e :: es ->
            let _, t as g_e = g env e tplty in
            insert_let g_e
              (fun x -> bind (xs @ [x]) (ts @ [t]) es) in
      bind [] [] es
  | Syntax.LetTuple(xts, e1, e2) ->
      insert_let (g env e1 tplty)
        (fun y ->
          let e2', t2 = g (M.add_list xts env) e2 tplty in
          LetTuple(xts, y, e2'), t2)
  | Syntax.Array(e1, e2) ->
      insert_let (g env e1 tplty)
        (fun x ->
          let _, t2 as g_e2 = g env e2 tplty in
          insert_let g_e2
            (fun y ->
              let l =
                match t2 with
                | Type.Float -> "create_float_array"
                | _ -> "create_array" in
              ExtFunApp(l, [x; y]), Type.Array(t2)))
  | Syntax.Get(e1, e2) ->
      (match g env e1 tplty with
        | ExtArray(x, _), Type.Array(t) ->
          insert_let (g env e2 tplty)
            (fun y -> GetE(x, y, t), t)
        | _, Type.Array(t) as g_e1 ->
          insert_let g_e1
            (fun x -> insert_let (g env e2 tplty)
                (fun y -> Get(x, y), t))
      | _ -> assert false)
  | Syntax.Put(e1, e2, e3) ->
      (match g env e1 tplty with
        | ExtArray(x, _), Type.Array(t) ->
          insert_let (g env e2 tplty)
            (fun y -> insert_let (g env e3 tplty)
                (fun z -> PutE(x, y, z, t), Type.Unit))
        | _ ->
          insert_let (g env e1 tplty)
            (fun x -> insert_let (g env e2 tplty)
                (fun y -> insert_let (g env e3 tplty)
                    (fun z -> Put(x, y, z), Type.Unit)))
      )

let f e = fst (g M.empty e Type.Unit)

let rec print_t nml =
    match nml with
    | Unit -> print_string "UNIT"
    | Int i -> (print_string "INT ";
                print_int i)
    | Float x -> (print_string "FLOAT ";
                  print_float x)
    | Neg s -> print_string ("NEG " ^ s)
    | FNeg s -> print_string ("FNEG " ^ s)
    | Xor (s1, s2) -> print_string ("XOR (" ^ s1 ^ ", " ^ s2 ^ ")")
    | Add (s1, s2) -> print_string (s1 ^ " + " ^ s2)
    | Sub (s1, s2) -> print_string (s1 ^ " - " ^ s2)
    | Mul (s1, s2) -> print_string (s1 ^ " * " ^ s2)
    | Div (s1, s2) -> print_string (s1 ^ " / " ^ s2)
    | FAdd (s1, s2) -> print_string (s1 ^ " +. " ^ s2)
    | FSub (s1, s2) -> print_string (s1 ^ " -. " ^ s2)
    | FMul (s1, s2) -> print_string (s1 ^ " *. " ^ s2)
    | FDiv (s1, s2) -> print_string (s1 ^ " /. " ^ s2)
    | FAddF (s1, s2) -> Printf.printf ("%s +. %f") s1 s2
    | FSubFL (s1, s2) -> Printf.printf ("%s -. %f") s1 s2
    | FSubFR (s1, s2) -> Printf.printf ("%f -. %s") s2 s1
    | FMulF (s1, s2) -> Printf.printf ("%s *. %f") s1 s2
    | IfEq (s1, s2, t1, t2) -> (print_string ("IF " ^ s1 ^ " = " ^ s2 ^ " THEN ");
                                print_t t1;
                                print_string " ELSE ";
                                print_t t2)
    | IfLE (s1, s2, t1, t2) -> (print_string ("IF " ^ s1 ^ " <= " ^ s2 ^ " THEN ");
                                print_t t1;
                                print_string " ELSE ";
                                print_t t2)
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
    | App (s1, s2::ss) -> (print_string (s1 ^ "(" ^ s2);
                           List.iter (fun s' ->
                               print_string (", " ^ s')) ss;
                           print_string ")")
    | Tuple (s::ss, _) -> (print_string ("(" ^ s);
                        List.iter (fun s' ->
                            print_string (", " ^ s')) ss;
                        print_string ")")
    | LetTuple (s::ss, s1, t2) -> (print_string ("LETTuple (" ^ (fst s));
                                   List.iter (fun (s', _) ->
                                       print_string (", " ^ s')) ss;
                                   print_string (") = " ^ s1 ^ " IN ");
                                   print_t t2)
    | Get (s1, s2) -> print_string (s1 ^ " . (" ^ s2 ^ ")")
    | Put (s1, s2, s3) -> print_string (s1 ^ " . (" ^ s2 ^ ") <- " ^ s3)
    | GetE (s1, s2, _) -> print_string (s1 ^ " . (" ^ s2 ^ ")")
    | PutE (s1, s2, s3, _) -> print_string (s1 ^ " . (" ^ s2 ^ ") <- " ^ s3)
    | ExtArray (s,_) -> print_string ("ExtArray " ^ s)
    | ExtTuple (s,_) -> print_string ("ExtTuple " ^ s)
    | ExtFunApp (f, s::ss) -> (print_string ("ExtFunApp " ^ f ^ "(" ^ s);
                               List.iter (fun s' ->
                                   print_string (", " ^ s')) ss;
                               print_string ")")
