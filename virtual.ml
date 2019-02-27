(* translation into PowerPC assembly with infinite number of virtual registers *)

open Asm

let globals =  [
     ("n_objects",16);
     ("dummy",17);
     ("objects",29);
     ("screen",89);
     ("viewpoint",92);
     ("light",95);
     ("beam",98);
     ("dummy",99);
     ("and_net",100);
     ("dummy",150);
     ("or_net",151);
     ("solver_dist",152);
     ("intsec_rectside",153);
     ("tmin",154);
     ("intersection_point",155);
     ("intersected_object_id",158);
     ("nvector",159);
     ("texture_color",162);
     ("diffuse_ray",165);
     ("rgb",168);
     ("image_size",171);
     ("image_center",173);
     ("scan_pitch",175);
     ("startp",176);
     ("startp_fast",179);
     ("screenx_dir",182);
     ("screeny_dir",185);
     ("screenz_dir",188);
     ("ptrace_dirvec",191);
     ("dummy",194);
     ("dirvecs",196);
     ("dummy",201);
     ("light_dirvec",264);
     ("dummy",266);
     ("reflections",272);
     ("n_reflections",452);
               ]

let tag2addr tag =
  match List.assoc_opt tag globals with
  | Some(v) -> (Printf.printf "%s => %d\n" tag v; C(v))
  | None -> V(tag)

let data = ref [] (* 浮動小数点数の定数テーブル (caml2html: virtual_data) *)

let classify xts ini addf addi =
  List.fold_left
    (fun acc (x, t) ->
       match t with
       | Type.Unit -> acc
       | Type.Float -> addf acc x
       | _ -> addi acc x t)
    ini
    xts

let separate xts =
  classify
    xts
    ([], [])
    (fun (int, float) x -> (int, float @ [x]))
    (fun (int, float) x _ -> (int @ [x], float))

let expand xts ini addf addi =
  classify
    xts
    ini
    (fun (offset, acc) x ->
       let offset = align offset in
       (offset + 1, addf x offset acc))
    (fun (offset, acc) x t ->
       (offset + 1, addi x t offset acc))

let rec g env = function (* 式の仮想マシンコード生成 (caml2html: virtual_g) *)
  | Closure.Unit -> Ans(Nop)
  | Closure.Int(i) -> Ans(Li(i))
  | Closure.Float(d) ->
    let l =
      try
        (* すでに定数テーブルにあったら再利用 *)
        let (l, _) = List.find (fun (_, d') -> d = d') !data in
        l
      with Not_found ->
        let l = Id.L(Id.genid "l") in
        data := (l, d) :: !data;
        l in
    Ans(FLi(l))
  | Closure.Neg(x) -> Ans(Neg(x))
  | Closure.Xor(x, y) -> Ans(Xor(x, y))
  | Closure.Add(x, y) -> Ans(Add(x, V(y)))
  | Closure.Sub(x, y) -> Ans(Sub(x, V(y)))
  | Closure.Mul(x, y) -> Ans(Mul(x, V(y)))
  | Closure.Div(x, y) -> Ans(Div(x, V(y)))
  | Closure.FNeg(x) -> Ans(FNeg(x))
  | Closure.FAdd(x, y) -> Ans(FAdd(x, y))
  | Closure.FSub(x, y) -> Ans(FSub(x, y))
  | Closure.FMul(x, y) -> Ans(FMul(x, y))
  | Closure.FDiv(x, y) -> Ans(FDiv(x, y))
  | Closure.Fless(x, y) -> Ans(Fless(x, y))
  | Closure.FAbs (x) -> Ans(FAbs(x))
  | Closure.FSqrt(x) -> Ans(FSqrt(x))
  | Closure.FToI(x) -> Ans(FToI(x))
  | Closure.IToF(x) -> Ans(IToF(x))
  | Closure.IfEq(x, y, e1, e2) ->
    (try
    (match M.find x env with
     | Type.Bool | Type.Int -> Ans(IfEq(x, V(y), g env e1, g env e2))
     | Type.Float -> Ans(IfFEq(x, y, g env e1, g env e2))
     | _ -> failwith "equality supported only for bool, int, and float")
     with Not_found -> failwith "hoge")
  | Closure.IfLE(x, y, e1, e2) ->
    (try
    (match M.find x env with
     | Type.Bool | Type.Int -> Ans(IfLE(x, V(y), g env e1, g env e2))
     | Type.Float -> Ans(IfFLE(x, y, g env e1, g env e2))
     | _ -> failwith "inequality supported only for bool, int, and float")
     with Not_found -> failwith "hoge")
  | Closure.Let((x, t1), e1, e2) ->
    let e1' = g env e1 in
    let e2' = g (M.add x t1 env) e2 in
    concat e1' (x, t1) e2'
  | Closure.Var(x) ->
    (match M.find x env with
     | Type.Unit -> Ans(Nop)
     | Type.Float -> Ans(FMv(x))
     | _ -> Ans(Mv(x)))
  | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = ys }, e2) -> (* クロージャの生成 (caml2html: virtual_makecls) *)
    (* Closureのアドレスをセットしてから、自由変数の値をストア *)
    let e2' = g (M.add x t env) e2 in
    let offset, store_fv =
      expand
        (List.map (fun y -> (y, M.find y env)) ys)
        (1, e2')
        (fun y offset store_fv -> seq(Stfd(y, V(x), C(offset)), store_fv))
        (fun y _ offset store_fv -> seq(Sw(y, V(x), C(offset)), store_fv)) in
    Let((x, t), Mv(reg_hp),
        Let((reg_hp, Type.Int), Add(reg_hp, C(align offset)),
            let z = Id.genid "l" in
            Let((z, Type.Int), SetL(l),
                seq(Sw(z, V(x), C(0)),
                    store_fv))))
  | Closure.AppCls(x, ys) ->
    let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
    Ans(CallCls(x, int, float))
  | Closure.AppDir(Id.L(x), ys) ->
    (try(
    let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
    Ans(CallDir(Id.L(x), int, float)))
     with Not_found -> failwith "hoge")

  | Closure.Tuple(xs) -> (* 組の生成 (caml2html: virtual_tuple) *)
    let y = Id.genid "t" in
    let (offset, store) =
      expand
        (List.map (fun x -> (x, M.find x env)) xs)
        (0, Ans(Mv(y)))
        (fun x offset store -> seq(Stfd(x, V(y), C(offset)), store))
        (fun x _ offset store -> seq(Sw(x, V(y), C(offset)), store))  in
    Let((y, Type.Tuple(List.map (fun x -> M.find x env) xs)), Mv(reg_hp),
        Let((reg_hp, Type.Int), Add(reg_hp, C(align offset)),
            store))
  | Closure.LetTuple(xts, y, e2) ->
    let s = Closure.fv e2 in
    let (offset, load) =
      expand
        xts
        (0, g (M.add_list xts env) e2)
        (fun x offset load ->
           if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
             fletd(x, Lfd(V(y), C(offset)), load))
        (fun x t offset load ->
           if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
             Let((x, t), Lw(V(y), C(offset)), load)) in
    load
  | Closure.Get(x, y) -> (* 配列の読み出し (caml2html: virtual_get) *)
    (try
    (match M.find x env with
     | Type.Array(Type.Unit) -> Ans(Nop)
     | Type.Array(Type.Float) -> Ans(Lfd(V(x), V(y)))
     | Type.Array(_) -> Ans(Lw(V(x), V(y)))
     | _ -> assert false)
     with Not_found -> failwith "hoge")
  | Closure.Put(x, y, z) ->
    (try
    (match M.find x env with
     | Type.Array(Type.Unit) -> Ans(Nop)
     | Type.Array(Type.Float) -> Ans(Stfd(z, V(x), V(y)))
     | Type.Array(_) -> Ans(Sw(z, V(x), V(y)))
     | _ -> assert false)
     with Not_found -> failwith "hoge")
  | Closure.GetE(x, y, t) -> (* 配列の読み出し (caml2html: virtual_get) *)
    (try
    (match t with
     | Type.Unit -> Ans(Nop)
     | Type.Float -> Ans(Lfd(tag2addr x, V(y)))
     | _ -> Ans(Lw(tag2addr x, V(y))))
     with Not_found -> failwith "hoge")
  | Closure.PutE(x, y, z, t) ->
    (try
    (match t with
     | Type.Unit -> Ans(Nop)
     | Type.Float -> Ans(Stfd(z, tag2addr x, V(y)))
     | _ -> Ans(Sw(z, tag2addr x, V(y)))
    )
     with Not_found -> failwith "hoge")
  | Closure.ExtArray(Id.L(x), t) -> Ans(SetL(Id.L("min_caml_" ^ x)))
  | Closure.ExtTuple(Id.L(x), t) -> Ans(SetL(Id.L("min_caml_" ^ x)))

(* 関数の仮想マシンコード生成 (caml2html: virtual_h) *)
let h { Closure.name = (Id.L(x), t); Closure.args = yts; Closure.formal_fv = zts; Closure.body = e } =
  let (int, float) = separate yts in
  let (offset, load) =
    expand
      zts
      (1, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
      (fun z offset load -> fletd(z, Lfd(V(x), C(offset)), load))
      (fun z t offset load -> Let((z, t), Lw(V(x), C(offset)), load)) in
  match t with
  | Type.Fun(_, t2) ->
    { name = Id.L(x); args = int; fargs = float; body = load; ret = t2 }
  | _ -> assert false

(* プログラム全体の仮想マシンコード生成 (caml2html: virtual_f) *)
let f (Closure.Prog(fundefs, e)) =
  data := [];
  let fundefs = List.map h fundefs in
  let e = g M.empty e in
  Prog(!data, fundefs, e)
