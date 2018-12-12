(* PowerPC assembly with a few virtual instructions *)

type id_or_imm = V of Id.t | C of int
type t = (* 命令の列 (caml2html: sparcasm_t) *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
and exp = (* 一つ一つの命令に対応する式 (caml2html: sparcasm_exp) *)
  | Nop
  | Li of int
  | FLi of Id.l
  | SetL of Id.l
  | Mv of Id.t
  | Neg of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * id_or_imm
  | Mul of Id.t * id_or_imm
  | Div of Id.t * id_or_imm
  | Sll of Id.t * id_or_imm
  | Lw of Id.t * id_or_imm
  | Sw of Id.t * Id.t * id_or_imm
  | FMv of Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | FSqrt of Id.t
  | Lfd of Id.t * id_or_imm
  | Stfd of Id.t * Id.t * id_or_imm
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * id_or_imm * t * t
  | IfLE of Id.t * id_or_imm * t * t
  | IfGE of Id.t * id_or_imm * t * t (* 左右対称ではないので必要 *)
  | IfFEq of Id.t * Id.t * t * t
  | IfFLE of Id.t * Id.t * t * t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list * Id.t list
  | CallDir of Id.l * Id.t list * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 (caml2html: sparcasm_save) *)
  | Restore of Id.t (* スタック変数から値を復元 (caml2html: sparcasm_restore) *)
type fundef = { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = 浮動小数点数テーブル + トップレベル関数 + メインの式 (caml2html: sparcasm_prog) *)
type prog = Prog of (Id.l * float) list * fundef list * t

let fletd(x, e1, e2) = Let((x, Type.Float), e1, e2)
let seq(e1, e2) = Let((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs = (* Array.init 24 (fun i -> Printf.sprintf "_R_%d" i) *)
  [| "%a0"; "%a1"; "%a2"; "%a3"; "%a4"; "%a5"; "%a6"; "%a7";
     "%t0"; "%t2"; "%t3"; "%t4"; "%t5"; "%t6";
     "%s2"; "%s3"; "%s4"; "%s5"; "%s6"; "%s7";
     "%s8"; "%s9"; "%s10"; "%s11" |]
let fregs = Array.init 32 (fun i -> Printf.sprintf "%%f%d" i)
let allregs = Array.to_list regs
let allfregs = Array.to_list fregs
let reg_cl = regs.(Array.length regs - 1) (* closure address (caml2html: sparcasm_regcl) *)
let reg_tmp = "%t1"
let reg_fsw = fregs.(Array.length fregs - 1) (* temporary for swap *)
let reg_link = "%ra" (* link register *)
let reg_sp = "%sp" (* stack pointer *)
let reg_hp = "%hp" (* heap pointer *)
let is_reg x = (x.[0] = '%')

(* super-tenuki *)
let rec remove_and_uniq xs = function
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(* free variables in the order of use (for spilling) (caml2html: sparcasm_fv) *)
let fv_id_or_imm = function V(x) -> [x] | _ -> []
let rec fv_exp = function
  | Nop | Li(_) | FLi(_) | SetL(_) | Comment(_) | Restore(_) -> []
  | Mv(x) | Neg(x) | FMv(x) | FNeg(x) | FSqrt(x) | Save(x, _) -> [x]
  | Add(x, y') | Sub(x, y') | Mul(x, y') | Div(x, y') | Sll(x, y') | Lfd(x, y') | Lw(x, y') -> x :: fv_id_or_imm y'
  | Sw(x, y, z') | Stfd(x, y, z') -> x :: y :: fv_id_or_imm z'
  | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) -> [x; y]
  | IfEq(x, y', e1, e2) | IfLE(x, y', e1, e2) | IfGE(x, y', e1, e2) ->  x :: fv_id_or_imm y' @ remove_and_uniq S.empty (fv e1 @ fv e2) (* uniq here just for efficiency *)
  | IfFEq(x, y, e1, e2) | IfFLE(x, y, e1, e2) -> x :: y :: remove_and_uniq S.empty (fv e1 @ fv e2) (* uniq here just for efficiency *)
  | CallCls(x, ys, zs) -> x :: ys @ zs
  | CallDir(_, ys, zs) -> ys @ zs
and fv = function
  | Ans(exp) -> fv_exp exp
  | Let((x, t), exp, e) ->
      fv_exp exp @ remove_and_uniq (S.singleton x) (fv e)
let fv e = remove_and_uniq S.empty (fv e)

let rec concat e1 xt e2 =
  match e1 with
  | Ans(exp) -> Let(xt, exp, e2)
  | Let(yt, exp, e1') -> Let(yt, exp, concat e1' xt e2)

let align i = (if i mod 8 = 0 then i else i + 4)

let print_id_or_imm = function
  | V(s) -> print_string s
  | C(i) -> print_int i

let rec print_t = function
  | Ans(exp) -> print_string "ans "; print_exp exp
  | Let((s, _), exp, t) ->
      (print_string ("let " ^ s ^ " = ");
      print_exp exp;
      print_string " in ";
      print_newline ();
      print_t t;
      )
and print_exp = function
  | Nop -> print_string "nop"
  | Li(n) -> (print_string "li "; print_int n)
  | FLi(Id.L(l)) -> print_string ("fli " ^ l)
  | SetL(Id.L(l)) -> print_string ("setl " ^ l)
  | Mv(s) -> print_string ("mv " ^ s)
  | Neg(s) -> print_string ("neg " ^ s)
  | Add(s, i) -> (print_string ("add " ^ s ^ " "); print_id_or_imm i)
  | Sub(s, i) -> (print_string ("sub " ^ s ^ " "); print_id_or_imm i)
  | Mul(s, i) -> (print_string ("mul " ^ s ^ " "); print_id_or_imm i)
  | Div(s, i) -> (print_string ("div " ^ s ^ " "); print_id_or_imm i)
  | Sll(s, i) -> (print_string ("sll " ^ s ^ " "); print_id_or_imm i)
  | Lw(s, i) -> (print_string ("lw " ^ s ^ " "); print_id_or_imm i)
  | Sw(s1, s2, i) -> (print_string ("sw " ^ s1 ^ " " ^ s2 ^ " "); print_id_or_imm i)
  | FMv(s) -> print_string ("fmv " ^ s)
  | FNeg(s) -> print_string ("fneg " ^ s)
  | FAdd(s1, s2) -> print_string ("fadd " ^ s1 ^ " " ^ s2 ^ " ")
  | FSub(s1, s2) -> print_string ("fsub " ^ s1 ^ " " ^ s2 ^ " ")
  | FMul(s1, s2) -> print_string ("fmul " ^ s1 ^ " " ^ s2 ^ " ")
  | FDiv(s1, s2) -> print_string ("fdiv " ^ s1 ^ " " ^ s2 ^ " ")
  | FSqrt(s1) -> print_string ("fsqrt " ^ s1 ^ " ")
  | Lfd(s, i) -> (print_string ("lfd " ^ s ^ " "); print_id_or_imm i)
  | Stfd(s1, s2, i) -> (print_string ("stfd " ^ s1 ^ " " ^ s2 ^ " "); print_id_or_imm i)
  | Comment(s) -> (print_string ("comment " ^ s))
  (* virtual instructions *)
  | IfEq(s, i, t1, t2) -> (print_string ("ifeq " ^ s ^ " ");
                           print_id_or_imm i;
                           print_string (" then ");
                           print_t t1;
                           print_string (" else ");
                           print_t t2; print_string " ")
  | IfLE(s, i, t1, t2) -> (print_string ("ifle " ^ s ^ " ");
                           print_id_or_imm i;
                           print_string (" then ");
                           print_t t1;
                           print_string (" else ");
                           print_t t2; print_string " ")
  | IfGE(s, i, t1, t2) -> (print_string ("ifge " ^ s ^ " ");
                           print_id_or_imm i;
                           print_string (" then ");
                           print_t t1;
                           print_string (" else ");
                           print_t t2; print_string " ")
  | IfFEq(s1, s2, t1, t2) -> (print_string ("ifeq " ^ s1 ^ " " ^ s2 ^ " ");
                           print_string (" then ");
                           print_t t1;
                           print_string (" else ");
                           print_t t2; print_string " ")
  | IfFLE(s1, s2, t1, t2) -> (print_string ("ifeq " ^ s1 ^ " " ^ s2 ^ " ");
                           print_string (" then ");
                           print_t t1;
                           print_string (" else ");
                           print_t t2; print_string " ")
  (* closure address, integer arguments, and float arguments *)
  | CallCls(s, ints, floats) ->
      (print_string ("callcls " ^ s ^ " ints: ");
       List.iter print_string ints;
       print_string " floats: ";
       List.iter print_string floats)
  | CallDir(Id.L(l), ints, floats) ->
      (print_string ("calldir " ^ l ^ " ints: ");
       List.iter print_string ints;
       print_string " floats: ";
       List.iter print_string floats)
  | Save(s1, s2) -> print_string ("save " ^ s1 ^ " " ^ s2)
  | Restore(s) -> print_string ("restore " ^ s)

let print_prog (Prog(fls, topfs, e)) =
  (print_string "\n(name, float) =\n";
  List.iter (fun (l, f) ->
    let Id.L(l) = l in
    print_string ("(" ^ l ^ " ");
    print_float f;
    print_string ") ";) fls;
  print_string "\nfundef list =\n";
  List.iter (fun fd ->
    let Id.L(n) = fd.name in
    print_string ("\tname: " ^ n ^ "\n\targs: (");
    List.iter(fun x -> print_string(x ^ ",")) fd.args;
    print_string (")\n\tbody: ");
    print_newline ();
    print_t(fd.body);
    print_string ("\n");) topfs;
  print_string "\n";
  print_t e)


