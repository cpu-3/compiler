open Parser

let limit = ref 1000

let rec iter n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  Format.eprintf "iteration %d@." n;
  if n = 0 then e else
  let e' = Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e)))) in
  if e = e' then e else
  iter (n - 1) e'

let lexbuf outchan nml = (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  Typing.extenv := M.empty;
  let tmp = (Simm.f
               (Virtual.f        (* closure.prog -> asm.prog *)
                  (Typecheck.f
                     (Closure.f     (* knormal.t -> closure.prog *)
                        (let a = iter !limit
                             (let b = Alpha.f nml in
                              print_string "KNormal after alpha: "; KNormal.print_t b; print_newline (); b) in
                         print_string "KNormal after iter: "; KNormal.print_t a;
                         print_newline (); a))))) in (* knormal.t -> knormal.t *)
  let _ = Asm.print_prog tmp in
  let _ = print_string "\n--------------------------------------\n" in
  let tmp = Sched.f tmp in
  let _ = print_string "\n--------------------------------------\n" in
  let _ = Asm.print_prog tmp in
  let _ = print_string "\n--------------------------------------\n" in
  let prog = RegAlloc.f tmp in
  (*print_string "\nAsm.Prog: ";
  Asm.print_prog prog;*)
  Emit.f outchan prog

let lexbuf' outchan buf = lexbuf outchan (KNormal.f (Typing.f (Parser.exp Lexer.token buf)))

let string s = lexbuf' stdout (Lexing.from_string s) (* 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)

let file f = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ ".s") in
  let stx = Parser.exp Lexer.token (Lexing.from_channel inchan) in
  let nml = KNormal.f (Typing.f stx) in (* syntax.t -> syntax.t -> knormal.t *)
  try
    (*print_string "Syntax: "; (* Syntax.tの中間結果 *)
    Syntax.print_t stx;
    print_newline ();
    print_string "KNormal: "; (* KNormal.tの中間結果 *)
    KNormal.print_t nml;
    print_newline ();*)
    lexbuf outchan nml;
    close_in inchan;
    close_out outchan;
  with e -> (close_in inchan; close_out outchan; raise e)

let () = (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined");
     ("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." Sys.argv.(0));
  List.iter
    (fun f -> ignore (file f))
    !files

