type t =
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
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list * Type.t
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | GetE of Id.t * Id.t * Type.t
  | PutE of Id.t * Id.t * Id.t * Type.t
  | ExtArray of Id.t * Type.t
  | ExtTuple of Id.t * (Type.t list)
  | ExtFunApp of Id.t * Id.t list
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

val fv : t -> S.t
val f : Syntax.t -> t

val print_t : t -> unit
