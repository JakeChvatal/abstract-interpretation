module Var : sig
  type t
  val compare : t -> t -> int
  val var : string -> t
end = struct
  type t = string
  let compare = String.compare
  let var x = x
end

type var = Var.t

(* expressions *)
type expr =
  | Call of var * atom * atom * expr
  | Return of atom
  | Plus of var * atom * atom * expr
  | Let of var * atom * expr

(* atomic data *)
and atom =
  | Var of var
  | Lambda of lambda
  | Int of int


and lambda = int * var * expr
let lam_compare (i1, _, _) (i2, _, _) = i2 - i1

module Addr : sig
  type t
  val compare : t -> t -> int
  val alloc : var -> t
end = struct
  type t = var
  let compare = Var.compare
  let alloc var = var
end

type addr = Addr.t

module Env = Map.Make(Var)
type env = addr Env.t

module Closure : sig
  type t = env * lambda
  val compare : t -> t -> int
  val toString : t -> string
end = struct
  type t = env * lambda
  let compare = (fun (env1, lam1) (env2, lam2) ->
      match lam_compare lam1 lam2 with
      | 0 -> Env.compare Addr.compare env1 env2
      | x -> x
    )
  let toString (_, (i, _, _)) = "<fun " ^ Int.to_string i ^ ">"
end

type closure = Closure.t

module IntegerValue : sig
  type t
  val fromInt : int -> t
  val join : t -> t -> t
  val toString : t -> string
  val empty : t
  val plus : t -> t -> t
  val compare : t -> t -> int
end = struct
  type t = All | None | One of int
  let empty = None
  let fromInt i = One i
  let toString iv =
    "[iv " ^
    (match iv with
     | All -> "all"
     | None -> "none"
     | One(i) -> Int.to_string i
    )
    ^"]"
  let join iv1 iv2 =
    match (iv1, iv2) with
    | (All, _) -> All
    | (_, All) -> All
    | (One(i1), One(i2)) ->
      if i1 = i2 then iv1 else All
    | (None, _) -> iv2
    | (_, None) -> iv1
  let plus iv1 iv2 =
    match (iv1, iv2) with
    | (All, _) -> All
    | (_, All) -> All
    | (One(i1), One(i2)) -> One(i1 + i2)
    | (None, _) -> None
    | (_, None) -> None
  let compare iv1 iv2 =
    match (iv1, iv2) with
    | (All, All) -> 0
    | (All, _) -> 1
    | (_, All) -> -1
    | (One(i1), One(i2)) -> i2 - i1
    | (None, None) -> 0
    | (None, _) -> -1
    | (_, None) -> 1
end

module Value : sig
  type t
  val fromClosure : closure -> t
  val fromInt : int -> t
  val compare : t -> t -> int
  val foldClosure : (closure -> 'a -> 'a) -> t -> 'a -> 'a
  val join : t -> t -> t
  val empty : t
  val toString : t -> string
  val plus : t -> t -> t
end = struct
  module ClosureSet = Set.Make(Closure)
  type t = ClosureSet.t * IntegerValue.t
  let empty = (ClosureSet.empty, IntegerValue.empty)
  let fromClosure c = (ClosureSet.singleton c, IntegerValue.empty)
  let fromInt i = (ClosureSet.empty, IntegerValue.fromInt i)
  let compare (c1, iv1) (c2, iv2) =
    match IntegerValue.compare iv1 iv2 with
    | 0 -> ClosureSet.compare c1 c2
    | x -> x
  let foldClosure f (c, iv) base = ClosureSet.fold f c base
  let join (c1, iv1) (c2, iv2) = (ClosureSet.union c1 c2, IntegerValue.join iv1 iv2)
  let toString (c, iv) =
    "<closures: " ^
    ClosureSet.fold (fun clo acc -> Closure.toString clo ^ acc) c
      (", integers: " ^ IntegerValue.toString iv ^ ">")
  let plus (c1, iv1) (c2, iv2) =
    (ClosureSet.empty, IntegerValue.plus iv1 iv2)
end

type value = Value.t

module Store : sig
  include Map.S with type key = addr
  val join : value t -> value t -> value t
  val extend : addr -> value -> value t -> value t
end = struct
  include Map.Make(Addr)
  let join = union (fun _ v1 v2 -> Some (Value.join v1 v2))
  let extend addr v store =
    match find_opt addr store with
    | None -> add addr v store
    | Some(v') -> add addr (Value.join v v') store
end

type store = value Store.t

let interpreter (e : expr) : value =

  (* evaluates an atomic expression *)
  let eval (atom : atom) (env : env) (store : store) : value =
    match atom with
    | Var(var) -> Store.find (Env.find var env) store
    | Lambda(lam) -> Value.fromClosure (env,lam)
    | Int(i) -> Value.fromInt(i)
  in

  (* applies a function to its argument  *)
  let rec apply (f : value) (arg : value) (store : store) : (value * store) =
    Value.foldClosure
      (fun (env, (_, var, expr)) (val_acc, store_acc) ->
         let addr = Addr.alloc var in
         let new_val, new_store = interpreter_env expr (Env.add var addr env) (Store.extend addr arg store) in
         (Value.join new_val val_acc, Store.join new_store store_acc))
      f (Value.empty, store)

  (* interprets an expression in an environment *)
  and interpreter_env (e : expr) (env : env) (store : store) : (value * store) =
    match e with
    | Let(var, arg, next) ->
      let arg = eval arg env store in
      let addr = Addr.alloc var in
      interpreter_env next (Env.add var addr env) (Store.extend addr arg store)
    | Call(var, f, arg, next) ->
      let f = eval f env store in
      let arg = eval arg env store in
      let (result, store) = apply f arg store in
      let addr = Addr.alloc var in
      interpreter_env next (Env.add var addr env) (Store.extend addr result store)
    | Return(atom) -> (eval atom env store, store)
    | Plus(var, a1, a2, next) ->
      let a1 = eval a1 env store in
      let a2 = eval a2 env store in
      let result = Value.plus a1 a2 in
      let addr = Addr.alloc var in
      interpreter_env next (Env.add var addr env) (Store.extend addr result store)

  in
  fst @@ interpreter_env e Env.empty Store.empty


(*** Test Cases ***)
let v = Var.var

let prog1 =
  (Call(v "f", Lambda(1, v "x1", Return(Var(v "x1"))), Lambda(2, v "y1", Return(Var(v "y1"))),
        (Call(v "x", Var(v "f"), Lambda(3, v "x2", Return(Var(v "x2"))),
              (Call(v "y", Var(v "f"), Lambda(4, v "x3", Return (Var (v "x3"))),
                    (Return (Var (v "x")))))))))
let prog2 =
  Call(v "f", Lambda(1, v "x1", Return(Var(v "x1"))), Lambda(2, v "y1", Return(Var(v "y1"))),
       Call(v "x", Var(v "f"), Lambda(3, v "x2", Return(Var(v "x2"))),
            Call(v "y", Var(v "f"), Lambda(4, v "x3", Return (Var (v "x3"))),
                 (Return (Var (v "y"))))))

(* TODO
 * produce All
 * produce None
 * produce One
 * nontermination
 * *)

let progOne =
  Let(v "x", Int(3),
      Let(v "y", Int(2),
         Plus(v "z", Var(v "x"), Var(v "y"), Return(Var(v "z")))))
let progNone =
  Plus(v "x", Lambda(1, v "f", Return(Var(v "f"))), Lambda(2, v "f", Return(Var(v "f"))), Return (Var(v "x")))
let progNonTerm =
  Let(v "f", Lambda(1, v "x", Call(v "v", Var(v "f"), Var(v "f"), Return(Var(v "x")))),
      Call(v "z", Var(v "f"), Var(v "f"), Return(Var(v "z"))))



let _ = print_string "running prog1";;
let _ = print_string (Value.toString (interpreter prog1));;
let _ = print_string "\n\n";;
let _ = print_string "running prog2";;
let _ = print_string (Value.toString (interpreter prog2));;
let _ = print_string "\n\n";;
