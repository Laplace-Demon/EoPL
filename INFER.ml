(*
inference rules

--------------------
type-of (const-exp num) tenv = int

--------------------
type-of (var-exp var) tenv = tenv(var)

type-of exp1 tenv = int
--------------------
type-of (zero?-exp exp1) tenv = bool

type-of exp1 tenv = int
type-of exp2 tenv = int
--------------------
type-of (diff-exp exp1 exp2) tenv = int

type-of exp1 tenv = t
--------------------
type-of (let-exp name exp1 body) tenv = type-of body [name=t]tenv

type-of exp1 tenv = bool
type-of exp2 tenv = t
type-of exp3 tenv = t
--------------------
type-of (if-exp exp1 exp2 exp3) tenv = t

type-of body [para=t_var] = t_res
--------------------
type-of (proc-exp para body) tenv = (t_var -> t_res)

type-of rator tenv = t1 -> t2
type-of rand tenv = t1
--------------------
type-of (call-exp rator rand) tenv = t2

type-of fun-body [para=t_var][name=(t_var->t_res)]tenv = t_res
--------------------
type-of (letrec-exp name para fun-body body) tenv = type-of body [name=(t_var->t_res)]tenv

type-of exp1 tenv = ty1
--------------------
type-of (newref exp1) tenv = refto ty1

type-of exp1 tenv = refto ty1
--------------------
type-of (deref exp1) tenv = ty1

type-of exp1 tenv = refto ty1
type-of exp2 tenv = ty1
--------------------
type-of (setref exp1 exp2) tenv = void

*)

(* type inference algorithm described in « Essentials of Programming Languages », Chapter 7 *)

let fresh_tvar =
  let sn = ref 0 in               (* good trick to realize "size effect" (actually not really) *)
  fun () ->
    let current_sn = !sn in
    sn := !sn + 1;
    TvarType current_sn

let rec otype2type oty =
  match oty with
    None -> fresh_tvar ()
  | Some ty -> ty

(* type environment *)
type type_environment =
  | EmptyTEnv
  | ExtendTEnv of string list * typ list * type_environment

let rec apply_tenv search_name tenv =
  match tenv with
    EmptyTEnv -> failwith (Printf.sprintf "Variable \"%s\" is not in the type environment." search_name)
  | ExtendTEnv (names, tys, saved_tenv) ->
      let rec loop names tys =
        match names, tys with
         [], _ -> apply_tenv search_name saved_tenv
        | _, [] -> failwith "Names and types lists are not aligned"
        | name :: names', ty :: tys' -> if name = search_name then ty else loop names' tys'
      in loop names tys

(* subst, for solving type equations *)

type substitution = (typ * typ) list

let empty_subst () = []

let extend_subst subst tvar tyexp =
  (tvar, tyexp) :: subst

let rec apply_one_subst tyexp tvar subst =
  match tyexp with
    VoidType | IntType | BoolType -> tyexp
  | ProcType (arg_types, res_type) ->
      ProcType (List.map (fun x -> apply_one_subst x tvar subst) arg_types, apply_one_subst res_type tvar subst)
  | RefType tyor ->
      RefType (apply_one_subst tyor tvar subst)
  | TvarType sn ->
      if tyexp = tvar then subst
      else tyexp

let rec apply_subst2type tyexp (subst : substitution) =
  match tyexp with
    VoidType | IntType | BoolType -> tyexp
  | ProcType (arg_types, res_type) ->
      ProcType (List.map (fun x -> apply_subst2type x subst) arg_types, apply_subst2type res_type subst)
  | RefType tyor ->
      RefType (apply_subst2type tyor subst)
  | TvarType sn ->
      let tmp = List.assoc_opt tyexp subst in
      if tmp <> None then apply_subst2type (Option.get tmp) subst
      else tyexp

(* free variable check *)
let rec no_occurrence tvar tyexp =
  match tyexp with
    VoidType | IntType | BoolType -> true
  | ProcType (arg_types, res_type) ->
      List.for_all (fun x -> no_occurrence tvar x) arg_types && no_occurrence tvar res_type
  | RefType tyor -> no_occurrence tvar tyor
  | TvarType sn -> tvar <> tyexp



"proc (f : ?) proc (x : ?) -((f 3), (f x))"

"letrec
  ? even(odd : ? x : ?) = if zero?(x) then 1 else (odd -(x,1))
  ? odd(x : ?) = if zero?(x) then 0 else ((even odd) -(x,1))
in (odd 13)"

"let x = newref 1
in let y = newref 2
in setref y deref x"