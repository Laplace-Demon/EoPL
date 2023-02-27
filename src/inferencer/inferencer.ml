open Lang

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

let otype2type oty =
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
  | TvarType _ ->
      if tyexp = tvar then subst
      else tyexp

let rec apply_subst2type tyexp (subst : substitution) =
  match tyexp with
    VoidType | IntType | BoolType -> tyexp
  | ProcType (arg_types, res_type) ->
      ProcType (List.map (fun x -> apply_subst2type x subst) arg_types, apply_subst2type res_type subst)
  | RefType tyor ->
      RefType (apply_subst2type tyor subst)
  | TvarType _ ->
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
  | TvarType _ -> tvar <> tyexp

(* Unifier *)
let unifier tyexp1 tyexp2 subst =
  let new_tyexp1 = apply_subst2type tyexp1 subst in
  let new_tyexp2 = apply_subst2type tyexp2 subst in
  let rec loop tyexp1 tyexp2 subst =
    if tyexp1 = tyexp2 then subst
    else match tyexp1, tyexp2 with
    | TvarType _, _ when no_occurrence tyexp1 tyexp2 -> extend_subst subst tyexp1 tyexp2
    | _, TvarType _ when no_occurrence tyexp2 tyexp1 -> extend_subst subst tyexp2 tyexp1
    | ProcType (arg_types1, res_type1), ProcType (arg_types2, res_type2) ->
        let subst = List.fold_left2 (fun subst arg1 arg2 -> loop arg1 arg2 subst) subst arg_types1 arg_types2 in
        loop res_type1 res_type2 subst
    | RefType tyor1, RefType tyor2 -> loop tyor1 tyor2 subst
    | _ -> failwith "Unification failure."
    in loop new_tyexp1 new_tyexp2 subst

type answer = typ * substitution

let answer2type (ans : answer) = fst ans

let answer2subst (ans : answer) = snd ans

(* inferencer *)

let rec type_of exp tenv subst =
  match exp with
    ConstExp _ -> (IntType, subst)
  | VarExp var -> (apply_tenv var tenv, subst)
  | DiffExp (exp1, exp2) ->
      let ans1 = type_of exp1 tenv subst in
      let ty1 = answer2type ans1 in
      let subst = answer2subst ans1 in
      let subst = unifier ty1 IntType subst in
      let ans2 = type_of exp2 tenv subst in
      let ty2 = answer2type ans2 in
      let subst = answer2subst ans2 in
      let subst = unifier ty2 IntType subst in
     (IntType, subst)
  | IsZeroExp exp1 ->
      let ans1 = type_of exp1 tenv subst in
      let ty1 = answer2type ans1 in
      let subst = answer2subst ans1 in
      let subst = unifier ty1 IntType subst in
     (BoolType, subst)
  | IfExp (exp1, exp2, exp3) ->
      let ans1 = type_of exp1 tenv subst in
      let ty1 = answer2type ans1 in
      let subst = answer2subst ans1 in
      let subst = unifier ty1 BoolType subst in
      let ans2 = type_of exp2 tenv subst in
      let ty2 = answer2type ans2 in
      let subst = answer2subst ans2 in
      let ans3 = type_of exp3 tenv subst in
      let ty3 = answer2type ans3 in
      let subst = answer2subst ans3 in
      let subst = unifier ty2 ty3 subst in
     (ty2, subst)
  | LetExp (pairs, body) ->
      let names = List.map fst pairs in
      let exps = List.map snd pairs in
      let rec loop tem_names tem_exps tem_tys subst =
        if tem_names = [] then type_of body (ExtendTEnv (names, (List.rev tem_tys), tenv)) subst
        else let ans = type_of (List.hd tem_exps) tenv subst in
             let ty = answer2type ans in
             let subst = answer2subst ans in loop (List.tl names) (List.tl tem_exps) (ty :: tem_tys) subst
      in loop names exps [] subst
  | ProcExp (pairs, body) ->
      let paras = List.map fst pairs in
      let para_otypes = List.map snd pairs in
      let para_tys = List.map (fun x -> otype2type x) para_otypes in
      let body_ans = type_of body (ExtendTEnv (paras, para_tys, tenv)) subst in
      let body_ty = answer2type body_ans in
      let subst = answer2subst body_ans in
     (ProcType (para_tys, body_ty), subst)
  | CallExp (rator, rands) ->
      let res_ty = fresh_tvar () in
      let rator_ans = type_of rator tenv subst in
      let rator_ty = answer2type rator_ans in
      let subst = answer2subst rator_ans in
      let rec loop tem_rands rand_tys subst =
        if tem_rands = [] then (res_ty, unifier rator_ty (ProcType (List.rev rand_tys, res_ty)) subst)
        else let ans = type_of (List.hd tem_rands) tenv subst in
             let ty = answer2type ans in
             let subst = answer2subst ans in loop (List.tl tem_rands) (ty :: rand_tys) subst
        in loop rands [] subst
  | LetRecExp (res_otype, name, pairs, fun_body, body) ->
      let paras = List.map fst pairs in
      let para_otypes = List.map snd pairs in
      let res_type = otype2type res_otype in
      let para_types = List.map (fun x -> otype2type x) para_otypes in
      let letrec_body_tenv = ExtendTEnv ([name], [ProcType (para_types, res_type)], tenv) in
      
      let fun_body_tenv = ExtendTEnv (paras, para_types, letrec_body_tenv) in
      let ans1 = type_of fun_body fun_body_tenv subst in
      let ty1 = answer2type ans1 in
      let subst = answer2subst ans1 in
      let subst = unifier ty1 res_type subst in
      type_of body letrec_body_tenv subst
  | NewrefExp exp1 ->
      let ans1 = type_of exp1 tenv subst in
      let ty1 = answer2type ans1 in
      let subst = answer2subst ans1 in
     (RefType ty1, subst)
  | DerefExp exp1 ->
      let deref_tvar = fresh_tvar () in
      let ans1 = type_of exp1 tenv subst in
      let ty1 = answer2type ans1 in
      let subst = answer2subst ans1 in
      let subst = unifier (RefType deref_tvar) ty1 subst in
     (deref_tvar, subst)
  | SetrefExp (exp1, exp2) ->
      let ans1 = type_of exp1 tenv subst in
      let ty1 = answer2type ans1 in
      let subst = answer2subst ans1 in
      let ans2 = type_of exp2 tenv subst in
      let ty2 = answer2type ans2 in
      let subst = answer2subst ans2 in
      let subst = unifier ty1 (RefType ty2) subst in
     (VoidType, subst)