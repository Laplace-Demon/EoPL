(* expressed values and denotated values *)
type expval =
    NumVal of int
  | BoolVal of bool
  | ProcVal of procedure
  | RefVal of int

and environment =
    EmptyEnv
  | ExtendEnv of string list * expval list * environment
  | ExtendEnvRec of string * string list * expression * environment

and procedure = string list * expression * environment

let expval2num ev =
  match ev with
    NumVal num -> num
  | _ -> failwith "Not a number."

let expval2bool ev =
  match ev with
    BoolVal bool -> bool
  | _ -> failwith "Not a boolean."

let expval2proc ev =
  match ev with
    ProcVal proc -> proc
  | _ -> failwith "Not a procedure."

let expval2ref ev =
  match ev with
    RefVal num -> num
  | _ -> failwith "Not a reference."

(* environment *)

let rec apply_env search_name env =
  match env with
    EmptyEnv -> failwith ("Variable \"" ^ search_name ^ "\" is not in the environment.")
  | ExtendEnv (names, vals, saved_env) ->
      let rec search_ribcage name_list val_list =
        match name_list, val_list with
          [], _ -> apply_env search_name saved_env
        | hd_name :: tl_name, hd_val :: tl_val ->
            if hd_name = search_name then hd_val
            else search_ribcage tl_name tl_val
        | _ -> failwith "Mismatch of names and values in environemnt."
      in search_ribcage names vals
  | ExtendEnvRec (name, paras, fun_body, saved_env) ->
      if name = search_name then ProcVal (paras, fun_body, env)
      else apply_env search_name saved_env

(* procedure *)

let apply_proc ((paras, body, saved_env) : procedure) (args : expval list) = value_of body (ExtendEnv (paras, args, saved_env))

(* global mutable variable to imitate the memory *)
let the_store = ref []

let empty_store () : expval list = []

let initialize_store () = the_store := empty_store ()

let get_store () = !the_store

let newref value =
  let next_ref = List.length !the_store in
  the_store := !the_store @ [value];
  next_ref

let deref ref =
  List.nth !the_store ref

let setref ref value =
  let rec loop lst1 lst2 m =
    match lst1 with
      [] -> the_store := List.rev lst2
    | hd :: tl ->
        if ref = m then loop tl (value :: lst2) (m + 1)
        else loop tl (hd :: lst2) (m + 1)
  in loop !the_store [] 0