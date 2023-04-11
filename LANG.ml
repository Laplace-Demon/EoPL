(*
   
PROGRAM ::= EXPRESSION

EXPRESSION ::= number
             | identifier
             | "-" "(" EXPRESSION "," EXPRESSION ")"
             | "zero?" "(" EXPRESSION ")"
             | "if" EXPRESSION "then" EXPRESSION "else" EXPRESSION
             | "let" {identifier "=" EXPRESSION}* "in" EXPRESSION
             | "letrec" type identifier "(" {identifier ":" type}* ")" "=" EXPRESSION "in" EXPRESSION
             | "proc" "(" {identifier ":" type}* ")" EXPRESSION
             | "(" EXPRESSION {EXPRESSION}* ")"
             | "newref" "(" EXPRESSION ")"
             | "deref" "(" EXPRESSION ")"
             | "setref" "(" EXPRESSION "," EXPRESSION ")"

  multiple let binding, list, pair

  binding: environment
  procedure: OCaml procedure representation + environment

*)

(* type *)

type typ =
    VoidType
  | IntType
  | BoolType
  | ProcType of typ list * typ
  | RefType of typ
  | TvarType of int

let rec type2string ty =
  match ty with
    VoidType -> "void"
  | IntType -> "int"
  | BoolType -> "bool"
  | ProcType (arg_tys, res_ty) ->
      let args_str =
        match arg_tys with
          [] -> "()"
        | [arg] -> type2string arg
        | _ -> String.concat " -> " (List.map type2string arg_tys)
      in
      "(" ^ args_str ^ " -> " ^ type2string res_ty ^ ")"
  | RefType ty -> "refto " ^ type2string ty
  | TvarType sn -> "var" ^ string_of_int sn

type expression =
    ConstExp of int
  | VarExp of string
  | DiffExp of expression * expression
  | IsZeroExp of expression
  | IfExp of expression * expression * expression
  | LetExp of (string * expression) list * expression
  | ProcExp of (string * typ option) list * expression
  | CallExp of expression * expression list
  | LetRecExp of typ option * string * (string * typ option) list * expression * expression
  | NewrefExp of expression
  | DerefExp of expression
  | SetrefExp of expression * expression

type program = AProgram of expression
