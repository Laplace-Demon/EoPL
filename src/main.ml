open Lang
open Analyser
open Inferencer
open Interpreter

(* toplevel *) 
let infer (str: string): string =
  match parse_program str with
  | AProgram exp ->
      let ans = type_of exp EmptyTEnv (empty_subst ()) in
      let tyexp = answer2type ans in
      let subst = answer2subst ans in
      type2string (apply_subst2type tyexp subst)


let run (str: string): string =
  match parse_program str with
  | AProgram exp ->
      expval2string (value_of exp EmptyEnv)