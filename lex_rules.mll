{
    open Lexing
}

let white = [' ' '\t']+ 
let newline = '\r' | '\n' | "\r\n"
let int = '-'? ['0'-'9'] ['0'-'9']*
let identifier = ['a'-'z'] ['a'-'z' 'A'-'Z' '-']*


rule read =
  parse
  | white      { read lexbuf }
  | newline    { new_line lexbuf; read lexbuf }
  | int        { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | '-'        { MINUS }
  | '('        { LEFT_PAREN }
  | ')'        { RIGHT_PAREN }
  | ','        { COMMA }
  | "zero?"    { ISZERO }
  | "true"     { TRUE }
  | "false"    { FALSE }
  | "if"       { IF }
  | "then"     { THEN }
  | "else"     { ELSE }
  | "let"      { LET }
  | '='        { DEF }
  | "in"       { IN }
  | "letrec"   { LETREC }
  | ':'        { TYPE_INTRO }
  | "proc"     { PROC }
  | "newref"   { NEWREF }
  | "deref"    { DEREF }
  | "setref"   { SETREF }
  | '?'        { TYPE_MISS }
  | "void"     { TYPE_VOID }
  | "int"      { TYPE_INT }
  | "bool"     { TYPE_BOOL }
  | "->"       { ARROW }
  | "refto"    { TYPE_REF }
  | identifier { IDENTIFIER (Lexing.lexeme lexbuf) }