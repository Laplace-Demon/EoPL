%{
    open LANG
%}

%token <int> INT
%token MINUS
%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA
%token ISZERO
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token LET
%token DEF
%token IN
%token LETREC
%token TYPE_INTRO
%token PROC
%token NEWREF
%token DEREF
%token SETREF
%token TYPE_MISS
%token TYPE_VOID
%token TYPE_INT
%token TYPE_BOOL
%token ARROW
%token TYPE_REF
%token <string> IDENTIFIER

%left ARROW

%start <LANG.program> PROGRAM
%%

PROGRAM:
  | EXPRESSION                                                                                     { AProgram $1 }

EXPRESSION:
  | INT                                                                                            { ConstExp $1 }
  | IDENTIFIER                                                                                     { VarExp $1 }
  | MINUS LEFT_PAREN EXPRESSION COMMA EXPRESSION RIGHT_PAREN                                       { DiffExp ($3, $5) }
  | ISZERO LEFT_PAREN EXPRESSION RIGHT_PAREN                                                       { IsZeroExp $3 }
  | IF EXPRESSION THEN EXPRESSION ELSE EXPRESSION                                                  { IfExp ($2, $4, $6) }
  | LET list(ID_EXP_PAIR) IN EXPRESSION                                                            { LetExp ($2, $4) }
  | LETREC OTYPE IDENTIFIER LEFT_PAREN list(ID_TYPE_PAIR) RIGHT_PAREN DEF EXPRESSION IN EXPRESSION { LetRecExp ($2, $3, $5, $8, $10) }
  | PROC LEFT_PAREN list(ID_TYPE_PAIR) RIGHT_PAREN EXPRESSION                                      { ProcExp ($3, $5) }
  | LEFT_PAREN EXPRESSION list(EXPRESSION) RIGHT_PAREN                                             { CallExp ($2, $3) }
  | NEWREF LEFT_PAREN EXPRESSION RIGHT_PAREN                                                       { NewrefExp $3 }
  | DEREF LEFT_PAREN EXPRESSION RIGHT_PAREN                                                        { DerefExp $3 }
  | SETREF LEFT_PAREN EXPRESSION COMMA EXPRESSION RIGHT_PAREN                                      { SetrefExp ($3, $5) }

ID_TYPE_PAIR:
  | IDENTIFIER TYPE_INTRO EXPRESSION                                                               { ($1, $3) }

ID_EXP_PAIR:
  | IDENTIFIER DEF OTYPE                                                                           { ($1, $3) }

OTYPE:
  | TYPE                                                                                           { Some $1 }
  | TYPE_MISS                                                                                      { None }

TYPE:
  | LEFT_PAREN TYPE RIGHT_PAREN                                                                    { $2 }
  | TYPE_VOID                                                                                      { VoidType }
  | TYPE_INT                                                                                       { IntType }
  | TYPE_BOOL                                                                                      { BoolType }
  | separated_nonempty_list(ARROW, TYPE)                                                           { let rev_types = List.rev $1 in ProcType (List.rev (tl rev_types), hd rev_types) }
  | TYPE_REF TYPE                                                                                  { RefType $2 }