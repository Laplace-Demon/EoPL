let parse_program (s: string) =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.pROGRAM Lexer.read lexbuf in
  ast