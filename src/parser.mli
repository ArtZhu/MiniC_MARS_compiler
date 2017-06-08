type token =
  | NUM of (int)
  | ID of (string)
  | TYPE of (string)
  | SEMI
  | COMMA
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | UNIT
  | TRUE
  | FALSE
  | IF
  | THEN
  | ELSE
  | AND
  | OR
  | NOT
  | PRINT
  | WHILE
  | RETURN
  | PLUS
  | MINUS
  | MULTIPLY
  | DIVIDE
  | MOD
  | CARET
  | LT
  | LE
  | EQ
  | NE
  | NEALT
  | GE
  | GT
  | GETS
  | EOF

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.program
