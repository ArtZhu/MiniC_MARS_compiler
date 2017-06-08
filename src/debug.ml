(* file: debug.ml
   author: Bob Muller
   date: 3-2-2009

   Various debugging stuff.
*)

(*
 * When !debug, debugging information is printed to file.dbg.
 *)
let debug = ref true;;

let dbgout = ref stdout;;

let debugLexer = ref false;;

let debugOut(out, printer, message, term) =
  (
    output_string out ("\n" ^ message ^ "\n\n");
    printer out term
  );;

let debugInfo(ouch, str, term) =
  (if !debug then
     debugOut(ouch, Ast.ppStream, str, term)
   else ());;

let debugSetup(fname) =
  if !debug then
    let dbgOut = Util.makeFile(fname,"dbg") in
    let _ = dbgout := dbgOut in
    let dbgName = Util.makeFileName(fname, "dbg") in
    let _ = print_string ("\nCompiling " ^ fname ^ 
			    " in debug mode. See file " ^ dbgName ^ ".\n") in
    let dt = Util.dateAndTime() in
    let prefix = Util.compilerName ^ ": " ^ dt ^ ". " in
    let _ = output_string dbgOut (prefix ^ "Compiling " ^ fname ^ " in debug mode.\n")
    in
      dbgOut
  else
    stdout

(* The following is for debugging the lexer. *)

let format = function
    Parser.NUM n -> string_of_int n
  | Parser.ID s -> s
  | Parser.TYPE t -> t
  | Parser.SEMI     -> ";"
  | Parser.COMMA     -> ","
  | Parser.LPAREN     -> "("
  | Parser.RPAREN     -> ")"
  | Parser.LBRACE     -> "{"
  | Parser.RBRACE     -> "}"
  | Parser.TRUE     -> "True"
  | Parser.FALSE     -> "False"
  | Parser.IF     -> "if"
  | Parser.THEN     -> "then"
  | Parser.ELSE     -> "else"
  | Parser.AND     -> "and"
  | Parser.OR     -> "or"
  | Parser.NOT     -> "not"
  | Parser.PRINT     -> "print"
  | Parser.WHILE     -> "while"
  | Parser.RETURN     -> "return"
  | Parser.PLUS     -> "+"
  | Parser.MINUS     -> "-"
  | Parser.MULTIPLY     -> "*"
  | Parser.DIVIDE     -> "/"
  | Parser.UNIT     -> "()"
  | Parser.MOD     -> "%"
  | Parser.CARET     -> "**"
  | Parser.LT     -> "<"
  | Parser.LE     -> "<="
  | Parser.EQ     -> "=="
  | Parser.NE     -> "!="
  | Parser.NEALT     -> "<>"
  | Parser.GE     -> ">="
  | Parser.GT     -> ">"
  | Parser.GETS     -> "="
  | Parser.EOF     -> "EOF";;

let rec dumpTokens lexer lexbuf =
  match lexer lexbuf with
      Parser.EOF -> print_string "EOF\n"
    | other -> let _ = print_string ((format other) ^ "\n") in
	dumpTokens lexer lexbuf;;

let dumpEnv tenv = 
  let printer id typ = output_string !dbgout ((Symbol.format id) ^ " : " ^ (Typ.format typ) ^ "\n") in
  let _ = output_string !dbgout "\nType Environment is:\n" in
    Environment.Environment.iter printer tenv;;

let dumpCGEnv env =
  let printer id offset = output_string !dbgout ((Symbol.format id) ^ " : " ^ (string_of_int offset) ^ "\n") in
  let _ = output_string !dbgout "\nCG Environment is:\n" in
    Environment.Environment.iter printer env


