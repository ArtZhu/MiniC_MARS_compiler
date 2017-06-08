open Environment

val typeCheck : Typ.t Environment.t -> Ast.program -> unit

exception TypeError of string
