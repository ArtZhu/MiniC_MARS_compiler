(* file: ast.mli
   author: Bob Muller

   CS3366 Principles of Programming Languages
*)
open Environment
module Sym = Symbol

type binding = {id : Sym.t; typ : Typ.t}

type program = Program of procedure list

and procedure = Procedure of {id : Sym.t;
                              formals : binding list;
                              typ : Typ.t;
                              body : statement}

and statement = Block of {decls : binding list;
                          statements : statement list}
              | Assign of {id : Sym.t; expr : term}
              | While of {expr : term; statement : statement}
              | IfS of {expr : term; thn : statement; els : statement}
              | Call of {rator : Sym.t; rands : term list}
              | Print of term
              | Return of term

and term = Id of Sym.t
         | Literal of {typ : Typ.t; bits : int}
         | App of {rator : Sym.t; rands : term list}    (* term is an identifier *)
         | If of {expr : term; thn : term; els : term}
         | And of {left : term; right : term}
         | Or of {left : term; right : term}
         | Let of {decl : declaration; body : term}
and
  declaration = ValBind of {bv : binding; defn : term}
              | FunBind of {id : Sym.t;
                            formals : binding list;
                            typ : Typ.t;
                            body : term}
and
  value = LiteralValue of {typ : Typ.t; bits : int}
        | BinaryOp of (value * value -> value)
        | UnaryOp of (value -> value)
        | Closure of {code : declaration; env : environment}
and
  environment = Env of value Environment.t

(*
type program = Program of procedure list

and procedure = Procedure of Typ.t * Symbol.t * ((Typ.t * Symbol.t) list) * statement

and statement = Block of (Typ.t * Symbol.t) list * statement list
		| Assign of Symbol.t * term
		| While of term * statement
		| IfS of term * statement * statement
		| Call of Symbol.t * term list
		| Print of term
		| Return of term

and term = Id of Symbol.t
           | Word of Typ.t * int
           | App of term * term list    (* term is an identifier *)
           | If of term * term * term
           | And of term * term
           | Or of term * term
           | Let of declaration * term
and
  declaration = ValBind of Symbol.t * Typ.t * term
                | FunBind of Symbol.t * Typ.t * (Symbol.t * Typ.t) list * term
and
  value = WordValue of Typ.t * int
          | BinaryOp of (value * value -> value)
          | UnaryOp of (value -> value)
          | Closure of declaration * environment
and
  environment = Env of value Environment.t;;
  *)
val toStringList : 'a list -> ('a -> string) -> string
val toString : term -> string
val toStringValue : value -> string

val pp : program -> unit
val ppv : value -> unit
val ppStream : out_channel -> program -> unit
val ppFile : string -> program -> unit
val setIndentLevel : int -> unit
