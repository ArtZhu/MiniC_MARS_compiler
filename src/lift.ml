(*
 * file: Lift.sml
 * author: Bob Muller
 * date: 1-1-2009.
 *
 * The Lift module implements a source-to-source transformation on
 * the nested let-expressions that may (or may not) have been introduced
 * in the naming phase. The transformation rule lifts inner let
 * expressions out. The transformation rule is:
 *
 * let x1 = (let x2 = e2 in e3) in e4
 *
 * is replaced by:
 *
 * let x2 = e2 in (let x1 = e3 in e4).
 *
 * Note that e2 may be a let-expression so the process iterates until
 * all let-expressions are lifted to top-level.
 *)

open Ast

let rec translate (Ast.Program procedures) =
  Ast.Program (List.map translateProcedure procedures)

and translateProcedure (Ast.Procedure {id; formals; typ; body}) = Ast.Procedure {id; formals; typ; body = translateStatement body}

and
  translateStatement statement =
  match statement with
  | Block {decls; statements} -> Block {decls; statements = List.map translateStatement statements}
  | Assign {id; expr} -> Assign {id; expr = translateTerm expr}
  | While {expr; statement} -> While {expr = translateTerm expr; statement = translateStatement statement}
  | IfS {expr; thn; els} -> IfS {expr = translateTerm expr; thn = translateStatement thn; els = translateStatement els}
  | Call {rator; rands} -> Call {rator; rands = List.map translateTerm rands}
  | Print term -> Print (translateTerm term)
  | Return term -> Return (translateTerm term)

and translateTerm term =
  match term with
  | Id _ -> term
  | Literal _ -> term
  | App {rator; rands} -> App {rator; rands = List.map translateTerm rands}
  | If {expr; thn; els} -> If {expr = translateTerm expr; thn = translateTerm thn; els = translateTerm els}
  | And {left; right} -> And {left = translateTerm left; right = translateTerm right}
  | Or {left; right} -> Or {left = translateTerm left; right = translateTerm right}
  | Let {decl; body} -> (match decl with
      | ValBind {bv; defn = Let {decl; body = innerBody}} ->
        translateTerm (Let {decl; body = Let {decl = ValBind {bv; defn = innerBody}; body}})
      | ValBind _ ->
        Let {decl; body = translateTerm body}
      | FunBind {id; formals; typ; body = innerBody} ->
        Let {decl = FunBind {id; formals; typ; body = translateTerm innerBody}; body = translateTerm body})
