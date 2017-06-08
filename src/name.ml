(*
 * file: name.ml
 * author: Bob Muller
 * date: January 5, 2009
 * revised: March, 2017
 *
 * The Name module implements a source-to-source transformation for
 * naming the values of subterms in miniC. In addition to naming values,
 * the Name module translates "or" and "and" forms into special-cases
 * of the conditional form nested within a let-form.
 *)

open Ast
open Environment

let rec translate (env : Typ.t Environment.t) (Ast.Program procedures)  =  (* YOUR CODE HERE *)
  Ast.Program (List.map (translateProcedure env) procedures)
and
  translateProcedure env (Ast.Procedure {id; formals; typ; body}) = (* FREE CODE! *)
  (* Printf.printf "%s %d" (Symbol.format id) (List.length formals); *)
  Ast.Procedure {id = id;
                 formals = formals;
                 typ = typ;
                 body = translateStatement env body}
and
  translateStatement env statement = (* YOUR CODE HERE *)
    match statement with
    | Ast.Block {decls = ds ; statements = ss } ->
        Ast.Block {decls = ds ;
                   statements = List.map (translateStatement env) ss}
    | Ast.Assign {id = i; expr = e} ->
      Ast.Assign {id = i;
                 expr = translateTerm env e}
    | Ast.While {expr = e; statement = s} ->
      Ast.While {expr = translateTerm env e;
                statement = translateStatement env s}
    | Ast.IfS {expr = e; thn = y; els = n} ->
      Ast.IfS {expr = translateTerm env e;
               thn = translateStatement env y;
               els = translateStatement env n}
    | Ast.Call {rator = op; rands = vs} ->
      Ast.Call {rator = op;
                rands = List.map (translateTerm env) vs}
    | Ast.Print term ->
      Ast.Print (translateTerm env term)
    | Ast.Return term ->
      Ast.Return (translateTerm env term)
and
  translateTerm env term =
  match term with
  | Ast.Id _ as i -> i
  | Ast.Literal _ as w -> w
  | Ast.If {expr = e; thn = y; els = n} ->  (* YOUR CODE HERE *)
    Ast.If {expr = translateTerm env e;
            thn = translateTerm env y;
            els = translateTerm env n}
  | Ast.Or {left; right} ->         (* FREE CODE Removes OR *)
    let x = Symbol.fresh() in
    let xterm = Ast.Id x in
    let bv = {Ast.id = x; typ = Typ.Bool}
    in
    Ast.Let {decl = Ast.ValBind {bv = bv;
                                 defn = translateTerm env left};
             body = Ast.If {expr = xterm;
                            thn = xterm;
                            els = translateTerm env right}}

  | Ast.And {left; right} ->      (* FREE CODE Removes AND *)
    let x = Symbol.fresh() in
    let xterm = Ast.Id x in
    let bv = {Ast.id = x; typ = Typ.Bool}
    in
    Ast.Let {decl = Ast.ValBind {bv = bv;
                                 defn = translateTerm env left};
             body = Ast.If {expr = xterm;
                            thn = translateTerm env right;
                            els = xterm}}

  | Ast.App {rator = op; rands = values} -> (* YOUR CODE HERE *)
    (* build list of fresh variables for existing operands *)
    let decl_var value = Symbol.fresh() in
    let vars = List.map decl_var values in

    (* funtion that wraps ast with
              Let var = value in ast *)
    let createTreeRight var value ast =
      let var_typ = Typ.Int in (*********** FIX **************)
      Ast.Let {decl = Ast.ValBind {bv = {id = var; typ = var_typ};
                                   defn = translateTerm env value};
               body = ast}
    in

    (* expr_var is the extra Symbol for the result of this Ast.App tree *)
    let expr_var = Symbol.fresh() in
    (* for mapping Symbol.t list "vars" to Ast.term list *)
    let to_term var = Ast.Id var in
    List.fold_right2 createTreeRight
      (vars)
      (values)
      (Ast.Let {decl = Ast.ValBind{
                      bv = {id = expr_var; typ = Typ.Int};
                      defn = Ast.App{
                              rator = op;
                              rands = List.map to_term vars}
                      };
                body = (to_term expr_var)})

  | Ast.Let {decl = Ast.ValBind {bv; defn}; body = b} -> (* YOUR CODE HERE *)
    Ast.Let {decl = Ast.ValBind {bv; defn};
              body = translateTerm env b}

  | Ast.Let {decl = Ast.FunBind
                 {id = i;
                  formals = f;
                  typ = t;
                  body = defBody};
             body = letBody} ->  (* YOUR CODE HERE *)
    Ast.Let {decl = Ast.FunBind {id = i;
                                 formals = f;
                                 typ = t;
                                 body = translateTerm env defBody};
             body = translateTerm env letBody}
