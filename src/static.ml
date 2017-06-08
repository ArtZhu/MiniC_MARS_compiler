(* file: static.ml
 *
 * Robert Muller
 * MC3366 Programming Languages
 *
 * This file contains a static semantics for the programming language
 * miniC aka Mars.
 *)

open Environment
open Ast

module E = Environment

exception TypeError of string

let fmt = Printf.sprintf

let makeType t =
  match t with
  | [only] -> only
  | ts -> Typ.Product ts

let processArgTypes typs =
  if List.exists (function None -> true | _ -> false) typs then
    None
  else
    (match List.map (function (Some t) -> t | None -> Typ.Int) typs with
      | [t] -> Some t                       (* Singleton. Don't make a tuple. *)
      | ts  -> Some (Typ.Product ts))

let rec gatherProcedureTypes tenv procedures =
  match procedures with
  | [] -> tenv
  | Ast.Procedure {id; formals; typ} :: procedures ->
    let argTypes = List.map (fun bv -> bv.typ) formals in
    let arrow = Typ.Arrow {from = Typ.Product argTypes; too = typ} in
    let tenv' = E.add id arrow tenv
    in
    gatherProcedureTypes tenv' procedures

let rec extendEnv tenv bindings =
  match bindings with
  | [] -> tenv
  | binding :: bindings ->
    extendEnv (E.add binding.id binding.typ tenv) bindings

(* The main event.
 *)
let rec typeCheck tenv (Ast.Program procedures) =
  let tenv' = gatherProcedureTypes tenv procedures in
  let _ = if !Debug.debug then Debug.dumpEnv tenv' else ()
  in
  List.iter (fun procedure -> typeProcedure tenv' procedure) procedures

and
  typeProcedure tenv (Ast.Procedure {id; formals; typ; body}) =
  let tenv' = extendEnv tenv formals
  in
  typeStatement tenv' typ body

and
  typeStatement tenv expected statement =
  match statement with
  | Ast.Block {decls; statements} ->
    let tenv' = extendEnv tenv decls
    in
    List.iter (fun stmt -> typeStatement tenv' expected stmt) statements

  | Ast.Assign {id; expr} ->
    (try
       let idtype = E.find id tenv
       in
       match typeOf tenv expr with
       | Some termtype ->
         (if Typ.equal idtype termtype then
            ()
          else
            raise(TypeError "typeStatement: type mismatch in assignment."))
       | None -> raise(TypeError "typeStatement: bad assignment.")
     with
       Not_found -> raise(TypeError "typeStatement: bad id in assignment."))

  | Ast.While {expr; statement} ->
    (match typeOf tenv expr with
     | Some Typ.Bool -> typeStatement tenv expected statement
     | wrong ->
       raise(TypeError "typeStatement: bad expr in while statement."))

  | Ast.IfS {expr; thn; els} ->
    (match typeOf tenv expr with
     | Some Typ.Bool ->
       let _ = typeStatement tenv expected thn
       in
       typeStatement tenv expected els
     | other ->
       raise(TypeError "typeStatement: test in if statement not of type bool."))

  | Ast.Call {rator; rands} ->
    let randsTypes = List.map (fun t -> typeOf tenv t) rands
    in
    (try
      (match E.find rator tenv with
       | Typ.Arrow {from = Typ.Product formalTypes; too} ->
         let filter formalType randMaybe =
           match randMaybe with
           | None ->
             raise(TypeError "typeStatement: arg to function ill-typed.")
           | Some randType ->
             if Typ.equal formalType randType then ()
             else
               raise(TypeError "typeStmnt: arg type disagrees with formal.")
         in
         (try
            List.iter2 filter formalTypes randsTypes
          with Invalid_argument _ ->
            raise(TypeError "typeStatement: wrong number of arguments.\n"))
       | anyOtherType ->
         raise(TypeError "typeStatement: trying to call a nonfunction."))
     with Not_found -> raise(TypeError "typeStatement: undefined function."))

| Ast.Print term ->
  (match typeOf tenv term with
   | Some Typ.Int -> ()
   | anythingElse ->
     raise(TypeError "typeStatement: print only works for ints."))

| Ast.Return term ->
  (match typeOf tenv term with
   | Some t ->
     if Typ.equal expected t then
	       ()
	     else
	       raise(TypeError "typeStatement: type of return expression is wrong.")
   | other ->
     raise(TypeError "typeStatement: return expression has no type."))

and
  (* Typing Expressions/Terms
  *)
  typeOf tenv term =
  match term with

  | Ast.Literal {typ; bits} -> Some typ

  | Ast.Id name ->
      (try (Some (E.find name tenv)) with Not_found -> None)

  | Ast.App {rator; rands} ->
    let termtypes = List.map (fun t -> typeOf tenv t) rands in
    (try
       (match Environment.find rator tenv with
        | Typ.Arrow {from =Typ.Product formaltypes; too} ->
          (let filter formalType randType =
            match randType with
            | None ->
              raise(TypeError "typeOf: arg to function ill-typed.")
            | Some at ->
              (if Typ.equal formalType at then ()
               else
                 raise(TypeError "typeOf: arg type doesn't agree with formal."))
           in
           try
             (
               List.iter2 filter formaltypes termtypes;
               Some too
             )
           with Invalid_argument _ ->
             raise(TypeError "typeOf: wrong number of arguments.\n"))

(* Fix here for UnaryOp *)
        | Typ.Arrow {from = formaltype; too} ->
          (let filter formalType randType =
             match randType with
             | None ->
               raise(TypeError "typeOf: arg to function ill-typed.")
             | Some at ->
               (if Typ.equal formalType at then ()
                else
                  raise(TypeError "typeOf: arg type doesn't agree with formal."))
           in
           try
             (
               List.iter2 filter [formaltype] termtypes;
               Some too
             )
           with Invalid_argument _ ->
             raise(TypeError "typeOf: wrong number of arguments.\n"))

        | anyOtherType ->
          Printf.printf "trying to call non-fn : %s\n" (Symbol.format rator);
          raise(TypeError "typeOf: trying to call a nonfunction."))

	 with Not_found -> raise(TypeError "typeOf: undefined function."))

  | Ast.And {left; right} | Ast.Or {left; right} ->
      (match typeOf tenv left with
	   Some Typ.Bool ->
	     (match typeOf tenv right with
		  (Some Typ.Bool) as typ -> typ
		| _ -> None)
	 | _ -> None)

  | Ast.If {expr; thn; els} ->
    (match typeOf tenv expr with
     | Some Typ.Bool ->
       (match (typeOf tenv thn, typeOf tenv els) with
        | (Some t, Some t') -> if Typ.equal t t' then Some t else None
        | _ -> None)
     | _ -> None)

  | Ast.Let {decl; body} ->
    (match typeOfDeclaration tenv decl with
     | Some tenv' -> typeOf tenv' body
     | None -> None)

and
  typeOfDeclaration tenv decl =
  match decl with
  | Ast.ValBind{bv = {id; typ}; defn} ->
    (match typeOf tenv defn with
     | Some typ' ->
       if Typ.equal typ typ' then
         Some (Environment.add id typ tenv)
       else
         None
     | None -> None)

  | Ast.FunBind {id; formals; typ; body} ->
    Some(Environment.empty);;
