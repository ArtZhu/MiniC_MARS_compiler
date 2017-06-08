(*
 * file: copyprop.sml
 * author:
 * date: 4-12-2015.
 *
 * The copyprop transformation does the following:
 *
 * let x = e1 in let y = x in e2 =copyprop=> let x = e1 in e2[y:=x]
 *)

open Environment

module E = Environment
    (*
let substitute x (*for*) y term =
  let rec translateTerm term =
    match term with
    | (Ast.Id z as i) ->
      (match Symbol.compare y z with
       | 0 -> Ast.Id x
       | _ -> i)
    | Ast.Literal _ as w -> w

    | Ast.If {expr; thn; els} ->
      Ast.If {expr = translateTerm expr;
              thn = translateTerm thn;
              els = translateTerm els}

    (* The following two cases can't happen because Or and And were eliminated in
       the naming phase.
    *)
    | Ast.Or _  -> raise (Failure "Cannot happen.")
    | Ast.And _ -> raise (Failure "Cannot happen.")

    | Ast.App {rator; rands} ->
      Ast.App {rator = rator; rands = List.map translateTerm rands}

    | Ast.Let {decl = Ast.ValBind {bv; defn}; body} ->
      Ast.Let {decl = Ast.ValBind {bv = bv; defn = translateTerm defn};
               body = translateTerm body}

    | Ast.Let {decl = Ast.FunBind {id; formals; typ; body = fbody};
               body = body} ->
      Ast.Let {decl = Ast.FunBind {id = id;
                                   formals = formals;
                                   typ = typ;
                                   body = translateTerm fbody};
               body = translateTerm body}
  in
  translateTerm term
*)

let rmNoop instructionstream =
  let rmNoopProcedure (Quads.Procedure {entry; formals; code}) =
    let code = List.filter
        (fun (Quads.Instruction {label; op}) -> match label, op with
           | None, Quads.Noop -> false
           | _ -> true) code in
    Quads.Procedure {entry; formals; code}
  in
  List.map rmNoopProcedure instructionstream

let rec translate instructionstream =
  let translate_and_concat translated_stream procedure =
    let t = translateProcedure procedure in
      List.append translated_stream [t]
  in
  List.fold_left translate_and_concat [] instructionstream

and
  translateProcedure (Quads.Procedure {entry; formals; code = c}) =
  Quads.Procedure {entry; formals;
                   code = translateInstructionList E.empty [] c}
and
  translateInstructionList env translated_code code =
    match code with
      | [] -> translated_code
      | instruction :: rest ->
        let (ret_env, ret_instr) = translateInstruction env instruction in
        translateInstructionList ret_env (translated_code @ [ret_instr]) rest
and
  translateInstruction env (instruction : Quads.instruction) =
  let Quads.Instruction {label = lbl; op = operation} = instruction in
  let (ret_env, ret_op) = (translateOperation env operation) in
  (ret_env, Quads.Instruction {label = lbl;
                               op = ret_op})
and
  translateOperation env op =
  match op with
  | Quads.Gets {dst; src} -> (
    match dst with
    | Quads.Word _ -> assert false
    | Quads.Id lhs ->
      let ( ret_env ,translated_src ) =
        translateRHS env (Some lhs) src in
      match translated_src with
      | None -> (ret_env, Quads.Noop)
      | Some tsrc -> (ret_env, Quads.Gets{dst; src = tsrc})
    )
  | Quads.Jmp lbl -> (env, op)
  | Quads.JmpZero {cond = c; dest = d} ->
    let tc = (
      match c with
      | Quads.Operand operand ->
        Quads.Operand (translateOperand env operand)
      | _ -> Printf.printf " JmpZero (cond : Quads.rhs) should be operand only.\n" ;
        assert false
    ) in
    (env, Quads.JmpZero {cond = tc; dest = d})
  | Quads.Call {label; opnds = operand_list} ->
    (env, Quads.Call {label;
                      opnds = List.map (translateOperand env) operand_list})
  | Quads.Ret operand ->
    (env, Quads.Ret (translateOperand env operand))
  | Quads.Print rhs -> (
    match (translateRHS env None rhs) with
    | (_, None) -> assert false
    | (_, Some trhs) ->
      (env, Quads.Print trhs)
    )
  | Quads.Noop -> (env, op)

and
  translateRHS env (maybeLHS : Symbol.t option) (rhs : Quads.rhs) =
    let (ret_env, translated_src) = (
      match rhs with
      | Quads.Operand ((Quads.Id rhs_sym) as r) -> (
        match maybeLHS with
        | None -> (env, Some (Quads.Operand (translateOperand env r)))
        | Some lhs_sym ->
          Printf.printf "replace %s as %s\n" (Symbol.format lhs_sym) (Symbol.format rhs_sym);
          (union lhs_sym rhs_sym env, None)
        )
      | Quads.Operand (Quads.Word w) -> (env, Some rhs)
      | Quads.BinPrimOp {op = primop; opnds = Quads.{src1 = s1; src2 = s2}} ->
        let translated_operands = Quads.
                                {src1 = (translateOperand env s1);
                                 src2 = (translateOperand env s2)}
        in
        (env, Some (Quads.BinPrimOp {op = primop;
                                     opnds = translated_operands}))
      | Quads.UnPrimOp {op = primop; opnd = operand} ->
        (env, Some (Quads.UnPrimOp {op = primop;
                                    opnd = (translateOperand env operand)}))
      | Quads.FunCall {label; opnds} ->
        let translated_operands = List.map (translateOperand env) opnds in
        (env, Some (Quads.FunCall {label; opnds = translated_operands}))
    ) in
    (ret_env, translated_src)
and
  translateOperand env (operand : Quads.operand) =
  match operand with
  | Quads.Word _ -> operand
  | Quads.Id id ->
    match E.mem id env with
    | false -> operand
    | true -> Quads.Id (E.find id env)
and
  union key value env =
    let v = match E.mem value env with
      | true -> (E.find value env)
      | false -> value
    in
    E.add key v env
