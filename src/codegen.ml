(*
 * file: codegen.ml
 * author: Bob Muller
 * date: 3-14-2009
 * revised: April, 2015
 * revised; March, 2017
 *
 * This file contains code for inserting control in the compilation
 * of mini-C. This code translates from the language of quads to
 * MIPS assembly code. The calling protocols is as follows:
 *
 * Register Conventions:
 *  t0 - t9 : caller-save regs
 *  s0 - s7 : callee-save regs
 *  fp : frame pointer
 *  ra : return address
 *  a0 - a3 : argument registers for first 4 arguments
 *  v0 - v1 : return values
 *
 * 1. Stack Frame Layout:

       +----------------------------+
       |      Caller-Save Regs      |                 higher addresses
       +----------------------------+
       |       Value of Arg 1       |
       +--           :            --+
       |             :              |
       +--                        --+
       |       Value of Arg n       |
       +----------------------------+
       |       Return Address       |
       +----------------------------+
       |   Caller's Frame Pointer   | <-- fp
       +----------------------------+
       |      Local Variable 1      |
       +--            :           --+
       |              :             |
       +--                        --+
       |      Local Variable k      |
       +----------------------------+
       |   Callee Save Registers    |                 lower addresses
       +----------------------------+
                                      <-- sp

 *)


(*| Q.Exit ->
  (fIL [
    toIn( None,
          Opn.Li {rd = Opnd.Reg(Opnd.Value 0);
                  imm32 = Opnd.Const32 syscallReturn},
          Some "$v0 gets exit code for syscall");
    toIn( None,
          Opn.Syscall,
          Some "Exit here"
        )])*)

open Environment

(*
 * Some abbreviations for frequently used modules.
 *)
module Q = Quads
module E = Environment
module Opn = Mips.Operation
module Opnd = Mips.Operand
module I = Mips.Instruction
module CS = Mips.Codestream

module B = Bases.Compiler

let makeLabel = Label.fromString

let fIL = CS.fromInstructionList
let toIn = I.toInstruction

(* Conventions
 *
 *   This section binds names to enforce some code generator conventions.
 *
 * Word size is 4 bytes.
 *)
let wordSize = 4

(* Conventions for system calls on MARS. These codes go in $v0.
 *)
let syscallPrintInt = 1
let syscallReturn = 10
let syscallReturnWithVal = 17

(* accumulator register used to accumulate results.
 *)
let accumulator =  Opnd.Value 0
let operand1Reg =  Opnd.Temp 1
let operand2Reg =  Opnd.Temp 2

(* dataBaseAddr is the register that is used to to hold the base
 * address of the data area. All variables accessed via indirect
 * addressing off of this register.
 *)
let dataBaseAddr = Opnd.Temp 1

(* targetLabelReg is the number of the register that is used to
 * hold the destination of a branch.
 *)
let targetLabelReg = Opnd.Temp 2

(* The registers to be used for operands of two-argument operations.
 *)
let firstOpndReg =  Opnd.Temp 3
let secondOpndReg = Opnd.Temp 4

(* The makeJumpStream function generates code for branching to
 * a label after testing a particular register.
 *
 * NB: The code overwrites register the targetLabelReg.
 *)
let makeJumpStream(testReg, destLabel) =
  let branch = toIn(None,
                    Opn.Beqz {rs = testReg; off18 = Opnd.Label destLabel},
                    Some "branch")
  in
    fIL [branch]

let push reg maybeLabel comment =
  let i1 = toIn(maybeLabel,
                Opn.Addi {rd = Opnd.Reg(Opnd.StackPointer);
                          rs = Opnd.Reg(Opnd.StackPointer);
                          const16 = Opnd.Const16 (-4)},
			          Some ("push " ^ comment)) in
  let i2 = toIn(None,
                Opn.Sw {rs = reg;
                        rt = Opnd.Indirect {offset = Some 0;
                                            reg = Opnd.StackPointer}},
                None)
  in
  fIL [i1; i2]

let pop dstreg maybeLabel comment=
  let i1 = toIn(None,
                Opn.Lw {rd = dstreg;
                        rs = Opnd.Indirect {offset = Some 0;
                                            reg = Opnd.StackPointer}},
			   Some ("pop " ^ comment)) in
  let i2 = toIn(None,
                Opn.Addi {rd = Opnd.Reg Opnd.StackPointer;
                          rs = Opnd.Reg Opnd.StackPointer;
                          const16 = Opnd.Const16 4},
                None)
  in
  fIL [i1; i2]

let makePrologue name nLocals =
  let pushFP = push (Opnd.Reg Opnd.FramePointer) (Some name) "fp" in
  let sp2fp = toIn(None, Opn.Move {rd = Opnd.Reg Opnd.FramePointer;
                                   rs = Opnd.Reg Opnd.StackPointer},
                   Some "fp <- sp") in
  let allocate = toIn(None,
                      Opn.Addi {rd = Opnd.Reg Opnd.StackPointer;
                                rs = Opnd.Reg Opnd.StackPointer;
                                const16 = Opnd.Const16 (wordSize * nLocals)},
                      Some "allocate locals")
  in
    CS.concat pushFP (fIL [sp2fp; allocate])

let makeEpilogue() =
  let i0 = toIn(None,
                Opn.Move {rd = Opnd.Reg (Opnd.Arg 0);
                          rs = Opnd.Reg accumulator},
                Some "$a0 gets answer for syscall") in
  let i1 = toIn(None,
                Opn.Li {rd = Opnd.Reg(Opnd.Value 0);
                        imm32 = Opnd.Const32 syscallPrintInt},
                Some "$v0 gets print_int code for syscall") in
  let i2 = toIn(None, Opn.Syscall, Some "Print the result") in
  let i3 = toIn(None,
                Opn.Li {rd = Opnd.Reg(Opnd.Value 0);
                        imm32 = Opnd.Const32 syscallReturn},
			          Some "Load return status") in
  let i4 = toIn(None, Opn.Syscall, None)
  in
  fIL [i0; i1; i2; i3; i4]

(* makeEnv constructs an environment for a given procedure. The
 * environment maps each identifier to its storage offset as suggested
 * by the picture at the top of the file. In particular, all variables
 * are accessed via indirect addressing using the frame pointer (fp) as
 * the base address. Formal parameters will have positive offsets while
 * local variables will have negative offsets.
 *)
let makeEnvOpnd env offset opnd =
  match opnd with
  | Q.Id id -> (match E.mem id env with
	| true  -> (env, offset)
  | false -> (E.add id offset env, offset - 1))
  | Q.Word _ -> (env, offset)

let makeEnvRHS env offset rhs =
  match rhs with
  | Q.Operand opnd -> makeEnvOpnd env offset opnd

  | Q.BinPrimOp {op; opnds = {Q.src1 = opnd1; src2 = opnd2}} ->
     let (env', offset') = makeEnvOpnd env offset opnd1
     in
     makeEnvOpnd env' offset' opnd2

  | Q.UnPrimOp {op; opnd} -> makeEnvOpnd env offset opnd

  | Q.FunCall {label; opnds} ->
    List.fold_right
      (fun opnd -> (fun (env, offset) -> makeEnvOpnd env offset opnd))
      opnds
      (env, offset)

let makeEnvOperation env offset opn =
  match opn with
  | Q.Gets {dst; src} ->
     let (env', offset') = makeEnvOpnd env offset dst
     in
     makeEnvRHS env' offset' src

  | Q.JmpZero {cond; dest} -> makeEnvRHS env offset cond

  | Q.Call {label; opnds} ->
     List.fold_right (fun opnd -> (fun (env, offset) -> makeEnvOpnd env offset opnd)) opnds (env, offset)

  | Q.Ret(opnd) -> makeEnvOpnd env offset opnd

  | other -> (env, offset)

let makeEnvInstruction env offset (Q.Instruction {label; op}) =
  makeEnvOperation env offset op

(* makeEnv makes an environment with an entry for each identifier. Identifiers that
   are formals are given positive offsets (see the picture above), identifiers that
   are local variables are given negative offsets.
*)
let makeEnv formals instructions = (* Environment.empty *) (* YOUR CODE HERE *)
  let rec buildEnv idx inc syms env =
    match syms with
    | [] -> env
    | sym :: rest -> buildEnv (idx+inc) inc rest (E.add sym idx env)
  in

  let localVars =
    let buildLocalVars (varList : Symbol.t list) instruction =
      match instruction with
      | Q.Instruction {label = l; op = Q.Gets {dst = Q.Id i; src = s}} ->
        (match (List.mem i formals) with
        | true -> varList
        | false -> varList @ [i])
      | _ -> varList
    in
    List.fold_left buildLocalVars [] instructions
  in
  let env = E.empty in
  let formals_env = (buildEnv 2 1 (List.rev formals) env) in
  (List.length localVars, buildEnv (-1) (-1) localVars formals_env)


let loadRegister reg env opnd maybeLabel =
  match opnd with
  | Q.Id name ->
    (*let _ = print_string ("1: " ^ (Q.formatOperand opnd) ^ " " ^ (string_of_bool (E.mem name env)) ^ "\n") in *debug*)
    let o = E.find name env in
    let offset = wordSize * o
    in
    toIn(maybeLabel,
         Opn.Lw {rd = Opnd.Reg reg;
                 rs = Opnd.Indirect {offset = Some offset;
                                     reg = Opnd.FramePointer}},
         None)

  | Q.Word {typ; bits} ->
    toIn(maybeLabel,
         Opn.Li {rd = Opnd.Reg reg; imm32 = Opnd.Const32 bits},
         None)

let storeRegister reg env opnd maybeLabel =
  match opnd with
  | Q.Id name ->
    (*let _ = print_string ("2: " ^ (Q.formatOperand opnd) ^ " " ^ (string_of_bool (E.mem name env)) ^ "\n") in *debug*)
    let o = E.find name env in
    let offset = wordSize * o
    in
    toIn(maybeLabel,
         Opn.Sw {rs = Opnd.Reg reg;
                 rt = Opnd.Indirect {offset = Some offset;
                                     reg = Opnd.FramePointer}},
         None)
  | _ -> failwith "storeRegister: bad store operand"

let translateOperand reg env opnd maybeLabel =
  (* toIn(None, Opn.Nop, None) *)             (* YOUR CODE HERE *)
  let operation =
  match opnd with
  | Q.Word {typ = t; bits = b} -> (
      match t with
      | Typ.Int ->
        Opn.Li {rd = Opnd.Reg reg;
                imm32 = Opnd.Const32 b}
      | Typ.Bool ->
        Opn.Li {rd = Opnd.Reg reg;
                imm32 = Opnd.Const32 b}
      | _ -> assert false
    )
  | Q.Id id ->
    (*let _ = print_string ("3: " ^ (Q.formatOperand opnd) ^ " " ^ (string_of_bool (E.mem id env)) ^ "\n") in *debug*)
    let id_offset = wordSize * (E.find id env) in
    Opn.Lw {rd = Opnd.Reg reg;
            rs = Opnd.Indirect {
                offset = Some id_offset;
                reg = Opnd.FramePointer
              }}
  in
 toIn(maybeLabel, operation, None)

let translateRHS env rhs maybeLabel reg =
  (* fIL [toIn(None, Opn.Nop, None)] *)       (* YOUR CODE HERE *)
  match rhs with
  | Q.Operand op ->
    fIL [translateOperand reg env op maybeLabel]
  | Q.BinPrimOp {op = primop; opnds = Q.{src1; src2}} -> (
    let cs_load_s1s2 =
      fIL [(translateOperand operand1Reg env src1 maybeLabel);
       (translateOperand operand2Reg env src2 maybeLabel)]
    in
    let ac = Opnd.Reg reg in
    let t1 = Opnd.Reg operand1Reg in
    let t2 = Opnd.Reg operand2Reg in
    (*let _ = print_string ("4: " ^ (Q.formatRHS rhs) ^ " " ^ (string_of_bool (E.mem primop Bases.Compiler.dynamicBasis)) ^ "\n") in *debug*)
    match E.find primop Bases.Compiler.dynamicBasis with
    | Bases.Compiler.CodeGenerator cg -> CS.concat cs_load_s1s2 (cg [ac; t1; t2])
    | _ -> assert false )
  | Q.UnPrimOp  {op = primop; opnd} -> (
      let cs_load_s1 =
        fIL [translateOperand operand1Reg env opnd maybeLabel] in
      let ac = Opnd.Reg reg in
      let t1 = Opnd.Reg operand1Reg in
      (*let _ = print_string ("5: " ^ (Q.formatRHS rhs) ^ " " ^ (string_of_bool (E.mem primop Bases.Compiler.dynamicBasis)) ^ "\n") in *debug*)
      match E.find primop Bases.Compiler.dynamicBasis with
      | Bases.Compiler.CodeGenerator cg -> CS.concat cs_load_s1 (cg [ac; t1])
      | _ -> assert false )
  | Q.FunCall {label = l; opnds = opnd_list} ->
      let push_args =
        (* Caller frame order ??? *)
        let prep_opnd maybeLabel1 opnd =
          CS.concat
            (fIL [loadRegister operand1Reg env opnd maybeLabel1])
            (push (Opnd.Reg operand1Reg) None "")
        in
        (* where prep_opnds list starts *)
        let push_ra maybeLabel1 = push (Opnd.Reg Opnd.ReturnAddress) maybeLabel1 "" in
        match opnd_list with
        | [] -> push_ra maybeLabel
        | opnd1 :: rest ->
          CS.concat
            (let cs1 = prep_opnd maybeLabel opnd1 in
             List.fold_left CS.concat cs1 (List.map (prep_opnd None) rest))
            (push_ra None)
      in
      let jal = fIL [toIn (None, Opn.Jal (Opnd.Label l), None)]
      in
      let dealloc_args =
        CS.concat
          (pop (Opnd.Reg Opnd.ReturnAddress) None "ra")
          (fIL [toIn (
               (None),
               (Opn.Addi {rd = Opnd.Reg Opnd.StackPointer;
                          rs = Opnd.Reg Opnd.StackPointer;
                          const16 = Opnd.Const16 (wordSize * (List.length opnd_list))
                         }),
               (Some "deallocate args")
             )])
      in
      CS.concat
        (CS.concat push_args jal)
        dealloc_args
      (* push_args; jal; dealloc args *)

let translateOperation env opn maybeLabel procedure_label =
  (* fIL [toIn(None, Opn.Nop, None)]  *)     (* YOUR CODE HERE *)

  match opn with
  | Q.Gets {dst = d; src = s} -> (
    let src_codestream = translateRHS env s maybeLabel accumulator in
    match d with
    | Q.Id id ->
      (*let _ = print_string ("6: " ^ (Q.formatOperation opn) ^ " " ^ (string_of_bool (E.mem id env)) ^ "\n") in debug*)
      let fp_offset = wordSize * (E.find id env) in
      CS.concat
        (src_codestream)
        (fIL [toIn(
            maybeLabel,
            Opn.Sw {rs = Opnd.Reg (Opnd.Value 0);
                    rt = Opnd.Indirect { offset = Some fp_offset;
                                         reg = Opnd.FramePointer}
                   },
            None
           )]
        )
    | _ -> assert false
    ) (* Q.Gets *)
  | Q.Jmp lbl ->
    fIL [toIn(
        maybeLabel,
        Opn.J (Opnd.Label lbl),
        None
      )]
  | Q.JmpZero {cond = c; dest = d} ->
    let trans_cond = translateRHS env c maybeLabel accumulator in
    CS.concat
      (trans_cond)
      (fIL [toIn(
                maybeLabel,
                Opn.Beqz {rs = Opnd.Reg accumulator; off18 = Opnd.Label d},

                (* Opn.Bnez {rs = Opnd.Reg accumulator; off18 = Opnd.Label d},*)
                (* it was beqz here,
                     but I don't think it works for cases like 7 == 5 *)
                  None
            )])
  | Q.Call {label = l ; opnds = opnd_list} ->
    let push_args =
      (* Caller frame order ??? *)
      let prep_opnd maybeLabel1 opnd =
        CS.concat
          (fIL [loadRegister operand1Reg env opnd maybeLabel1])
          (push (Opnd.Reg operand1Reg) None "")
      in
      (* where prep_opnds list starts *)
      let push_ra maybeLabel1 = push (Opnd.Reg Opnd.ReturnAddress) maybeLabel1 "" in
      match opnd_list with
      | [] -> push_ra maybeLabel
      | opnd1 :: rest ->
        CS.concat
          (let cs1 = prep_opnd maybeLabel opnd1 in
           List.fold_left CS.concat cs1 (List.map (prep_opnd None) rest))
          (push_ra None)
    in
    let jal = fIL [toIn (None, Opn.Jal (Opnd.Label l), None)]
    in
    let dealloc_args =
      CS.concat
        (pop (Opnd.Reg Opnd.ReturnAddress) None "ra")
        (fIL [toIn (
             (None),
             (Opn.Addi {rd = Opnd.Reg Opnd.StackPointer;
                        rs = Opnd.Reg Opnd.StackPointer;
                        const16 = Opnd.Const16 (wordSize * (List.length opnd_list))
                       }),
             (Some "deallocate args")
           )])
    in
    CS.concat
      (CS.concat push_args jal)
      dealloc_args
(* push_args; jal; dealloc args *)
  | Q.Print rhs ->
    CS.concat
      (translateRHS env rhs None (Opnd.Arg 0))
      (fIL [
       toIn( None,
                          Opn.Li {rd = Opnd.Reg(Opnd.Value 0);
                                  imm32 = Opnd.Const32 syscallPrintInt},
                          Some "$v0 gets print_int code for syscall");
       toIn( None,
                          Opn.Syscall,
                          Some "print"
      )]) (* IMP *)
  | Q.Ret opnd ->
    let reg =
      if procedure_label = (Label.fromString "main") then (Opnd.Arg 0)
      else (Opnd.Value 0) in
    let set_v0_instr = translateOperand
        reg env opnd maybeLabel in
    fIL [set_v0_instr]
(* I think restoring fp and jr ra should not reside here,
    they both should be the last part of translate Procedure, funccall. *)
  | Q.Noop ->
    fIL [toIn(
          maybeLabel,
          Opn.Nop,
          None
      )]

let translateInstruction env procedure_label
                          (Q.Instruction {label = maybeLabel;
                                          op = opn} : Q.instruction)
                         : CS.t =
  (* YOUR CODE HERE *)
  translateOperation env opn maybeLabel procedure_label

let translateProcedure (Q.Procedure {entry; formals; code}) = (* YOUR CODE HERE *)
  let (num_local_vars, cgenv) = makeEnv formals code in
  let sp_dec = num_local_vars + 1 in
  let dec_sp_instr =toIn(
                (Some entry),
                (Opn.Addi {rd = Opnd.Reg Opnd.StackPointer;
                         rs = Opnd.Reg Opnd.StackPointer;
                           const16 = Opnd.Const16 (-4)}),
                (Some "push fp")
    ) in
  let new_fp_instr =toIn(
                None,
                (Opn.Sw {rs = Opnd.Reg Opnd.FramePointer;
                       rt = Opnd.Indirect {offset = Some 0;
                                      reg = Opnd.StackPointer}}),
                None
    ) in
  let move_instr  =toIn(
                None,
                (Opn.Move {rd = Opnd.Reg Opnd.FramePointer;
                           rs = Opnd.Reg Opnd.StackPointer}),
                Some "fp <- sp"
    ) in
  let alloc_local_vars_instr =toIn(
                None,
                (Opn.Addi {rd = Opnd.Reg Opnd.StackPointer;
                          rs = Opnd.Reg Opnd.StackPointer;
                          const16 = Opnd.Const16 (-wordSize * sp_dec)}),
                Some "allocate locals"
    ) in
  let restore_sp_intr =toIn(
      None,
      (Opn.Move {rd = Opnd.Reg Opnd.StackPointer; rs = Opnd.Reg Opnd.FramePointer}),
      None
    ) in
  let restore_fp_instr = pop (Opnd.Reg Opnd.FramePointer) None "restore fp" in
  let return_instrs =
    if entry = (Label.fromString "main") then
      [toIn(None,
            Opn.Li {rd = Opnd.Reg(Opnd.Value 0);
                    imm32 = Opnd.Const32 syscallReturnWithVal},
            Some "$v0 gets exit code for syscall");
      toIn( None,
            Opn.Syscall,
            Some "Exit here"
      )]
    else
      [toIn(
        None,
        (Opn.Jr (Opnd.Reg Opnd.ReturnAddress)),
        Some "return"
      )] in

  ignore(Debug.dumpCGEnv cgenv);

  (entry,
  CS.concat(
    (CS.concat  (fIL (dec_sp_instr ::
                      new_fp_instr ::
                      move_instr ::
                      alloc_local_vars_instr :: []))
                (List.fold_left CS.concat (CS.empty)
                                          (List.map (translateInstruction cgenv entry) code))))
    (CS.concat   (fIL [restore_sp_intr])
                 (CS.concat restore_fp_instr (fIL return_instrs)))
  )
(*
 * The main function. It leaves the result of evaluating and expression in
 * the accumulator.
*)
let translate procedures =  (* Mips.Codestream.empty *) (* YOUR CODE HERE *)
  let main_first_concat cs1 (tag, cs2) =
    match tag = Label.fromString "main" with
    | true -> CS.concat cs2 cs1
    | false -> CS.concat cs1 cs2
  in
  CS.concat
    (fIL [toIn (None, Mips.Operation.Data, None);
                 toIn(None, Mips.Operation.Text, None)])
    (List.fold_left main_first_concat
                    CS.empty (List.map translateProcedure procedures))
  (*
  let rec translate_and_concat instruction_list procedure_list =
    match procedure_list with
    | procedure :: rest -> translate_and_concat
                             (instruction_list @ (translateProcedure procedure))
                             rest
(*                        instruction_list @
                          translate_and_concat (translateProcedure procedure) rest
*)
    | [] -> instruction_list
  in
  translate_and_concat [] procedures
*)
