(* file: compile.ml author: R. Muller date: 1-5-2009.  revised: April
 * 2015

  The Compile module implements a gut-simple compiler for the language
  miniC.  The mc compiler generates code for the MIPS processor (as
  implemented by the MARS Simulator). The compiler consists of several
  majors phases, each of which is implemented in a separate module.
 *)
open Ast
open Symbol

let fmt = Printf.sprintf

module type COMPILE =
  sig
    val compile : unit -> unit
  end;;

module Compile : COMPILE =
  struct

    open Bases
    open Static
    open Typ

(* The following switch can be set via the command-line to run the type-checker.
*)
  let typeChecking = ref true

  (* compilerOptions processes compiler options and returns the
   * position in Sys.argv where the source file ought to be. Remember
   * that Sys.argv.(0) is the string showing the program invocation.
   *)
  let compilerOptions() =
    match Array.length(Sys.argv) with
    | 2 -> 1
    |	3 ->
      (match Sys.argv.(1) with
       | "-nocheck" -> typeChecking := false; 2
       | "-t" -> Debug.debugLexer := true; 2
       | anythingelse ->
         failwith (fmt "Unknow compiler option %s.\n\n" Sys.argv.(1)))
    | _ -> failwith "Too many compiler options.\n\n"

  let parseFile fileName =
    let inch = open_in fileName in
    let lexbuf = Lexing.from_channel inch in
    let ast = (if !Debug.debugLexer then
                 let _ = Debug.dumpTokens Lexer.token lexbuf
                 in
                 Ast.Program([])
               else
                 Parser.program Lexer.token lexbuf)
    in
    close_in inch ;
    ast

  let compile() =
    let n = compilerOptions () in
    let filename = Sys.argv.(n) in
    let dbgOut = Debug.debugSetup filename in
    (* *)let _ = Printf.printf "filename : [%s]\n" filename in

    (* Parse the text in the input file.
     *)
    let ast = parseFile filename in
    let _ = Debug.debugInfo(dbgOut, "The input program is:", ast) in

    (* See if the user wants this program typed-checked.
    *)

    let typeEnv = Bases.Compiler.staticBasis in
    (* moved it out to use it for naming as well *)
    let _ = (if !typeChecking then

              (* Type-check the parse tree.
              *)
               let msg = (try
                            let _ = Static.typeCheck typeEnv ast
                            in
                            "\nThe program is well-typed.\n"
                          with Static.TypeError s ->
                            let _ = print_string s in
                            let _ = Util.writeln(dbgOut,0,s)
                            in
                            failwith "Compilation failed.\n")
               in
               (if !Debug.debug then Util.writeln(dbgOut, 0, msg) else ())
             else
               (* No type checking, pretend the program was well-typed. *)
               ()) in


    (* Checks presence of main*)
    let Program ps = ast in
    let _ =
      match List.exists (fun (Ast.Procedure Ast.{id; formals; _}) -> Symbol.format id = "main" && formals = []) ps with
    | true -> ()
    | false -> failwith "main() not found"
    in

    (* Perform the naming source-to-source transformation.
    *)
    let named = Name.translate typeEnv ast in
    let _ = Debug.debugInfo(dbgOut, "After the naming phase:", named) in

    (* Remove nested let-defintions, another source-to-source translation.
     *)
    let lifted = Lift.translate named in
    let _ = Debug.debugInfo(dbgOut, "After the lifting phase:", lifted) in

    (* Remove propagated copies.
     *)
    let copy = Copyprop.translate lifted in
    let _ = Debug.debugInfo(dbgOut, "After the copyprop phase:", copy) in

    (* Insert control forms; a translation to the language of quadruples.
     *)
    let quads = Control.translate copy in
    let _ = Util.writeln(dbgOut, 0, "\nAfter the control phase:") in
    let _ = Quads.dumpInstructionStream quads in

    (* Remove propagated copies. from quads
    *)(*
    let copyquads = Copyprop_quads.rmNoop (Copyprop_quads.translate quads) in
    let _ = Util.writeln(dbgOut, 0, "\nAfter the copyprop phase:") in
    let _ = Quads.dumpInstructionStream copyquads in
*)
    (* Produce a code stream --- a sequence of MIPS instructions.
    *)
    let codestream = Codegen.translate quads in
    let _ = (if !Debug.debug then
               let objfname = Util.makeFileName(filename, "asm") in
               let msg = fmt "\nEmitting MIPS assembley code to %s\n\n" objfname
               in
               (
                 Util.writeln(dbgOut, 0, msg);
                 close_out(dbgOut)
               )
             else ()) in

    (* Emit the assembley code stream to the output file.  This code can
     * be assembled and run using the MARS simulator.
     *)
    let _ = Mips.Codestream.emit(filename, codestream)
    in
    ()

  let go = compile

  let s = go ()

  end
      (*
module Q = Quads

let run () = (
  let quadsPgm1 = (
    let f = Label.fromString "f" in
    let n1 = Symbol.fromString "n1" in
    let n2 = Symbol.fromString "n2" in
    let plus = Symbol.fromString "+" in
    let x = Symbol.fresh() in
    let i1 = Q.Instruction
        { label = None;
          op = Q.Gets
              { dst = Q.Id x;
                src = Q.BinPrimOp
                    { op = plus;
                      opnds = { Q.src1 = Q.Id n1;
                                Q.src2 = Q.Id n2  }}}} in
    let i2 = Q.Instruction {label = None; op = Q.Ret(Q.Id x)}
    in
    [Q.Procedure {entry = f; formals = [n1; n2]; code = [i1; i2]}]
  ) in

  let codestream = Codegen.translate quadsPgm1 in

  let filename = "test/test.mc" in
  let _ = Mips.Codestream.emit(filename, codestream)
  in
  ()
)

let t = run ()

*)
