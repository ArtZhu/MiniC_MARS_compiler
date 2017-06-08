(*
 * file: bases.ml.
 * author: R. Muller
 * date: 4-4-2002, converted from SML to Ocaml on 1-8-2009.
 *
 * This file contains the code for building both the static and dynamic basis.
 * The function makeBasis will construct a static basis when applied to the
 * list Bases.primOpTypes.  The same function will construct a dynamic
 * basis when applied to the list implementationsOfPrimitives.   These bases
 * are constructed in the preamble to the top-level read-eval-print loop in
 * Lx.sml.  The apply functions can used to actually put a type checker for (or
 * implementation of) a primitive to use.
 *
 * To extend the basis with new primitives, the list primNames must be
 * extended with an appropriate identifier.
 *)

open Environment

(*
 * This is the master list of names of primitive operators.
 *
 * NB: THESE NAMES ARE LAYED OUT IN A FIXED ORDER!
 *)
let primOpNames = ["+"; "-"; "*"; "/"; "%"; "**"; "<"; "<="; "=="; "<>"; ">="; ">"; "not"];;

let primOps = List.map Symbol.fromString primOpNames;;

type primop = Symbol.t;;

let isPrim id = List.mem id primOps;;

let makeBasis values =
  let keyValuePairs = Util.zip(primOps, values) in
  let insert map (key, value) = Environment.add key value map
  in
    List.fold_left insert Environment.empty keyValuePairs;;

module Compiler =
  struct
    (*
     * The Bases.Compiler module defines the types and code generators
     * for the primitive operations built-in to the language. The order
     * of the types and the code generators must agree with the ordering
     * of the primitive operations in the Op module.
     *)
    let intCrossInt2Int =
      Typ.Arrow {from = Typ.Product [Typ.Int; Typ.Int]; too = Typ.Int}

    let intCrossInt2Bool =
      Typ.Arrow {from = Typ.Product [Typ.Int; Typ.Int]; too = Typ.Bool}

    let int2Int = Typ.Arrow {from = Typ.Int; too = Typ.Int}

    let bool2Bool = Typ.Arrow {from = Typ.Bool; too =Typ.Bool}

    let operatorTypes =
      [
	      intCrossInt2Int;  (* + *)
	      intCrossInt2Int;  (* - *)
	      intCrossInt2Int;  (* * *)
	      intCrossInt2Int;  (* / *)
	      intCrossInt2Int;  (* % *)
	      intCrossInt2Int;  (* ** *)
	      intCrossInt2Bool; (* < *)
	      intCrossInt2Bool; (* <= *)
	      intCrossInt2Bool; (* == *)
	      intCrossInt2Bool; (* <> *)
	      intCrossInt2Bool; (* >= *)
	      intCrossInt2Bool; (* > *)
	      bool2Bool         (* not *)
      ];;

    let staticBasis = makeBasis operatorTypes;;

    (* Code Generators for the Primitve Operations *)

    module Opn = Mips.Operation;;
    module Opnd = Mips.Operand;;
    module Instr = Mips.Instruction;;
    module CS = Mips.Codestream;;

    let toInstr = Instr.toInstruction;;
    let fIL = CS.fromInstructionList;;

    type codegenerator = Opnd.t list -> Mips.Codestream.t

    (* The code generator maintains an environment for looking up information
     * about identifiers. When the identifier is a primitive operator, the
     * code generator would like to find a codegenerator for that operator.
     * When the identifier is a variable (or temporary), the code generator
     * would like to find the storage offset for that variable.
     *
     * NB: The cg_value type is exported so that the code generator can use
     * the CodeGenerator and Offset constructors.
     *)
    type cg_value = CodeGenerator of codegenerator | Offset of int;;

    let operatorCodeGenerators = [
      (* +
       *)
      (function
        | [rd; rs; rt] -> fIL [toInstr(None, Opn.Add {rd; rs; rt}, None)]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* -
       *)
      (function
        | [rd; rs; rt] -> fIL [toInstr(None, Opn.Sub {rd; rs; rt}, None)]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* *
       *)
      (function
        | [rd; rs; rt] -> fIL [toInstr(None, Opn.Mul {rd; rs; rt}, None)]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* /
       *)
      (function
        | [rd; rs; rt] -> fIL [toInstr(None, Opn.Div {rs; rt}, None);
                               toInstr(None, Opn.Mflo rd, None)]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* %
       *)
      (function
        | [rd; rs; rt] -> fIL [toInstr(None, Opn.Div {rs; rt}, None);
                               toInstr(None, Opn.Mfhi rd, None)]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (*
       * **  NOT IMPLEMENTED
       *)
      (function
        | [] -> fIL [toInstr(None, Opn.Nop, Some "**: NOT IMPLEMENTED")]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* <
       *)
      (function
        | [rd; rs; rt] -> fIL [toInstr(None, Opn.Slt {rd; rs; rt}, None)]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* <=
       *)
      (function
        | [rd; rs; rt] ->
          fIL [toInstr(None, Opn.Sub  {rd = rd; rs = rs; rt = rt}, Some "<=");
               toInstr(None, Opn.Slti {rd = rd; rs = rd; const16 = Opnd.Const16 1}, None)]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* ==
      *)
      (* I don't think this works *)

      (function
        | [rd; rs; rt] ->
          fIL [toInstr(None, Opn.Li   {rd; imm32 = Opnd.Const16 0}, None);
               toInstr(None, Opn.Sub  {rd = rs; rs; rt}, Some "==");
               toInstr(None, Opn.Li   {rd = rt; imm32 = Opnd.Const16 1}, None);
               toInstr(None, Opn.Movz {rd = rd; rs = rt; rt = rs}, None)]
      	| other -> failwith "Bases: something is wrong with the opr codegens.");
(*
      (function
        | [rd; rs; rt] ->
          fIL [toInstr(None, Opn.Sub  {rd = rd; rs = rs; rt = rt}, Some "==")]
      	| other -> failwith "Bases: something is wrong with the opr codegens.");
*)
      (* <>
       *)
      (function
        | [rd; rs; rt] ->
          fIL [toInstr(None, Opn.Li   {rd; imm32 = Opnd.Const16 0}, None);
               toInstr(None, Opn.Sub  {rd = rs; rs; rt}, Some "<>");
               toInstr(None, Opn.Li   {rd = rt; imm32 = Opnd.Const16 1}, None);
               toInstr(None, Opn.Movn {rd = rd; rs = rt; rt = rs}, None)]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* >=
       *)
      (function
        | [rd; rs; rt] ->
          fIL [toInstr(None, Opn.Sub  {rd = rd; rs = rt; rt = rs}, Some ">=");
               toInstr(None, Opn.Slti {rd = rd; rs = rd; const16 = Opnd.Const16 1}, None)]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* >
       *)
      (function
        | [rd; rs; rt] -> fIL [toInstr(None, Opn.Slt {rd = rd; rs = rt; rt = rs}, Some ">")]
        | other -> failwith "Bases: something is wrong with the opr codegens.");

      (* not
      *)
      (* not right *)
      (*
      (function
        | [rd; rs] ->fIL [toInstr(None, Opn.Not {rd; rs}, Some "not")]
        | other -> failwith "Bases: something is wrong with the opr codegens.")
       *)
      (* follows the true = 1, false = 0 notion *)
       (function
         | [rd; rs] ->fIL [toInstr(None, Opn.Slti {rd; rs; const16 = Opnd.Const16 1}, Some "not")]
         | other -> failwith "Bases: something is wrong with the opr codegens.")
    ];;

let codeGenerators = List.map (fun cg -> CodeGenerator cg) operatorCodeGenerators;;

let dynamicBasis = makeBasis codeGenerators;;

 end;;

module Interpreter =
  struct
    let applyBinary = function
	(operation,[value1;value2]) -> operation(value1,value2)
      | _ -> raise (Failure "Cannot happen.");;

    let applyUnary = function
	(operation,[value]) -> operation(value)
      | _ -> raise (Failure "Cannot happen.");;

      (****************************************************************************
       *
       * The implementation of primitive operations. Note that the order of
       * these together with the unarys must match up with the order of the
       * operator names in op.ml.
       *)
    let binaryPrePrimOps =
      [
	(function
    (Ast.LiteralValue {bits = v1},  Ast.LiteralValue {bits = v2}) ->  (* + *)
      Ast.LiteralValue {typ = Typ.Int; bits = v1 + v2}
	  | other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->      (* - *)
     Ast.LiteralValue {typ = Typ.Int; bits = v1 - v2}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->      (* * *)
     Ast.LiteralValue {typ = Typ.Int; bits = v1 * v2}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->          (* / *)
     Ast.LiteralValue {typ = Typ.Int; bits = v1 / v2}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->          (* % *)
     Ast.LiteralValue {typ = Typ.Int; bits = v1 mod v2}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->          (* ** *)
	       let v1' = float_of_int v1 in
	       let v2' = float_of_int v2 in
        Ast.LiteralValue {typ = Typ.Int; bits = int_of_float(v1' ** v2')}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->           (* < *)
     Ast.LiteralValue {typ = Typ.Bool; bits = if v1 < v2 then 1 else 0}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->           (* <= *)
     Ast.LiteralValue {typ = Typ.Bool; bits = if v1 <= v2 then 1 else 0}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->           (* == *)
     Ast.LiteralValue {typ = Typ.Bool; bits = if v1 = v2 then 1 else 0}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->           (* <> *)
     Ast.LiteralValue {typ = Typ.Bool; bits = if v1 <> v2 then 1 else 0}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->           (* >= *)
     Ast.LiteralValue {typ = Typ.Bool; bits = if v1 >= v2 then 1 else 0}
	| other -> raise (Failure "basis: bad dynamic environment.\n"));

	(function
	     (Ast.LiteralValue{bits = v1}, Ast.LiteralValue{bits = v2}) ->           (* > *)
     Ast.LiteralValue {typ = Typ.Bool; bits = if v1 > v2 then 1 else 0}
	| other -> raise (Failure "basis: bad dynamic environment.\n"))
      ];;

      (*
       * Coerce the implementations of binary primitives to be Ast.letues.
       *)
      let binaryPrimOps = List.map (fun x -> Ast.BinaryOp x) binaryPrePrimOps;;

      (*
       *  The unary primtives.
       *)
      let unaryPrePrimOps =
	[
	  (function
       (Ast.LiteralValue {bits}) ->       (* not *)
       Ast.LiteralValue {typ = Typ.Bool; bits = if bits = 1 then 0 else 1}
	     | other -> raise (Failure "basis: bad dynamic environment.\n"))
 ];;
      (* Could fix here to change true = non-zero and false = zero ? *)

      (*
       * Coerce the implementations of unary primitives to be Ast.values.
       *)
      let unaryPrimOps = List.map (fun x -> Ast.UnaryOp x) unaryPrePrimOps;;

      (*
       * Make the dynamic basis for export to the interpreter.
       *)
      let dynamicBasis = makeBasis (binaryPrimOps @ unaryPrimOps);;
  end;;
