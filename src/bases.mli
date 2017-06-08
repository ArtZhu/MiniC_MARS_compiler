(* file: bases.mli
 * author: Bob Muller
 * date: 3-2-2009
 *
 * This is the interface file for the bases used in the PEL compiler.
 *)
open Environment

type primop = Symbol.t;;

val primOps : primop list;;

val isPrim : Symbol.t -> bool;;


(*
 * The compiler uses the staticBasis for type checking and the dynamicBasis
 * to hold code generators for the primitive operators.
 *)
module Compiler :
sig
  val staticBasis : Typ.t Environment.t;;

  type codegenerator = Mips.Operand.t list -> Mips.Codestream.t;;
  type cg_value = CodeGenerator of codegenerator | Offset of int;;
  val dynamicBasis : cg_value Environment.t;;
end;;

(* The interpreter doesn't include a type checker. Its dynamicBasis provides
 * interpretations of the primitive operators.
 *)
module Interpreter :
sig
  val dynamicBasis : Ast.value Environment.t

  val applyBinary : ('a * 'a -> 'a) * 'a list -> 'a
  val applyUnary  : ('a -> 'a) * 'a list -> 'a
end;;
